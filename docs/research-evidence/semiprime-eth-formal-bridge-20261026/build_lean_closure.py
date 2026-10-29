#!/usr/bin/env python3
"""Strict isolated build of the pinned external SAT theorem's source closure."""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import hashlib
import json
import os
import subprocess
import time

WORK = Path('/tmp/semiprime-d1-audit-20261026')
SOURCE = WORK / 'openai-math/lean'
BUILD = WORK / 'lean-build'
LOGS = WORK / 'lean-logs'
LEAN = '/home/dbsanfte/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
CLOSURE = json.loads((WORK / 'lean-closure.json').read_text())
DEPS = CLOSURE['modules']
TARGET = CLOSURE['target']
JOBS = 6
sha = lambda data: hashlib.sha256(data).hexdigest()


def write_state(state):
    temp = WORK / 'lean-build-state.json.tmp'
    temp.write_text(json.dumps(state, indent=2) + '\n')
    temp.replace(WORK / 'lean-build-state.json')


def main():
    BUILD.mkdir(exist_ok=True)
    LOGS.mkdir(exist_ok=True)
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=SOURCE, text=True).strip() == CLOSURE['head']
    assert not CLOSURE['missing']
    cache_paths = [p for p in os.environ['LEAN_PATH'].split(':')
                   if '/.lake/packages/' in p or '/.elan/toolchains/' in p]
    env = dict(os.environ, LEAN_PATH=':'.join([str(BUILD)] + cache_paths))
    state_path = WORK / 'lean-build-state.json'
    state = json.loads(state_path.read_text()) if state_path.exists() else dict(
        status='running', target=TARGET, commit=CLOSURE['head'],
        compiler=LEAN, options=['-DautoImplicit=false', '-DwarningAsError=true', '-j1'],
        source_root=str(SOURCE), output_root=str(BUILD), jobs=JOBS,
        completed={}, failed={}, started_at=time.time())
    assert state['commit'] == CLOSURE['head']
    for name, record in state['completed'].items():
        source = SOURCE / (name.replace('.', '/') + '.lean')
        output = BUILD / (name.replace('.', '/') + '.olean')
        assert sha(source.read_bytes()) == record['source_sha256'], name
        assert sha(output.read_bytes()) == record['olean_sha256'], name
    done = set(state['completed'])
    pending = set(DEPS) - done
    # A prior failure is not silently retried with changed source or options.
    if state['failed']:
        print(json.dumps(dict(status='previous-failure', failed=state['failed'])), flush=True)
        return 1
    state['status'] = 'running'
    write_state(state)

    def compile_one(name):
        relative = Path(name.replace('.', '/'))
        source = SOURCE / relative.with_suffix('.lean')
        output = BUILD / relative.with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        log = LOGS / (name + '.log')
        command = [LEAN, '-DautoImplicit=false', '-DwarningAsError=true', '-j1',
                   '-R', str(SOURCE), '-o', str(output), str(source)]
        before = time.monotonic()
        with log.open('w') as handle:
            result = subprocess.run(command, cwd=SOURCE, env=env, stdout=handle, stderr=subprocess.STDOUT)
        record = dict(source_sha256=sha(source.read_bytes()), log=str(log),
                      seconds=round(time.monotonic() - before, 3), exit_code=result.returncode)
        if result.returncode == 0:
            record['olean_sha256'] = sha(output.read_bytes())
        return name, record

    last = time.monotonic()
    running = {}
    with ThreadPoolExecutor(max_workers=JOBS) as pool:
        while pending or running:
            if not state['failed']:
                ready = sorted(m for m in pending if all(d in done for d in DEPS[m] if d in DEPS))
                for name in ready[:JOBS-len(running)]:
                    pending.remove(name)
                    running[pool.submit(compile_one, name)] = name
            if not running:
                if state['failed']:
                    break
                raise RuntimeError('Unresolved dependency cycle: ' + ', '.join(sorted(pending)[:20]))
            finished, _ = wait(running, timeout=10, return_when=FIRST_COMPLETED)
            for future in finished:
                name, record = future.result()
                running.pop(future)
                if record['exit_code'] == 0:
                    done.add(name)
                    state['completed'][name] = record
                else:
                    state['failed'][name] = record
                    print(json.dumps(dict(failed=name, **record)), flush=True)
            if finished:
                state['active_modules'] = list(running.values())
                state['pending_modules'] = len(pending)
                write_state(state)
            if time.monotonic() - last >= 25:
                print(json.dumps(dict(completed=len(done), total=len(DEPS), running=list(running.values()),
                                      failed=len(state['failed']))), flush=True)
                last = time.monotonic()
    state['status'] = 'failed' if state['failed'] else 'complete'
    state['finished_at'] = time.time()
    write_state(state)
    print(json.dumps(dict(status=state['status'], completed=len(done), total=len(DEPS),
                          target=TARGET, seconds=round(state['finished_at'] - state['started_at'], 2))), flush=True)
    if state['status'] == 'complete':
        print((LOGS / (TARGET + '.log')).read_text(), flush=True)
    return bool(state['failed'])


if __name__ == '__main__':
    raise SystemExit(main())

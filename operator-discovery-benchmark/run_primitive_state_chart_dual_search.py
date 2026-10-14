"""Freeze and run one direct chart dual search, without hashing."""
import argparse
import ast
from pathlib import Path
import resource
import subprocess
import sys
import time
from detector_parallel import run_jobs
import primitive_state_chart_dual_protocol as C


def sources():
    pending = ['run_primitive_state_chart_dual_search',
               'primitive_state_chart_dual_search',
               'check_primitive_state_chart_dual_search_run',
               'publish_cancellation_primitive_state_chart_dual_search', *C.TESTS]
    seen = set()
    while pending:
        name = pending.pop()
        path = C.ROOT / (name+'.py')
        if name in seen or not path.is_file():
            continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.Import):
                pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                pending.append(node.module.split('.')[0])
    return sorted(name+'.py' for name in seen)+[C.SCOPE, C.NOTE]


def validate(directory):
    d = Path(directory)
    C.require(C.read(d/'protocol.json') == C.protocol(), 'fixed chart dual protocol')
    C.require(C.read(d/'parent.json') == C.parent(), 'fixed mathematical premises')


def load_parent():
    report = C.read(C.ROOT/C.REPORT, C.CAPS[C.REPORT])
    review = C.read(C.ROOT/C.REVIEW, C.CAPS[C.REVIEW])
    C.license_parent(report, review)
    return report, review


def freeze(directory):
    C.runtime()
    d = Path(directory).resolve()
    if d.exists():
        raise FileExistsError('fresh chart dual destination required')
    load_parent()
    names = sources()
    if sum((C.ROOT/name).stat().st_size for name in names) > 8388608:
        raise OverflowError('bounded source snapshot')
    for name, cap in C.CAPS.items():
        if (C.ROOT/name).stat().st_size > cap:
            raise OverflowError('bounded designated input')
    d.mkdir()
    (d/'source_snapshot').mkdir()
    for name in names:
        (d/'source_snapshot'/name).write_bytes((C.ROOT/name).read_bytes())
    C.write(d/'protocol.json', C.protocol())
    C.write(d/'parent.json', C.parent())
    C.write(d/'source_snapshot.json', names)


def worker(job):
    import primitive_state_chart_dual_search as P
    C.runtime()
    d = Path(job['directory'])
    C.require(job.get('index') == 0 and job.get('phase') == 'search',
              'single declared worker')
    start, cpu = time.monotonic(), time.process_time()
    deadline = start+3600
    record = dict(status='UNKNOWN', producer_complete=False, artifact=None,
                  ledger=C.ledger(), stage_counts={}, **C.FLAGS)
    try:
        validate(d)
        load_parent()
        chart = C.read(C.ROOT/C.CHART, C.CAPS[C.CHART])
        endpoint = C.read(C.ROOT/C.ENDPOINT, C.CAPS[C.ENDPOINT])
        def checkpoint(value):
            C.write(d/'jobs/progress.json', value)
        outcome = P.search(chart, endpoint, deadline=deadline, checkpoint=checkpoint)
        C.write(d/'jobs/proposal.json', outcome, 8388608)
        record.update(status=outcome['status'], producer_complete=True,
                      artifact='proposal.json', stage_counts=outcome.get('stage_counts', {}),
                      reason=outcome.get('reason'))
    except Exception as error:
        record.update(status='UNKNOWN', producer_complete=False,
                      reason=str(error) or type(error).__name__, error_type=type(error).__name__)
    record['cost'] = dict(elapsed_seconds=time.monotonic()-start,
                          cpu_seconds=time.process_time()-cpu,
                          peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                          observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),
                          pid=__import__('os').getpid())
    record['deadline_exceeded'] = time.monotonic() > deadline
    if record['deadline_exceeded']:
        record.update(status='UNKNOWN', producer_complete=False,
                      reason='cooperative worker deadline exceeded')
    C.write(d/'jobs/search-job.json', record)
    return dict(file='jobs/search-job.json', status=record['status'],
                cost=record['cost'], **C.FLAGS)


def run(directory):
    C.runtime()
    d = Path(directory).resolve()
    validate(d)
    with (d/'run_started.json').open('x') as handle:
        handle.write('{"one_fixed_search":true}\n')
    tests = subprocess.run([sys.executable, '-B', '-m', 'unittest', *C.TESTS],
                           cwd=C.ROOT, capture_output=True, text=True, timeout=300)
    C.write(d/'tests.json', dict(returncode=tests.returncode, stdout=tests.stdout,
                                stderr=tests.stderr), 1048576)
    C.require(tests.returncode == 0, 'frozen chart dual tests passed')
    result = run_jobs([dict(directory=str(d), phase='search', index=0)],
                      worker='run_primitive_state_chart_dual_search:worker', **C.PARALLEL)
    C.write(d/'execution.json', result, 1048576)
    C.write(d/'receipt.json', dict(one_fixed_search=True, files=[
        'protocol.json', 'parent.json', 'tests.json', 'execution.json',
        'jobs/search-job.json', 'jobs/proposal.json'], **C.FLAGS))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['freeze', 'run'])
    parser.add_argument('directory')
    args = parser.parse_args()
    (freeze if args.command == 'freeze' else run)(args.directory)

"""Frozen full-atom completion diagnostic of an already admitted separator."""
import argparse
import ast
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
import run_detector as R
from detector_parallel import run_jobs
from detector_workflow_guard import require_verified_runtime
import cancellation_complete_gram_program as P
import check_complete_gram_moment_probe as M

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'cancellation-arithmetic-results'
PARENT = BASE / 'joint-gram-compressed-replay-001'
FLAGS = dict(global_bound_proved=False, RH_proved=False)
PARALLEL = dict(workers=1, worker_memory_bytes=6*1024**3, memory_budget_bytes=6*1024**3,
                timeout_seconds=600, max_jobs=1, max_result_bytes=65536)
TESTS = ['test_check_cancellation_complete_gram_program', 'test_check_complete_gram_moment_probe',
         'test_run_complete_gram_moment_probe', 'test_check_complete_gram_probe_run']
INPUTS = ['cancellation-arithmetic-results/publication-006/manifest.json',
          'cancellation-arithmetic-results/publication-006/report.json',
          'cancellation-arithmetic-results/joint-gram-compressed-replay-001/result.json',
          'cancellation-arithmetic-results/joint-gram-compressed-replay-001/receipt.json',
          'cancellation-arithmetic-results/joint-gram-compressed-replay-001/independent_verification.json',
          'cancellation-arithmetic-results/joint-shared-gram-probe-001/protocol.json']


def sources():
    pending = ['run_complete_gram_moment_probe', 'check_complete_gram_probe_run', *TESTS]
    seen = set()
    while pending:
        name = pending.pop(); path = ROOT / (name + '.py')
        if name in seen or not path.is_file():
            continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.Import):
                pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                pending.append(node.module.split('.')[0])
    return sorted(name + '.py' for name in seen)


def parent_bindings():
    for name, h in R.read(BASE / 'publication-006/manifest.json')['files'].items():
        if R.sha(ROOT / name) != h:
            raise ValueError('published evidence changed: ' + name)
    review = R.read(PARENT / 'independent_verification.json')
    if review.get('all_passed') is not True:
        raise ValueError('admitted original separator required')
    for name, h in review['input_sha256'].items():
        if R.sha(PARENT / name) != h:
            raise ValueError('original admission binding: ' + name)
    result = R.read(PARENT / 'result.json')
    if result['status'] != 'exact_separator' or result['synthesis']['certified'] is not True:
        raise ValueError('exact original separator required')
    return result


def freeze(directory):
    require_verified_runtime(); original = parent_bindings()
    for name in ['check_complete_gram_probe_run', *TESTS]:
        if not (ROOT / (name + '.py')).is_file():
            raise FileNotFoundError(name)
    d = Path(directory).resolve(); d.mkdir(parents=True, exist_ok=False)
    (d / 'frozen_source').mkdir()
    hashes = {}
    for name in sources():
        (d / 'frozen_source' / name).write_bytes((ROOT / name).read_bytes())
        hashes[name] = R.sha(ROOT / name)
    protocol = dict(schema=1, program=original['program'], scales=original['scales'],
                    language=P.SPEC, gram_specs=P.gram_specs(), gram_groups=P.group_descriptors(),
                    tests=TESTS, parallel=PARALLEL, no_new_float_search=True,
                    conditioning='complete prior atom union fixed before inspecting its cross moments',
                    missing_policy='unknown; no implicit zero moments',
                    numerical_response_inputs=False, larger_cone_feasibility_proved=False,
                    resource_scope='external 6 GiB and 600 seconds; source builder and PSD checker retain their existing local caps; full moment expansion has no global internal operation cap',
                    **FLAGS)
    R.write(d / 'protocol.json', protocol); R.write(d / 'source_seal.json', hashes)
    R.write(d / 'input.json', dict(input_sha256={name: R.sha(ROOT / name) for name in INPUTS}))
    R.write(d / 'seal.json', dict(protocol_sha256=R.sha(d / 'protocol.json'),
                                 source_seal_sha256=R.sha(d / 'source_seal.json'),
                                 input_sha256=R.sha(d / 'input.json')))
    return d


def validate(directory):
    d = Path(directory); seal = R.read(d / 'seal.json')
    for name in ['protocol', 'source_seal', 'input']:
        if seal[name + '_sha256'] != R.sha(d / (name + '.json')):
            raise ValueError('probe seal changed: ' + name)
    source = R.read(d / 'source_seal.json')
    if set(source) != set(sources()):
        raise ValueError('complete executed source closure')
    for name, h in source.items():
        if R.sha(ROOT / name) != h or R.sha(d / 'frozen_source' / name) != h:
            raise ValueError('frozen probe source changed: ' + name)
    inputs = R.read(d / 'input.json')['input_sha256']
    if set(inputs) != set(INPUTS):
        raise ValueError('complete prior evidence bindings')
    for name, h in inputs.items():
        if R.sha(ROOT / name) != h:
            raise ValueError('original input changed: ' + name)
    parent_bindings()


def worker(job):
    require_verified_runtime(); d = Path(job['directory']); validate(d)
    if (d / 'result.json').exists() or (d / 'receipt.json').exists():
        raise FileExistsError('exclusive probe result')
    protocol = R.read(d / 'protocol.json'); start = time.monotonic(); cpu = time.process_time()
    out = dict(no_new_float_search=True, **FLAGS)
    try:
        original = parent_bindings()
        if protocol['program'] != original['program'] or protocol['scales'] != original['scales']:
            raise ValueError('same original program and scales')
        probe = M.audit_existing_separator(protocol['program'], protocol['scales'], original['synthesis'])
        out.update(status='complete', probe=probe)
    except (OverflowError, MemoryError, TimeoutError, ImportError) as error:
        out.update(status='missing_resource', reason=str(error) or type(error).__name__)
    except (ValueError, TypeError, KeyError, RuntimeError) as error:
        out.update(status='rejected', reason=str(error) or type(error).__name__)
    out['cost'] = dict(elapsed_seconds=time.monotonic()-start, cpu_seconds=time.process_time()-cpu,
                       peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                       observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())), pid=os.getpid())
    validate(d); R.write(d / 'result.json', out)
    return dict(file='result.json', sha256=R.sha(d / 'result.json'), status=out['status'], cost=out['cost'], **FLAGS)


def run(directory):
    require_verified_runtime(); d = Path(directory).resolve(); validate(d)
    if (d / 'tests.json').exists():
        raise FileExistsError('probe already started')
    test = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS], cwd=ROOT,
                          capture_output=True, text=True, timeout=180)
    R.write(d / 'tests.json', dict(returncode=test.returncode, stdout=test.stdout, stderr=test.stderr))
    if test.returncode:
        raise ValueError('pre-score calibration failed')
    execution = run_jobs([dict(directory=str(d))], worker='run_complete_gram_moment_probe:worker', **PARALLEL)
    R.write(d / 'execution.json', execution); validate(d)
    R.write(d / 'receipt.json', dict(files_sha256={str(p.relative_to(d)): R.sha(p) for p in sorted(d.rglob('*.json'))},
                                   source_count=len(R.read(d / 'source_seal.json')), **FLAGS))
    print(execution)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['freeze', 'run']); parser.add_argument('directory')
    args = parser.parse_args(); (freeze if args.command == 'freeze' else run)(args.directory)

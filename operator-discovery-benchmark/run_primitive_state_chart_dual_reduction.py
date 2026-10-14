"""One frozen exact LP reduction, numerical proposal and exact restoration."""
import argparse
import ast
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
from detector_parallel import run_jobs
import primitive_state_chart_dual_reduction_protocol as C

NOTES = ['primitive_state_chart_dual_reduction_contract.txt',
         'primitive_state_chart_dual_reduction_resource_scope.txt',
         'primitive_state_chart_dual_reduction_soundness_v1.txt']


def sources():
    pending = ['run_primitive_state_chart_dual_reduction',
               'primitive_state_chart_dual_reduction',
               'check_primitive_state_chart_dual_reduction_run',
               'publish_cancellation_primitive_state_chart_dual_reduction', *C.TESTS]
    seen = set()
    while pending:
        name = pending.pop()
        path = C.ROOT/(name+'.py')
        if name in seen or not path.is_file():
            continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.Import):
                pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                pending.append(node.module.split('.')[0])
    return sorted(name+'.py' for name in seen)+NOTES


def validate(directory):
    d = Path(directory)
    C.require(C.read(d/'protocol.json') == C.protocol(), 'fixed reduction protocol')
    C.require(C.read(d/'parent.json') == C.parent(), 'fixed reduction premises')


def load_parent():
    values = [C.read(C.ROOT/name, C.CAPS[name]) for name in (
        C.CHART_REPORT, C.CHART_REVIEW, C.REPORT, C.REVIEW)]
    C.license_parent(*values)
    return values


def freeze(directory):
    C.runtime()
    d = Path(directory).resolve()
    if d.exists():
        raise FileExistsError('fresh reduction research destination required')
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
    import primitive_state_chart_dual_reduction as P
    C.runtime()
    d = Path(job['directory'])
    C.require(job.get('index') == 0 and job.get('phase') == 'search', 'single declared worker')
    start, cpu = time.monotonic(), time.process_time()
    deadline = start+3600
    record = dict(status='UNKNOWN', producer_complete=False, reduction_saved=False,
                  ledger=C.ledger(), stage_counts={}, **C.FLAGS)
    try:
        validate(d)
        load_parent()
        chart = C.read(C.ROOT/C.CHART, C.CAPS[C.CHART])
        rays = C.read(C.ROOT/C.RAYS, C.CAPS[C.RAYS])['rays']
        geometry = C.read(C.ROOT/C.GEOMETRY, C.CAPS[C.GEOMETRY])
        def checkpoint(value):
            C.write(d/'jobs/progress.json', value)
        def save_reduction(value):
            C.write(d/'jobs/reduction.json', value, 67108864)
            record['reduction_saved'] = True
        outcome = P.search(chart, rays, geometry, deadline=deadline,
                           checkpoint=checkpoint, save_reduction=save_reduction)
        C.write(d/'jobs/proposal.json', outcome, 8388608)
        record.update(status=outcome['status'], producer_complete=True,
                      stage_counts=outcome.get('stage_counts', {}), reason=outcome.get('reason'),
                      route=outcome.get('route'))
    except Exception as error:
        record.update(status='UNKNOWN', producer_complete=False,
                      reason=str(error) or type(error).__name__, error_type=type(error).__name__)
    record['cost'] = dict(elapsed_seconds=time.monotonic()-start,
                          cpu_seconds=time.process_time()-cpu,
                          peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                          observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),
                          pid=os.getpid())
    record['deadline_exceeded'] = time.monotonic() > deadline
    if record['deadline_exceeded']:
        record.update(status='UNKNOWN', producer_complete=False, reason='worker deadline exceeded')
    C.write(d/'jobs/search-job.json', record)
    return dict(file='jobs/search-job.json', status=record['status'], cost=record['cost'], **C.FLAGS)


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
    C.require(tests.returncode == 0, 'frozen reduction tests passed')
    synthetic = C.synthetic_receipt(tests.stdout)
    C.write(d/'tests.json', dict(returncode=tests.returncode, stdout=tests.stdout,
                                stderr=tests.stderr, synthetic_work=synthetic), 1048576)
    result = run_jobs([dict(directory=str(d), phase='search', index=0)],
                      worker='run_primitive_state_chart_dual_reduction:worker', **C.PARALLEL)
    C.write(d/'execution.json', result, 1048576)
    C.write(d/'receipt.json', dict(one_fixed_search=True, files=[
        'protocol.json', 'parent.json', 'tests.json', 'execution.json',
        'jobs/search-job.json', 'jobs/reduction.json', 'jobs/proposal.json'], **C.FLAGS))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['freeze', 'run'])
    parser.add_argument('directory')
    args = parser.parse_args()
    (freeze if args.command == 'freeze' else run)(args.directory)

"""One exact post-search witness audit within the joint research budget."""
import argparse
import contextvars
import json
import math
import os
from pathlib import Path
import re
import resource
import time
import primitive_state_chart_dual_protocol as C
import check_primitive_state_chart_dual_search as CORE

SCHEMA = 'primitive-state-chart-dual-independent-review-v1'
_IO = contextvars.ContextVar('chart_dual_io', default=None)


def read(path, cap=65536):
    with Path(path).open('rb') as handle:
        data = handle.read(cap+1)
    if len(data) > cap:
        raise OverflowError('independent input byte cap')
    state = _IO.get()
    if state is not None:
        state[0] += 2*(len(data)//64+1)
        state[1] += len(data)
        if state[0] > 10000000:
            raise OverflowError('independent IO reserve within preparation')
        if time.monotonic() > state[2]:
            raise TimeoutError('independent input deadline')
    return json.loads(data)


def no_global_claim(value):
    C.require(isinstance(value, dict), 'explicit scoped object')
    for key in C.FLAGS:
        C.require(value.get(key) is False, 'explicit false scope flag '+key)


def verify_transport(execution):
    rows = execution.get('results')
    C.require(type(rows) is list and len(rows) == 1
              and rows[0].get('index') == 0
              and rows[0].get('status') in ('available', 'missing_resource', 'error'),
              'single declared worker result')
    cost = execution.get('cost', {})
    for key, value in dict(requested_workers=1, workers=1, max_in_flight=1,
                           numerical_threads_per_worker=1, worker_memory_bytes=6*1024**3,
                           memory_budget_bytes=6*1024**3, worker_memory_limit_enforced=True,
                           serial_fallback=False, start_method='spawn').items():
        C.require(type(cost.get(key)) is type(value) and cost[key] == value,
                  'actual worker resource boundary '+key)
    return rows[0]


def verify_job(job, execution, outcome):
    no_global_claim(job)
    C.require(job.get('ledger') == C.ledger(), 'one combined work allowance')
    C.require(job.get('status') in ('CERTIFICATE_PROPOSED', 'NONCERTIFIED', 'UNKNOWN'),
              'explicit producer outcome')
    C.require(type(job.get('producer_complete')) is bool
              and type(job.get('deadline_exceeded')) is bool, 'explicit completion flags')
    rows = [verify_transport(execution)]
    if rows[0]['status'] == 'available':
        C.require(rows[0].get('value') == dict(file='jobs/search-job.json',
                    status=job['status'], cost=job.get('cost'), **C.FLAGS),
                  'saved job is the transported result')
    else:
        C.require(job['status'] == 'UNKNOWN', 'failed transport cannot admit a witness')
    metrics = job.get('cost', {})
    for key in ('elapsed_seconds', 'cpu_seconds', 'peak_rss_kib'):
        value = metrics.get(key)
        C.require(type(value) in (int, float) and math.isfinite(value) and value >= 0,
                  'finite producer resource measurement')
    if job['producer_complete']:
        C.require(rows[0]['status'] == 'available' and job['deadline_exceeded'] is False
                  and metrics['elapsed_seconds'] <= 3600
                  and metrics['peak_rss_kib'] <= 6*1024**2
                  and metrics.get('observed_threads_at_completion') == 1,
                  'completed producer respects enforced limits')
        C.require(type(outcome) is dict and outcome.get('status') == job['status']
                  and job.get('artifact') == 'proposal.json', 'complete saved outcome')
        no_global_claim(outcome)
        counts = outcome.get('stage_counts')
        C.require(type(counts) is dict and job.get('stage_counts') == counts
                  and 'assembly' in counts and set(counts) <= {'assembly', 'native', 'restoration'},
                  'all retained stage counters bound to the saved outcome')
        C.require('restoration' not in counts or 'native' in counts,
                  'restoration requires a native proposal')
        for stage, values in counts.items():
            C.require(type(values) is dict, 'explicit stage counters')
            for key in ('operations', 'peak_live_cells', 'maximum_rational_bits'):
                C.require(type(values.get(key)) is int and values[key] >= 0,
                          'nonnegative exact stage counter '+key)
            C.require(values['operations'] <= C.ALLOCATIONS[stage],
                      'stage work stays within its combined-budget reservation')
            if job['status'] != 'UNKNOWN':
                C.require(values['peak_live_cells'] <= 6000000
                          and values['maximum_rational_bits'] <= 4096,
                          'completed stage respects rational limits')
        if 'native' in outcome:
            native = outcome['native']
            C.require(type(native) is dict and native.get('counts') == counts.get('native'),
                      'native counters match the complete stage record')
            iterations = native.get('iterations')
            iteration_ok = iterations is None or (type(iterations) is int and 0 <= iterations <= 100)
            C.require(iteration_ok or (job['status'] == 'UNKNOWN'
                      and native.get('success') is False and native.get('resource_failure')),
                      'invalid observed iteration count requires explicit nonadmission')
            C.require(native.get('options', {}).get('presolve') is False
                      and native['options'].get('maxiter') == 100
                      and native['options'].get('threads') == 1,
                      'one bounded native solver policy')
    else:
        C.require(job['status'] == 'UNKNOWN', 'incomplete producer remains unknown')
    return job['producer_complete']


def unknown(reason, *, resource_failure=None):
    return dict(schema=SCHEMA, status='UNKNOWN', all_passed=False,
                workflow_verified=False, certificate_verified=False,
                finite_augmented_cone_infeasibility_certified=False,
                independent_check=None, reason=reason, resource_failure=resource_failure,
                joint_work=C.ledger(), **C.FLAGS)


def _audit(directory, deadline):
    d = Path(directory)
    C.require(read(d/'protocol.json') == C.protocol(), 'fixed declared protocol')
    C.require(read(d/'parent.json') == C.parent(), 'fixed parent locations')
    report = read(C.ROOT/C.REPORT, C.CAPS[C.REPORT])
    parent_review = read(C.ROOT/C.REVIEW, C.CAPS[C.REVIEW])
    C.license_parent(report, parent_review)
    tests = read(d/'tests.json', 1048576)
    count = re.search(r'Ran (\d+) tests?', tests.get('stderr', ''))
    C.require(tests.get('returncode') == 0 and count
              and tests['stderr'].rstrip().endswith('OK'), 'reserved synthetic suite passed')
    C.require(read(d/'run_started.json') == dict(one_fixed_search=True), 'one producer attempt')
    execution = read(d/'execution.json', 1048576)
    terminal_path = d/'jobs/search-job.json'
    if not terminal_path.exists():
        transport = verify_transport(execution)
        C.require(transport['status'] != 'available', 'available worker requires its terminal record')
        result = unknown(transport.get('reason', 'worker returned no terminal record'),
                         resource_failure=dict(transport_status=transport['status']))
        result.update(workflow_verified=True, tests_passed=int(count.group(1)))
        return result
    job = read(terminal_path)
    proposal_path = d/'jobs/proposal.json'
    outcome = read(proposal_path, 8388608) if proposal_path.exists() else None
    complete = verify_job(job, execution, outcome)
    if not complete:
        result = unknown(job.get('reason', 'producer incomplete'))
        result.update(workflow_verified=True, job=job, tests_passed=int(count.group(1)))
        return result
    chart = read(C.ROOT/C.CHART, C.CAPS[C.CHART])
    check = CORE.verify_outcome(chart, parent_review, outcome, deadline=deadline,
                                max_operations=50000000, max_cells=6000000, max_bits=4096)
    no_global_claim(check)
    proved = check.get('finite_augmented_cone_infeasibility_certified') is True
    C.require(not proved or (check.get('verified') is True
              and check.get('complete') is True
              and check.get('status') == 'FINITE_CONE_INFEASIBLE'),
              'exact complete certificate required for separation')
    status = 'FINITE_CONE_INFEASIBLE' if proved else job['status']
    C.require(status in ('FINITE_CONE_INFEASIBLE', 'NONCERTIFIED', 'UNKNOWN'),
              'no unverified proposed witness promotion')
    result = dict(schema=SCHEMA, status=status, all_passed=status != 'UNKNOWN',
                  workflow_verified=True, certificate_verified=proved,
                  finite_augmented_cone_infeasibility_certified=proved,
                  independent_check=check, resource_failure=None,
                  joint_work=dict(C.ledger(), independent_operations=check.get('audit_operations')),
                  job=job, tests_passed=int(count.group(1)),
                  proof_scope='the publication028 augmented finite cone only',
                  numerical_solver_independently_replayed=False,
                  old_elimination_replayed=False, source_rebuilds=0, **C.FLAGS)
    if time.monotonic() > deadline:
        raise TimeoutError('independent mathematical audit deadline')
    return result


def audit(directory, *, write=False, time_limit=3600):
    C.runtime()
    C.require(type(time_limit) in (int, float) and math.isfinite(time_limit)
              and 0 < time_limit <= 3600, 'bounded independent deadline')
    d = Path(directory)
    target, marker = d/'independent_verification.json', d/'independent_started.json'
    if target.exists() or marker.exists():
        raise FileExistsError('sole independent allowance already started or consumed')
    with marker.open('x') as handle:
        handle.write('{"one_final_independent_audit":true,"max_operations":50000000}\n')
    start, cpu = time.monotonic(), time.process_time()
    deadline = start+time_limit
    token = _IO.set([0, 0, deadline])
    previous = resource.getrlimit(resource.RLIMIT_AS)
    cap = 6*1024**3
    C.require(previous[1] == resource.RLIM_INFINITY or previous[1] >= cap,
              'supported independent memory boundary')
    try:
        resource.setrlimit(resource.RLIMIT_AS, (cap, previous[1]))
        try:
            result = _audit(d, deadline)
        except (OverflowError, TimeoutError, MemoryError) as error:
            result = unknown(str(error) or type(error).__name__,
                             resource_failure=dict(type=type(error).__name__,
                                consumed_counts=getattr(error, 'independent_audit_counts', None)))
        cost = dict(elapsed_seconds=time.monotonic()-start,
                    cpu_seconds=time.process_time()-cpu,
                    peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                    observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),
                    audit_memory_limit_bytes=cap, audit_memory_limit_enforced=True,
                    pid=os.getpid())
        result['cost'] = cost
        result['joint_work'].update(independent_io_operations=_IO.get()[0],
                                    independent_input_bytes=_IO.get()[1])
        try:
            data = C.encoded(result)
            if len(data) > 8388608 or _IO.get()[0]+2*(len(data)//64+1) > 10000000:
                raise OverflowError('independent output reserve')
            if time.monotonic() > deadline:
                raise TimeoutError('independent output deadline')
            if write:
                with target.open('xb') as handle:
                    handle.write(data)
                if time.monotonic() > deadline:
                    raise TimeoutError('post-write independent deadline')
        except (OverflowError, TimeoutError, MemoryError) as error:
            result = unknown(str(error) or type(error).__name__,
                             resource_failure=dict(type=type(error).__name__))
            result['cost'] = cost
            if write:
                target.write_bytes(C.encoded(result))
        return result
    finally:
        resource.setrlimit(resource.RLIMIT_AS, previous)
        _IO.reset(token)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = audit(args.directory, write=args.write)
    print(json.dumps({key:result.get(key) for key in (
        'schema', 'status', 'all_passed', 'certificate_verified',
        'finite_augmented_cone_infeasibility_certified', 'resource_failure', 'cost')}))

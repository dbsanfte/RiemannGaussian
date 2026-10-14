"""Audit complete exact reduction and, if present, one separating certificate."""
import argparse
import contextvars
import json
import math
import os
from pathlib import Path
import re
import resource
import time
import primitive_state_chart_dual_reduction_protocol as C
import check_primitive_state_chart_dual_reduction as CORE
from check_primitive_state_chart_dual_search_run import verify_transport, no_global_claim

SCHEMA = 'primitive-state-chart-dual-reduction-independent-review-v1'
_IO = contextvars.ContextVar('chart_dual_reduction_io', default=None)


def read(path, cap=65536):
    with Path(path).open('rb') as handle:
        data = handle.read(cap+1)
    if len(data) > cap:
        raise OverflowError('independent bounded input')
    state = _IO.get()
    if state is not None:
        state[0] += 2*(len(data)//64+1)
        state[1] += len(data)
        if state[0] > 10000000:
            raise OverflowError('independent I/O reserve within preparation')
        if time.monotonic() > state[2]:
            raise TimeoutError('independent input deadline')
    return json.loads(data)


def native_reservation(m, n):
    C.require(type(m) is int and type(n) is int and 0 < m <= 443 and 0 < n <= 851,
              'compressed native dimensions')
    preparation = 16*m*n+64*(m+n)+1048576
    setup = preparation+m**3+2*m*n+1048576
    step = 2*m*n+m*m
    k = min(10000, max(0, (160000000-setup)//step))
    return dict(preparation_work_reserve=preparation, initial_factorization=m**3,
                per_iteration=step, max_iterations=k, input_and_transport=2*m*n+1048576,
                total=setup+k*step)


def verify_job(job, execution, outcome, reduction):
    transport = verify_transport(execution)
    no_global_claim(job)
    C.require(job.get('ledger') == C.ledger(), 'single combined reduction allocation')
    C.require(job.get('status') in ('CERTIFICATE_PROPOSED', 'NONCERTIFIED', 'UNKNOWN')
              and type(job.get('producer_complete')) is bool
              and type(job.get('reduction_saved')) is bool
              and type(job.get('deadline_exceeded')) is bool, 'explicit producer disposition')
    if transport['status'] == 'available':
        C.require(transport.get('value') == dict(file='jobs/search-job.json',
                  status=job['status'], cost=job.get('cost'), **C.FLAGS),
                  'saved terminal record matches transport')
    else:
        C.require(job['status'] == 'UNKNOWN', 'failed transport cannot propose admission')
    cost = job.get('cost', {})
    for key in ('elapsed_seconds', 'cpu_seconds', 'peak_rss_kib'):
        value = cost.get(key)
        C.require(type(value) in (int, float) and math.isfinite(value) and value >= 0,
                  'finite worker resource measurement')
    C.require(not job['reduction_saved'] or type(reduction) is dict,
              'saved reduction artifact available')
    if not job['producer_complete']:
        C.require(job['status'] == 'UNKNOWN', 'incomplete producer remains unknown')
        return False
    C.require(transport['status'] == 'available' and job['deadline_exceeded'] is False
              and cost['elapsed_seconds'] <= 3600 and cost['peak_rss_kib'] <= 6*1024**2
              and cost.get('observed_threads_at_completion') == 1,
              'completed worker respects enforced limits')
    C.require(type(outcome) is dict and outcome.get('status') == job['status'],
              'complete saved outcome')
    no_global_claim(outcome)
    counts = outcome.get('stage_counts')
    C.require(type(counts) is dict and counts == job.get('stage_counts')
              and 'reduction' in counts and set(counts) <= {'reduction', 'native', 'restoration'},
              'complete bound stage counters')
    for stage, values in counts.items():
        C.require(type(values) is dict, 'explicit stage counters')
        for key in ('operations', 'peak_live_cells', 'maximum_rational_bits'):
            C.require(type(values.get(key)) is int and values[key] >= 0, 'nonnegative stage counter')
        C.require(values['operations'] <= C.ALLOCATIONS[stage], 'stage operation allowance')
        if job['status'] != 'UNKNOWN':
            C.require(values['peak_live_cells'] <= 6000000
                      and values['maximum_rational_bits'] <= 4096, 'completed rational limits')
    route = outcome.get('route')
    C.require(route == job.get('route'), 'declared route bound to terminal record')
    if 'restoration' in counts:
        C.require('native' in counts and route == 'reduced_lp',
                  'single native support before restoration')
    native = outcome.get('native')
    if native is not None:
        C.require(type(native) is dict and native.get('counts') == counts.get('native'),
                  'native consumed counters')
        options = native.get('options', {})
        limit = options.get('maxiter')
        m = len(reduction.get('final_rows', [])) if reduction else 0
        n = len(reduction.get('active_columns', [])) if reduction else 0
        expected = native_reservation(m, n)
        unattempted_failure = (job['status'] == 'UNKNOWN' and native.get('attempted') is False
                              and bool(native.get('resource_failure')))
        C.require(options.get('presolve') is False and options.get('threads') == 1
                  and ((type(limit) is int and 1 <= limit <= 10000)
                       or (limit in (None, 0) and unattempted_failure)),
                  'bounded one-call native policy')
        C.require((limit is None and unattempted_failure) or limit == expected['max_iterations'],
                  'native iteration cap chosen solely from compressed dimensions')
        if native.get('attempted') is True:
            C.require(native.get('reservation') == expected and expected['total'] <= 160000000,
                      'complete dimension-only native reservation')
        iterations = native.get('iterations')
        okay = iterations is None or (type(iterations) is int and type(limit) is int
                                      and 0 <= iterations <= limit)
        C.require(okay or (job['status'] == 'UNKNOWN' and native.get('success') is False
                           and native.get('resource_failure')), 'native iteration failure retained explicitly')
    return True


def unknown(reason, resource_failure=None):
    return dict(schema=SCHEMA, status='UNKNOWN', search_status='UNKNOWN',
                all_passed=False, workflow_verified=False, reduction_verified=False,
                certificate_verified=False, finite_augmented_cone_infeasibility_certified=False,
                independent_check=None, reason=reason, resource_failure=resource_failure,
                joint_work=C.ledger(), **C.FLAGS)


def _audit(directory, deadline):
    d = Path(directory)
    C.require(read(d/'protocol.json') == C.protocol(), 'fixed declared reduction protocol')
    C.require(read(d/'parent.json') == C.parent(), 'designated mathematical inputs')
    premises = [read(C.ROOT/name, C.CAPS[name]) for name in (
        C.CHART_REPORT, C.CHART_REVIEW, C.REPORT, C.REVIEW)]
    C.license_parent(*premises)
    tests = read(d/'tests.json', 1048576)
    match = re.search(r'Ran (\d+) tests?', tests.get('stderr', ''))
    C.require(tests.get('returncode') == 0 and match
              and tests['stderr'].rstrip().endswith('OK'), 'reserved synthetic suite passed')
    C.require(tests.get('synthetic_work') == C.synthetic_receipt(tests.get('stdout', '')),
              'cumulative development and frozen synthetic work bound')
    C.require(read(d/'run_started.json') == dict(one_fixed_search=True), 'one producer attempt')
    execution = read(d/'execution.json', 1048576)
    terminal = d/'jobs/search-job.json'
    if not terminal.exists():
        transport = verify_transport(execution)
        C.require(transport['status'] != 'available', 'available producer needs terminal record')
        result = unknown(transport.get('reason', 'no terminal worker record'))
        result.update(workflow_verified=True, tests_passed=int(match.group(1)))
        return result
    job = read(terminal)
    proposal_path, reduction_path = d/'jobs/proposal.json', d/'jobs/reduction.json'
    outcome = read(proposal_path, 8388608) if proposal_path.exists() else None
    reduction = read(reduction_path, 67108864) if reduction_path.exists() else None
    completed = verify_job(job, execution, outcome, reduction)
    if reduction is None or not completed:
        result = unknown(job.get('reason') or 'complete reduction outcome unavailable')
        result.update(workflow_verified=True, job=job, tests_passed=int(match.group(1)))
        return result
    chart = read(C.ROOT/C.CHART, C.CAPS[C.CHART])
    rays = read(C.ROOT/C.RAYS, C.CAPS[C.RAYS])['rays']
    geometry = read(C.ROOT/C.GEOMETRY, C.CAPS[C.GEOMETRY])
    check = CORE.verify_outcome(chart, premises[1], rays, geometry, premises[3], reduction, outcome,
                deadline=deadline, max_operations=80000000, max_cells=6000000, max_bits=4096)
    no_global_claim(check)
    C.require(check.get('verified') is True and check.get('complete') is True
              and check.get('reduction_verified') is True, 'complete exact reduction proof')
    proved = check.get('finite_augmented_cone_infeasibility_certified') is True
    C.require(check.get('certificate_verified') is proved, 'separate complete separator verdict')
    if proved:
        C.require(check.get('status') == 'FINITE_CONE_INFEASIBLE', 'exact separator status')
    result = dict(schema=SCHEMA,
                  status='FINITE_CONE_INFEASIBLE' if proved else 'REDUCTION_VERIFIED',
                  search_status=job['status'], all_passed=True, workflow_verified=True,
                  reduction_verified=True, certificate_verified=proved,
                  finite_augmented_cone_infeasibility_certified=proved,
                  independent_check=check, job=job, resource_failure=None,
                  joint_work=dict(C.ledger(), independent_operations=check.get('audit_operations')),
                  synthetic_work=tests['synthetic_work'],
                  tests_passed=int(match.group(1)),
                  scope='exact reduction equivalence and optional separator of the augmented finite cone',
                  numerical_solver_independently_replayed=False, **C.FLAGS)
    if time.monotonic() > deadline:
        raise TimeoutError('complete independent reduction deadline')
    return result


def audit(directory, *, write=False, time_limit=3600):
    C.runtime()
    C.require(type(time_limit) in (int, float) and math.isfinite(time_limit)
              and 0 < time_limit <= 3600, 'bounded independent deadline')
    d = Path(directory)
    target, marker = d/'independent_verification.json', d/'independent_started.json'
    if target.exists() or marker.exists():
        raise FileExistsError('sole80m audit already started or consumed')
    with marker.open('x') as handle:
        handle.write('{"one_final_independent_audit":true,"max_operations":80000000}\n')
    start, cpu = time.monotonic(), time.process_time()
    deadline = start+time_limit
    previous = resource.getrlimit(resource.RLIMIT_AS)
    cap = 6*1024**3
    C.require(previous[1] == resource.RLIM_INFINITY or previous[1] >= cap,
              'supported independent memory boundary')
    token = _IO.set([0, 0, deadline])
    try:
        resource.setrlimit(resource.RLIMIT_AS, (cap, previous[1]))
        try:
            result = _audit(d, deadline)
        except (OverflowError, TimeoutError, MemoryError) as error:
            result = unknown(str(error) or type(error).__name__, dict(type=type(error).__name__,
                      consumed_counts=getattr(error, 'independent_audit_counts', None)))
        except (ValueError, TypeError, KeyError) as error:
            result = unknown(str(error) or type(error).__name__)
            result['validation_failure'] = dict(type=type(error).__name__,
                                                reason=str(error) or type(error).__name__)
        cost = dict(elapsed_seconds=time.monotonic()-start, cpu_seconds=time.process_time()-cpu,
                    peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                    observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),
                    audit_memory_limit_bytes=cap, audit_memory_limit_enforced=True, pid=os.getpid())
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
            result = unknown(str(error) or type(error).__name__, dict(type=type(error).__name__))
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
    print(json.dumps({key:result.get(key) for key in ('schema', 'status', 'search_status',
        'all_passed', 'reduction_verified', 'certificate_verified', 'resource_failure', 'cost')}))

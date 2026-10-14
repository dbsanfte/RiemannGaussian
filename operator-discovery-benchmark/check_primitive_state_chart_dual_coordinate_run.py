"""One audit of sparse-search accounting and an optional exact separator."""
import argparse
import contextvars
import json
import math
import os
from pathlib import Path
import re
import resource
import time
import primitive_state_chart_dual_coordinate_protocol as C
import check_primitive_state_chart_dual_coordinate as CORE
from check_primitive_state_chart_dual_search_run import verify_transport, no_global_claim

SCHEMA = 'primitive-state-chart-dual-coordinate-independent-review-v1'
_IO = contextvars.ContextVar('chart_dual_coordinate_io', default=None)


def read(path, cap=65536):
    with Path(path).open('rb') as handle:
        data = handle.read(cap+1)
    if len(data) > cap:
        raise OverflowError('independent bounded input')
    state = _IO.get()
    if state is not None:
        state[0] += 2*(len(data)//64+1); state[1] += len(data)
        if state[0] > 10000000:
            raise OverflowError('independent I/O reserve within preparation')
        if time.monotonic() > state[2]:
            raise TimeoutError('independent input deadline')
    return json.loads(data)


def verify_job(job, execution, outcome):
    transport = verify_transport(execution)
    no_global_claim(job)
    C.require(job.get('ledger') == C.ledger(), 'single complete coordinate allocation')
    C.require(job.get('status') in ('CERTIFICATE_PROPOSED','NONCERTIFIED','UNKNOWN')
              and type(job.get('producer_complete')) is bool
              and type(job.get('deadline_exceeded')) is bool, 'explicit producer disposition')
    if transport['status'] == 'available':
        C.require(transport.get('value') == dict(file='jobs/search-job.json',
                  status=job['status'], cost=job.get('cost'), **C.FLAGS),
                  'terminal record matches transport')
    else:
        C.require(job['status'] == 'UNKNOWN', 'failed transport cannot propose admission')
    cost = job.get('cost', {})
    for key in ('elapsed_seconds','cpu_seconds','peak_rss_kib'):
        value = cost.get(key)
        C.require(type(value) in (int,float) and math.isfinite(value) and value >= 0,
                  'finite worker resource measurement')
    if not job['producer_complete']:
        C.require(job['status'] == 'UNKNOWN', 'incomplete producer remains unknown')
        return False
    C.require(transport['status'] == 'available' and job['deadline_exceeded'] is False
              and cost['elapsed_seconds'] <= 3600 and cost['peak_rss_kib'] <= 6*1024**2
              and cost.get('observed_threads_at_completion') == 1,
              'completed worker respects enforced limits')
    C.require(type(outcome) is dict and outcome.get('status') == job['status'],
              'complete saved coordinate outcome')
    no_global_claim(outcome)
    counts = outcome.get('stage_counts')
    C.require(type(counts) is dict and counts == job.get('stage_counts') and 'model' in counts
              and set(counts) <= {'model','numerical','restoration'}, 'bound started-stage counters')
    for stage, values in counts.items():
        C.require(type(values) is dict, 'explicit stage counters')
        for key in ('operations','peak_live_cells','maximum_rational_bits'):
            C.require(type(values.get(key)) is int and values[key] >= 0, 'nonnegative stage counter')
        C.require(values['operations'] <= C.ALLOCATIONS[stage], 'stage operation allowance')
        if job['status'] != 'UNKNOWN':
            C.require(values['peak_live_cells'] <= 6000000 and values['maximum_rational_bits'] <= 4096,
                      'completed rational limits')
    C.require(outcome.get('route') == job.get('route') == 'coordinate_descent',
              'one declared coordinate route')
    numerical = outcome.get('numerical')
    if numerical is not None:
        C.require(type(numerical) is dict and numerical.get('counts') == counts.get('numerical'),
                  'same saved numerical consumed counters')
        C.require(type(numerical.get('max_operations')) is int
                  and numerical['max_operations'] == C.ALLOCATIONS['numerical'],
                  'actual trajectory uses the fixed numerical allocation')
    if 'restoration' in counts:
        C.require(type(numerical) is dict and numerical.get('complete') is True
                  and type(numerical.get('selected')) is dict,
                  'one selected complete trajectory before restoration')
    return True


def unknown(reason, resource_failure=None):
    return dict(schema=SCHEMA, status='UNKNOWN', search_status='UNKNOWN',
                all_passed=False, workflow_verified=False, certificate_verified=False,
                finite_augmented_cone_infeasibility_certified=False,
                independent_check=None, reason=reason, resource_failure=resource_failure,
                joint_work=C.ledger(), **C.FLAGS)


def _audit(directory, deadline):
    d = Path(directory)
    C.require(read(d/'protocol.json') == C.protocol(), 'fixed coordinate protocol')
    C.require(read(d/'parent.json') == C.parent(), 'designated mathematical inputs')
    premises = [read(C.ROOT/name,C.CAPS[name]) for name in (
        C.CHART_REPORT,C.CHART_REVIEW,C.REPORT,C.REVIEW)]
    C.license_parent(*premises)
    tests = read(d/'tests.json',1048576)
    match = re.search(r'Ran (\d+) tests?',tests.get('stderr',''))
    C.require(tests.get('returncode') == 0 and match and tests['stderr'].rstrip().endswith('OK'),
              'reserved synthetic suite passed')
    C.require(tests.get('synthetic_work') == C.synthetic_receipt(tests.get('stdout','')),
              'cumulative development and frozen synthetic work')
    C.require(read(d/'run_started.json') == dict(one_fixed_search=True),'one producer attempt')
    execution = read(d/'execution.json',1048576)
    terminal = d/'jobs/search-job.json'
    if not terminal.exists():
        transport = verify_transport(execution)
        C.require(transport['status'] != 'available','available producer needs terminal record')
        result = unknown(transport.get('reason','no terminal worker record'))
        result.update(workflow_verified=True,tests_passed=int(match.group(1)))
        return result
    job = read(terminal)
    path = d/'jobs/proposal.json'
    outcome = read(path,8388608) if path.exists() else None
    if not verify_job(job,execution,outcome):
        result = unknown(job.get('reason') or 'complete outcome unavailable')
        result.update(workflow_verified=True,job=job,tests_passed=int(match.group(1)))
        return result
    chart = read(C.ROOT/C.CHART,C.CAPS[C.CHART])
    rays = read(C.ROOT/C.RAYS,C.CAPS[C.RAYS])['rays']
    geometry = read(C.ROOT/C.GEOMETRY,C.CAPS[C.GEOMETRY])
    reduction = read(C.ROOT/C.REDUCTION,C.CAPS[C.REDUCTION])
    check = CORE.verify_outcome(chart,premises[1],rays,geometry,reduction,premises[3],outcome,
                deadline=deadline,max_operations=90000000,max_cells=6000000,max_bits=4096)
    no_global_claim(check)
    C.require(check.get('verified') is True,'completed independent outcome check')
    proved = check.get('finite_augmented_cone_infeasibility_certified') is True
    C.require(check.get('certificate_verified') is proved and check.get('complete') is proved,
              'only a complete exact separator is a mathematical admission')
    C.require(check.get('status') == ('FINITE_CONE_INFEASIBLE' if proved else job['status']),
              'explicit exact or numerical disposition')
    result = dict(schema=SCHEMA,status=check['status'],search_status=job['status'],
                  all_passed=proved,workflow_verified=True,certificate_verified=proved,
                  finite_augmented_cone_infeasibility_certified=proved,
                  independent_check=check,job=job,resource_failure=None,
                  joint_work=dict(C.ledger(),independent_operations=check.get('audit_operations')),
                  synthetic_work=tests['synthetic_work'],tests_passed=int(match.group(1)),
                  scope='one sparse numerical proposal and optional full finite-cone separator',
                  numerical_trajectory_replayed=False,numerical_scores_verified=False,**C.FLAGS)
    if time.monotonic() > deadline:
        raise TimeoutError('complete independent coordinate deadline')
    return result


def audit(directory, *, write=False, time_limit=3600):
    C.runtime()
    C.require(type(time_limit) in (int,float) and math.isfinite(time_limit) and 0 < time_limit <= 3600,
              'bounded independent deadline')
    d = Path(directory)
    target,marker = d/'independent_verification.json',d/'independent_started.json'
    if target.exists() or marker.exists():
        raise FileExistsError('sole90m audit already started or consumed')
    with marker.open('x') as handle:
        handle.write('{"one_final_independent_audit":true,"max_operations":90000000}\n')
    start,cpu = time.monotonic(),time.process_time(); deadline = start+time_limit
    previous = resource.getrlimit(resource.RLIMIT_AS); cap = 6*1024**3
    C.require(previous[1] == resource.RLIM_INFINITY or previous[1] >= cap,
              'supported independent memory boundary')
    token = _IO.set([0,0,deadline])
    try:
        resource.setrlimit(resource.RLIMIT_AS,(cap,previous[1]))
        try:
            result = _audit(d,deadline)
        except (OverflowError,TimeoutError,MemoryError) as error:
            result = unknown(str(error) or type(error).__name__,dict(type=type(error).__name__,
                consumed_counts=getattr(error,'independent_audit_counts',None)))
        except (ValueError,TypeError,KeyError) as error:
            result = unknown(str(error) or type(error).__name__)
            result['validation_failure'] = dict(type=type(error).__name__,reason=str(error))
        cost = dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,
                    peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                    observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),
                    audit_memory_limit_bytes=cap,audit_memory_limit_enforced=True,pid=os.getpid())
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
        except (OverflowError,TimeoutError,MemoryError) as error:
            result = unknown(str(error) or type(error).__name__,dict(type=type(error).__name__))
            result['cost'] = cost
            if write:
                target.write_bytes(C.encoded(result))
        return result
    finally:
        resource.setrlimit(resource.RLIMIT_AS,previous)
        _IO.reset(token)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory'); parser.add_argument('--write',action='store_true')
    args = parser.parse_args(); result = audit(args.directory,write=args.write)
    print(json.dumps({key:result.get(key) for key in ('schema','status','search_status',
        'all_passed','workflow_verified','certificate_verified','resource_failure','validation_failure','cost')}))

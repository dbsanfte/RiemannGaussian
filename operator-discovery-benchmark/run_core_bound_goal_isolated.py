"""Resume the unchanged bound-goal experiment with isolated test processes.

pilot-001 and every frozen source remain immutable.  The only change is
test orchestration: one module's process limits cannot affect another owner.
"""
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

import run_core_bound_goal_search as ORIGINAL
from prime_bank_candidates import Meter


ROOT = ORIGINAL.ROOT
OUT = ROOT/'core-bound-goal-results/pilot-002'
FAILED = ORIGINAL.OUT
MEMORY = 2*1024**3
SUITES = [dict(owner='root', modules=['test_core_bound_goal_search', 'test_run_core_bound_goal_search',
                                     'test_run_core_bound_goal_isolated']),
          dict(owner='checker', modules=['test_check_core_bound_goal_search'])]
FILES = ORIGINAL.FILES+['run_core_bound_goal_isolated.py', 'core_bound_goal_isolated_protocol.txt',
                         'test_run_core_bound_goal_isolated.py', 'core_bound_goal_isolated_development.json']
read, write = ORIGINAL.read, ORIGINAL.write


def prior_failure_cost(directory):
    failure = read(directory/'terminal_failure.json')
    tests = read(directory/'frozen_tests.json')
    if (failure['error'] != 'frozen owned tests failed' or tests['returncode'] == 0 or
            (directory/'report.json').exists() or (directory/'search.json').exists()):
        raise ValueError('this retry accounts only for the preserved pre-search test failure')
    return dict(startup_operations=2000000, frozen_test_operations=tests['operations'],
                total_operations=2000000+tests['operations'])


def run_owned_suites(root, suites, memory=MEMORY):
    results = []
    script = ('import resource,runpy,sys; '
              f'resource.setrlimit(resource.RLIMIT_AS,({memory},resource.getrlimit(resource.RLIMIT_AS)[1])); '
              'sys.argv=["unittest"]+sys.argv[1:]; runpy.run_module("unittest",run_name="__main__")')
    for suite in suites:
        started = time.monotonic()
        run = subprocess.run([sys.executable, '-B', '-c', script, *suite['modules']], cwd=root,
                             capture_output=True, text=True, timeout=300)
        results.append(dict(owner=suite['owner'], modules=suite['modules'], returncode=run.returncode,
            stdout=run.stdout, stderr=run.stderr,
            operations=sum(map(int, re.findall(r'operations=(\d+)', run.stdout))),
            elapsed_seconds=time.monotonic()-started))
    return results


def verify():
    ORIGINAL.verify()
    for name in read(OUT/'source_files.json'):
        if (ROOT/name).read_bytes() != (OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('changed isolated-run frozen source '+name)


def main():
    import check_core_bound_goal_search as CHECK
    started = time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS, (4*1024**3, resource.getrlimit(resource.RLIMIT_AS)[1]))
    ORIGINAL.verify()
    ORIGINAL.require_current_input(ROOT, ORIGINAL.PARENT)
    failed_cost = prior_failure_cost(FAILED)
    development = ORIGINAL.validate_receipts([read(ROOT/name) for name in ORIGINAL.RECEIPTS+
                                              ['core_bound_goal_isolated_development.json']])
    if OUT.exists():
        raise FileExistsError('preserve every terminal attempt; no unchanged restart')
    OUT.mkdir(parents=True)
    (OUT/'source_snapshot').mkdir()
    for name in FILES:
        (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(OUT/'source_files.json', FILES)
    write(OUT/'protocol.json', dict(schema='core-bound-goal-isolated-run-v1', input=ORIGINAL.INPUT,
        spec=ORIGINAL.P.DEFAULT_SPEC, previous_failed_attempt=str(FAILED.relative_to(ROOT)),
        prior_failure_cost=failed_cost, only_change='run test owners in separate processes',
        suites=SUITES, memory_limit_bytes=4*1024**3, test_memory_limit_bytes=MEMORY,
        runtime_limit_seconds=1800, inclusive_operation_cap=ORIGINAL.CAP,
        hashes=False, actual_source_observations=0, model_calls_in_search=0,
        whole_signed_bound_proved=False, RH_proved=False))
    meter = Meter(ORIGINAL.CAP, 1800)
    meter.charge(2000000)
    tests = run_owned_suites(ROOT, SUITES)
    test_ops = sum(r['operations'] for r in tests)
    write(OUT/'frozen_tests.json', dict(returncode=int(any(r['returncode'] for r in tests)),
        operations=test_ops, suites=tests))
    if any(r['returncode'] for r in tests):
        raise RuntimeError('isolated frozen tests failed')
    parent = read(ROOT/ORIGINAL.INPUT)
    result = ORIGINAL.P.search(parent, ORIGINAL.P.DEFAULT_SPEC, meter)
    checked = CHECK.verify_search(parent, result, meter)
    if not checked['verified']:
        raise ArithmeticError('independent bound-goal verification failed')
    artifact = str((OUT/'search.json').relative_to(ROOT))
    next_input = ORIGINAL.P.feedback(result, ORIGINAL.INPUT, artifact)
    feedback_check = CHECK.verify_feedback(result, next_input, ORIGINAL.INPUT, artifact, meter)
    if not feedback_check['verified']:
        raise ArithmeticError('independent feedback verification failed')
    write(OUT/'search.json', result)
    write(OUT/'verification.json', dict(search=checked, feedback=feedback_check))
    write(OUT/'next_search_input.json', next_input)
    total = meter.operations+development+test_ops+failed_cost['total_operations']
    if total > ORIGINAL.CAP:
        raise OverflowError('inclusive cap includes preserved failure and all development/frozen tests')
    verify()
    report = dict(status='AUXILIARY_IDENTITIES_AND_BACKWARD_BOUND_REQUIREMENTS_VERIFIED_WITH_OPEN_SIGNED_CORE',
        **result['statistics'], alpha=parent['selected_source_representation']['alpha'],
        gamma=parent['selected_source_representation']['gamma'],
        representative_target=result['generated_bound_targets'][0] if result['generated_bound_targets'] else None,
        actual_source_observations=0, model_calls_in_search=0,
        prior_failure_cost=failed_cost, main_operations=meter.operations, inclusive_operations=total,
        elapsed_seconds=time.monotonic()-started, peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        whole_signed_bound_proved=False, RH_proved=False)
    write(OUT/'report.json', report)
    publication = OUT/'publication-001'
    publication.mkdir()
    raw = (OUT/'next_search_input.json').read_bytes()
    for path in (publication/'next_search_input.json', ROOT/ORIGINAL.PUBLIC_INPUT):
        with path.open('xb') as stream:
            stream.write(raw)
    write(OUT.parent/'latest.json', dict(report=str((OUT/'report.json').relative_to(ROOT)),
        input=ORIGINAL.PUBLIC_INPUT, status=report['status'], whole_signed_bound_proved=False, RH_proved=False))
    print(json.dumps({k: v for k, v in report.items() if k != 'representative_target'}), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        if OUT.exists() and not (OUT/'terminal_failure.json').exists():
            write(OUT/'terminal_failure.json', dict(error_type=type(error).__name__, error=str(error),
                status='incomplete', whole_signed_bound_proved=False, RH_proved=False))
        raise

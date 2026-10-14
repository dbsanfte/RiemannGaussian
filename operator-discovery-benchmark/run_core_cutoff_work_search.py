"""Freeze and run exact cutoff bound synthesis; numerical work is deferred."""
import json
from pathlib import Path
import resource
import time

import core_cutoff_work_search as P
import run_core_weighted_height_search as PRIOR
from prime_bank_candidates import Meter


ROOT = Path(__file__).resolve().parent
INPUT = 'candidate10_weighted_height_obligation.json'
PUBLIC_INPUT = 'candidate10_cutoff_work_obligation.json'
PARENT = ROOT/'core-weighted-height-results/pilot-001'
OUT = ROOT/'core-cutoff-work-results/pilot-001'
CAP = 600000000
RECEIPTS = ['core_cutoff_work_development.json', 'core_cutoff_work_checker_development.json']
FILES = ['core_cutoff_work_search.py', 'core_cutoff_bound_planner.py',
    'check_core_cutoff_work_search.py', 'run_core_cutoff_work_search.py',
    'test_core_cutoff_work_search.py', 'test_check_core_cutoff_work_search.py',
    'core_cutoff_work_search_protocol.txt', 'CORE_CUTOFF_TRANSITION_RULE_REVIEW_022.txt',
    'CORE_CUTOFF_TRANSITION_SCOPE_REVIEW_023.txt', 'CORE_CUTOFF_AUTOMATIC_CONTROL_REVIEW_024.txt',
    'prime_bank_candidates.py', INPUT]+RECEIPTS
read, write = PRIOR.read, PRIOR.write


def require_input():
    if (ROOT/INPUT).read_bytes() != (PARENT/'publication-001/next_search_input.json').read_bytes():
        raise ValueError('exact preceding published obligation required')
    if read(PARENT/'report.json')['status'] != 'WEIGHTED_HEIGHT_PROOF_SEARCH_VERIFIED_WITH_OPEN_SIGNED_CORE':
        raise ValueError('verified preceding weighted-height study required')


def verify():
    PRIOR.verify()
    require_input()
    for name in read(OUT/'source_files.json'):
        if (ROOT/name).read_bytes() != (OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen cutoff-work source '+name)


def main():
    import check_core_cutoff_work_search as CHECK
    started = time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS, (4*1024**3, resource.getrlimit(resource.RLIMIT_AS)[1]))
    PRIOR.verify()
    require_input()
    development = PRIOR.PRIOR.PRIOR.ORIGINAL.validate_receipts([read(ROOT/n) for n in RECEIPTS])
    # Passed development checks are not rerun without a source change. The
    # frozen study independently verifies every generated actual certificate.
    OUT.mkdir(parents=True, exist_ok=False)
    try:
        (OUT/'source_snapshot').mkdir()
        for name in FILES:
            (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
        write(OUT/'source_files.json', FILES)
        write(OUT/'protocol.json', dict(schema='core-cutoff-work-run-v1', input=INPUT,
            memory_limit_bytes=4*1024**3, runtime_limit_seconds=1800,
            inclusive_operation_cap=CAP, imported_rules=P.RULES,
            diagnostics=P.DIAGNOSTIC_SPEC, actual_source_observations=0,
            model_calls_in_search=0, fitted_constants=0, hashes=False,
            testing='owned development suites plus affected checks; independent frozen certificate replay',
            whole_signed_bound_proved=False, RH_proved=False))
        meter = Meter(CAP-development, 1800)
        meter.charge(2000000)
        parent = read(ROOT/INPUT)
        result = P.search(parent, meter)
        write(OUT/'search.json', result)
        checked = CHECK.verify_search(parent, result, meter)
        if not checked['verified']:
            raise ArithmeticError('independent cutoff bound verification failed')
        artifact = str((OUT/'search.json').relative_to(ROOT))
        next_input = P.feedback(parent, result, INPUT, artifact)
        feedback_check = CHECK.verify_feedback(parent, result, next_input, INPUT, artifact, meter)
        if not feedback_check['verified']:
            raise ArithmeticError('independent complete source feedback verification failed')
        write(OUT/'verification.json', dict(search=checked, feedback=feedback_check))
        write(OUT/'next_search_input.json', next_input)
        total = meter.operations+development
        if total > CAP:
            raise OverflowError('inclusive operation cap includes all recorded development checks')
        verify()
        chosen = []
        for target in result['targets']:
            program = target['programs'][target['selected_program']]
            b = program['bound_search']
            route = b['routes'][b['selected_route']] if b['selected_route'] is not None else None
            chosen.append(dict(target_id=target['target_id'], corrected=program['subtract_exact_head'],
                goal_U_power=b['goal_U_power'], zero_sector_control=b['zero_sector_control'],
                route=None if route is None else {k: route[k] for k in
                    ['method', 'aggregation', 'status', 'recurrence', 'nonnegative_cost', 'relation_to_original_goal']
                    if k in route},
                next_target_count=len(b['next_bound_targets']), actual_arithmetic_bound_proved=b['goal_proved']))
        report = dict(status='CUTOFF_BOUND_COMPOSITIONS_VERIFIED_WITH_OPEN_SIGNED_CORE', **result['statistics'],
            selected_routes=chosen, actual_source_observations=0, numerical_diagnostics_executed=False,
            model_calls_in_search=0, fitted_constants=0, development_operations=development,
            main_operations=meter.operations, inclusive_operations=total,
            elapsed_seconds=time.monotonic()-started,
            peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            new_uniform_signed_arithmetic_estimates=0, whole_signed_bound_proved=False, RH_proved=False)
        write(OUT/'report.json', report)
        publication = OUT/'publication-001'
        publication.mkdir()
        raw = (OUT/'next_search_input.json').read_bytes()
        for path in (publication/'next_search_input.json', ROOT/PUBLIC_INPUT):
            with path.open('xb') as stream:
                stream.write(raw)
        write(OUT.parent/'latest.json', dict(report=str((OUT/'report.json').relative_to(ROOT)),
            input=PUBLIC_INPUT, status=report['status'], whole_signed_bound_proved=False, RH_proved=False))
        print(json.dumps(report), flush=True)
    except Exception as error:
        write(OUT/'terminal_failure.json', dict(error_type=type(error).__name__, error=str(error),
            status='incomplete', whole_signed_bound_proved=False, RH_proved=False))
        raise


if __name__ == '__main__':
    main()

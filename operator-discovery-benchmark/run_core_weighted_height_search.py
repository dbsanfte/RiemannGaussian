"""Immutable weighted-height proof search with separately owned test processes."""
import json
from pathlib import Path
import resource
import time

import core_weighted_height_search as P
import run_core_moment_bound_search as PRIOR
from prime_bank_candidates import Meter


ROOT = Path(__file__).resolve().parent
INPUT = 'candidate10_moment_bound_obligation.json'
PUBLIC_INPUT = 'candidate10_weighted_height_obligation.json'
PARENT = ROOT/'core-moment-bound-results/pilot-001'
OUT = ROOT/'core-weighted-height-results/pilot-001'
CAP = 300000000
SUITES = [dict(owner='root', modules=['test_core_weighted_height_search']),
          dict(owner='checker', modules=['test_check_core_weighted_height_search'])]
RECEIPTS = ['core_weighted_height_development.json', 'core_weighted_height_checker_development.json']
FILES = ['core_weighted_height_search.py', 'check_core_weighted_height_search.py',
    'run_core_weighted_height_search.py', 'test_core_weighted_height_search.py',
    'test_check_core_weighted_height_search.py', 'core_weighted_height_search_protocol.txt',
    'CORE_WEIGHTED_MOMENT_RULE_REVIEW_020.txt', 'CORE_WEIGHTED_MOMENT_SHARPNESS_REVIEW_021.txt',
    'prime_bank_candidates.py', INPUT]+RECEIPTS
read, write = PRIOR.read, PRIOR.write
load_context = PRIOR.load_context


def require_input():
    if (ROOT/INPUT).read_bytes() != (PARENT/'publication-001/next_search_input.json').read_bytes():
        raise ValueError('exact preceding published obligation required')
    if read(PARENT/'report.json')['status'] != 'MOMENT_PROOF_SEARCH_VERIFIED_WITH_OPEN_SIGNED_CORE':
        raise ValueError('verified preceding study required')


def verify():
    PRIOR.verify()
    require_input()
    for name in read(OUT/'source_files.json'):
        if (ROOT/name).read_bytes() != (OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen weighted-height source '+name)


def main():
    import check_core_weighted_height_search as CHECK
    started = time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS, (4*1024**3, resource.getrlimit(resource.RLIMIT_AS)[1]))
    PRIOR.verify()
    require_input()
    development = PRIOR.PRIOR.ORIGINAL.validate_receipts([read(ROOT/n) for n in RECEIPTS])
    if OUT.exists():
        raise FileExistsError('preserve every terminal attempt; no unchanged restart')
    OUT.mkdir(parents=True)
    (OUT/'source_snapshot').mkdir()
    for name in FILES:
        (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(OUT/'source_files.json', FILES)
    context = load_context()
    write(OUT/'context.json', context)
    write(OUT/'protocol.json', dict(schema='core-weighted-height-run-v1', input=INPUT, spec=P.DEFAULT_SPEC,
        owner_suites=SUITES, memory_limit_bytes=4*1024**3, test_memory_limit_bytes=2*1024**3,
        runtime_limit_seconds=1800, inclusive_operation_cap=CAP,
        source_observations=0, fitted_constants=0, model_calls_in_search=0, hashes=False,
        imported_theorems=P.RULES, whole_signed_bound_proved=False, RH_proved=False))
    meter = Meter(CAP, 1800)
    meter.charge(2000000)
    tests = PRIOR.PRIOR.run_owned_suites(ROOT, SUITES)
    test_ops = sum(t['operations'] for t in tests)
    write(OUT/'frozen_tests.json', dict(returncode=int(any(t['returncode'] for t in tests)),
        suites=tests, operations=test_ops))
    if any(t['returncode'] for t in tests):
        raise RuntimeError('isolated frozen weighted-height suites failed')
    parent = read(ROOT/INPUT)
    result = P.search(parent, context, P.DEFAULT_SPEC, meter)
    checked = CHECK.verify_search(parent, context, result, meter)
    if not checked['verified']:
        raise ArithmeticError('independent weighted-height proof search verification failed')
    artifact = str((OUT/'search.json').relative_to(ROOT))
    next_input = P.feedback(parent, result, INPUT, artifact)
    fb_check = CHECK.verify_feedback(parent, result, next_input, INPUT, artifact, meter)
    if not fb_check['verified']:
        raise ArithmeticError('independent full-source feedback verification failed')
    write(OUT/'search.json', result)
    write(OUT/'verification.json', dict(search=checked, feedback=fb_check))
    write(OUT/'next_search_input.json', next_input)
    total = meter.operations+development+test_ops
    if total > CAP:
        raise OverflowError('inclusive cap includes every development and frozen check')
    verify()
    selected = []
    for target in result['targets']:
        if target['selected_line'] is None:
            continue
        line = target['lines'][target['selected_line']]
        plan = line['plans'][line['selected_plan']]
        selected.append(dict(target_id=target['target_id'], sigma=line['sigma'],
            kappa=plan['kappa'], epsilon=plan['epsilon'], tau=plan['tau'],
            high_U_power=plan['high_U_power'], required_low_U_power=plan['required_low_U_power'],
            generic_low_U_power=plan['generic_low_U_power'], low_status=plan['low_obligation_status'],
            inherited_component_bound_proved=target['inherited_component_bound_proved']))
    report = dict(status='WEIGHTED_HEIGHT_PROOF_SEARCH_VERIFIED_WITH_OPEN_SIGNED_CORE', **result['statistics'],
        selected_plans=selected, actual_source_observations=0, fitted_constants=0, model_calls_in_search=0,
        main_operations=meter.operations, inclusive_operations=total,
        elapsed_seconds=time.monotonic()-started, peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        whole_signed_bound_proved=False, RH_proved=False)
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


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        if OUT.exists() and not (OUT/'terminal_failure.json').exists():
            write(OUT/'terminal_failure.json', dict(error_type=type(error).__name__, error=str(error),
                status='incomplete', whole_signed_bound_proved=False, RH_proved=False))
        raise

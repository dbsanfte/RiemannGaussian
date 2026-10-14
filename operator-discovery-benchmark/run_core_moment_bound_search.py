"""One immutable study of executable moment-proof search, with isolated tests."""
import json
from pathlib import Path
import resource
import time

import core_moment_bound_search as P
import run_core_bound_goal_isolated as PRIOR
from prime_bank_candidates import Meter


ROOT = Path(__file__).resolve().parent
INPUT = 'candidate10_bound_goal_obligation.json'
PUBLIC_INPUT = 'candidate10_moment_bound_obligation.json'
PARENT = ROOT/'core-bound-goal-results/pilot-002'
OUT = ROOT/'core-moment-bound-results/pilot-001'
CAP = 300000000
SUITES = [dict(owner='root', modules=['test_core_moment_bound_search']),
          dict(owner='checker', modules=['test_check_core_moment_bound_search'])]
RECEIPTS = ['core_moment_bound_development.json', 'core_moment_bound_checker_development.json']
FILES = ['core_moment_bound_search.py', 'check_core_moment_bound_search.py',
    'run_core_moment_bound_search.py', 'test_core_moment_bound_search.py',
    'test_check_core_moment_bound_search.py', 'core_moment_bound_search_protocol.txt',
    'JOINT_REMAINDER_MOMENT_REVIEW_018.txt', 'JOINT_REMAINDER_MOMENT_CHECK_019.txt',
    'prime_bank_candidates.py', INPUT, 'candidate10_frame_bound_obligation.json']+RECEIPTS
read, write = PRIOR.read, PRIOR.write


def load_context():
    prior = read(PARENT/'search.json')
    frame = read(ROOT/'candidate10_frame_bound_obligation.json')
    seen = set()
    while frame.get('schema') != 'detector-bound-program-search-input-v1':
        if id(frame) in seen:
            raise ValueError('acyclic inherited channel chain')
        seen.add(id(frame))
        frame = frame['parent_obligation']
    return dict(complete_signed_join=prior['complete_signed_join'],
        channel_programs=frame['generated_bound_program_obligations'])


def require_input():
    if (ROOT/INPUT).read_bytes() != (PARENT/'publication-001/next_search_input.json').read_bytes():
        raise ValueError('exact current published obligation required')
    if read(PARENT/'report.json')['status'] != 'AUXILIARY_IDENTITIES_AND_BACKWARD_BOUND_REQUIREMENTS_VERIFIED_WITH_OPEN_SIGNED_CORE':
        raise ValueError('verified preceding study required')


def verify():
    PRIOR.verify()
    require_input()
    for name in read(OUT/'source_files.json'):
        if (ROOT/name).read_bytes() != (OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen moment-study source '+name)


def main():
    import check_core_moment_bound_search as CHECK
    started = time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS, (4*1024**3, resource.getrlimit(resource.RLIMIT_AS)[1]))
    PRIOR.verify()
    require_input()
    development = PRIOR.ORIGINAL.validate_receipts([read(ROOT/n) for n in RECEIPTS])
    if OUT.exists():
        raise FileExistsError('preserve every terminal attempt; no unchanged restart')
    OUT.mkdir(parents=True)
    (OUT/'source_snapshot').mkdir()
    for name in FILES:
        (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(OUT/'source_files.json', FILES)
    context = load_context()
    write(OUT/'context.json', context)
    write(OUT/'protocol.json', dict(schema='core-moment-bound-run-v1', input=INPUT, spec=P.DEFAULT_SPEC,
        owner_suites=SUITES, memory_limit_bytes=4*1024**3, test_memory_limit_bytes=2*1024**3,
        runtime_limit_seconds=1800, inclusive_operation_cap=CAP,
        source_observations=0, fitted_constants=0, model_calls_in_search=0, hashes=False,
        imported_theorems=P.RULES, whole_signed_bound_proved=False, RH_proved=False))
    meter = Meter(CAP, 1800)
    meter.charge(2000000)
    tests = PRIOR.run_owned_suites(ROOT, SUITES)
    test_ops = sum(t['operations'] for t in tests)
    write(OUT/'frozen_tests.json', dict(returncode=int(any(t['returncode'] for t in tests)),
        suites=tests, operations=test_ops))
    if any(t['returncode'] for t in tests):
        raise RuntimeError('isolated frozen moment suites failed')
    parent = read(ROOT/INPUT)
    result = P.search(parent, context, P.DEFAULT_SPEC, meter)
    checked = CHECK.verify_search(parent, context, result, meter)
    if not checked['verified']:
        raise ArithmeticError('independent moment proof search verification failed')
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
    report = dict(status='MOMENT_PROOF_SEARCH_VERIFIED_WITH_OPEN_SIGNED_CORE', **result['statistics'],
        paid_components=[dict(target_id=t['target_id'],
            sigma=t['candidate_lines'][t['selected']]['sigma'],
            energy_X_power=t['candidate_lines'][t['selected']]['recovered_energy_X_power'],
            constant=t['proof_constant']) for t in result['targets'] if t['component_bound_proved']],
        actual_source_observations=0, fitted_constants=0, model_calls_in_search=0,
        main_operations=meter.operations, inclusive_operations=total,
        elapsed_seconds=time.monotonic()-started, peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        whole_signed_bound_proved=False, RH_proved=False)
    write(OUT/'report.json', report)
    publication = OUT/'publication-001'
    publication.mkdir()
    raw = (OUT/'next_search_input.json').read_bytes()
    for path in (publication/'next_search_input.json', ROOT/PUBLIC_INPUT):
        with path.open('xb') as f:
            f.write(raw)
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

"""Run the current missing bound through the frozen argument grammar once."""
import json
from pathlib import Path
import resource
import time

import core_bound_argument_search as P
import verify_core_signed_primitive_publication as PRIOR
from prime_bank_candidates import Meter

ROOT = Path(__file__).resolve().parent
INPUT = 'candidate10_signed_primitive_obligation.json'
PUBLIC_INPUT = 'candidate10_bound_argument_obligation.json'
PARENT = ROOT/'core-signed-primitive-results/pilot-001/verification-001'
OUT = ROOT/'core-bound-argument-results/pilot-001'
CAP, SECONDS, MEMORY = 1000000000, 900, 4*1024**3
RECEIPTS = ['core_bound_argument_search_development.json', 'core_bound_argument_checker_development.json']
FILES = ['core_bound_argument_search.py', 'check_core_bound_argument_search.py',
    'test_core_bound_argument_search.py', 'test_check_core_bound_argument_search.py',
    'run_core_bound_argument_search.py', 'core_bound_argument_search_protocol.txt',
    'CORE_RATIONAL_CONDUCTOR_BOUND_REVIEW_030.txt', 'prime_bank_candidates.py', INPUT]+RECEIPTS
read, write = PRIOR.read, PRIOR.write


def require_input():
    P.require((ROOT/INPUT).read_bytes() == (PARENT/'publication-001/next_search_input.json').read_bytes(),
              'exact preceding accepted publication including its saved interface correction')
    P.require(read(PARENT/'verification.json')['verified'], 'verified preceding signed-primitive result')


def verify():
    PRIOR.verify()
    require_input()
    for name in read(OUT/'source_files.json'):
        P.require((ROOT/name).read_bytes() == (OUT/'source_snapshot'/name).read_bytes(),
                  'unchanged frozen bound-argument source '+name)


def main():
    import check_core_bound_argument_search as C
    from run_core_bound_goal_search import validate_receipts
    started = time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, resource.getrlimit(resource.RLIMIT_AS)[1]))
    PRIOR.verify()
    require_input()
    development = validate_receipts([read(ROOT/name) for name in RECEIPTS])
    OUT.mkdir(parents=True, exist_ok=False)
    meter = Meter(CAP-development, SECONDS)
    try:
        (OUT/'source_snapshot').mkdir()
        for name in FILES:
            (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
        write(OUT/'source_files.json', FILES)
        write(OUT/'protocol.json', dict(schema='core-bound-argument-run-v1', input=INPUT, spec=P.SPEC,
            memory_limit_bytes=MEMORY, runtime_seconds=SECONDS, operation_cap=CAP,
            numerical_source_observations=0, runtime_model_calls=0, fitted_constants=0, hashes=False,
            whole_signed_bound_proved=False, RH_proved=False))
        meter.charge(2000000)
        parent = read(ROOT/INPUT)
        print('Searching arguments for the current missing bound and inferred auxiliaries.', flush=True)
        result = P.search(parent, meter)
        write(OUT/'proof_search.json', result)
        artifact = str(OUT.relative_to(ROOT))
        output = P.feedback(parent, result, artifact)
        print('Checking every proof step, open bridge, unsigned comparison and original source binding.', flush=True)
        checked = C.verify_feedback(parent, result, output, artifact, meter)
        P.require(checked['verified'], 'independent argument and full-feedback verification')
        write(OUT/'verification.json', checked)
        write(OUT/'next_search_input.json', output)
        verify()
        report = dict(status='BOUND_ARGUMENT_SEARCH_VERIFIED_WITH_OPEN_SIGNED_CORE',
            **result['statistics'], auxiliary_selection=result['auxiliary_selection'],
            supplied_rules='CORE_RATIONAL_CONDUCTOR_BOUND_REVIEW_030.txt',
            actual_source_argument_closed=result['trials'][0]['proof_search']['target_proved'],
            open_frontier=result['trials'][0]['proof_search']['frontier'],
            inherited_source_bindings=len(parent['generated_bound_obligations']),
            development_operations=development, study_operations=meter.operations,
            inclusive_operations=development+meter.operations, elapsed_seconds=time.monotonic()-started,
            main_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            whole_signed_bound_proved=False, RH_proved=False)
        write(OUT/'report.json', report)
        publication = OUT/'publication-001'
        publication.mkdir()
        raw = (OUT/'next_search_input.json').read_bytes()
        for path in (publication/'next_search_input.json', ROOT/PUBLIC_INPUT):
            with path.open('xb') as stream:
                stream.write(raw)
        write(OUT.parent/'latest.json', dict(input=PUBLIC_INPUT, status=report['status'],
            report=str((OUT/'report.json').relative_to(ROOT)), whole_signed_bound_proved=False, RH_proved=False))
        print(json.dumps({k: v for k, v in report.items() if k != 'open_frontier'}), flush=True)
    except Exception as error:
        write(OUT/'terminal_failure.json', dict(status='incomplete', error_type=type(error).__name__, error=str(error),
            operations=meter.operations, development_operations=development,
            whole_signed_bound_proved=False, RH_proved=False))
        raise


if __name__ == '__main__':
    main()

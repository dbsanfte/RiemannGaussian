"""One frozen signed primitive search, followed by an independent proof check."""
import json
from pathlib import Path
import resource
import time

import core_signed_primitive_search as P
import run_core_work_moment_proof_search as PRIOR
from prime_bank_candidates import Meter

ROOT = Path(__file__).resolve().parent
INPUT = 'candidate10_work_moment_proof_obligation.json'
PUBLIC_INPUT = 'candidate10_signed_primitive_obligation.json'
PARENT = ROOT/'core-work-moment-proof-results/pilot-001'
OUT = ROOT/'core-signed-primitive-results/pilot-001'
CAP, SECONDS, MEMORY = 1000000000, 900, 4*1024**3
RECEIPTS = ['core_signed_primitive_search_development.json', 'core_signed_primitive_checker_development.json']
FILES = ['core_signed_primitive_search.py', 'check_core_signed_primitive_search.py',
    'test_core_signed_primitive_search.py', 'test_check_core_signed_primitive_search.py',
    'run_core_signed_primitive_search.py', 'core_signed_primitive_search_protocol.txt',
    'CORE_SIGNED_PRIMITIVE_SEARCH_REVIEW_029.txt', 'core_work_moment_proof_search.py',
    'check_core_work_moment_proof_search.py', INPUT]+RECEIPTS
read, write = PRIOR.read, PRIOR.write


def require_input():
    P.require((ROOT/INPUT).read_bytes() == (PARENT/'publication-001/next_search_input.json').read_bytes(),
              'complete preceding publication')
    P.require(read(PARENT/'report.json')['status'] ==
        'UNIFORM_WORK_MOMENT_PROOF_ATTEMPTS_VERIFIED_WITH_OPEN_SIGNED_CORE', 'verified parent study')
    P.require(read(PARENT/'proof_verification.json')['verified'] and
        read(PARENT/'feedback_verification.json')['verified'], 'accepted reusable parent proof and source binding')


def verify():
    PRIOR.verify(); require_input()
    for name in read(OUT/'source_files.json'):
        P.require((ROOT/name).read_bytes() == (OUT/'source_snapshot'/name).read_bytes(), 'unchanged frozen source '+name)


def main():
    import check_core_signed_primitive_search as C
    from run_core_bound_goal_search import validate_receipts
    started = time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, resource.getrlimit(resource.RLIMIT_AS)[1]))
    PRIOR.verify(); require_input()
    development = validate_receipts([read(ROOT/name) for name in RECEIPTS])
    OUT.mkdir(parents=True, exist_ok=False)
    meter = Meter(CAP-development, SECONDS)
    try:
        (OUT/'source_snapshot').mkdir()
        for name in FILES:
            (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
        write(OUT/'source_files.json', FILES)
        write(OUT/'protocol.json', dict(schema='core-signed-primitive-run-v1', input=INPUT, spec=P.SPEC,
            memory_limit_bytes=MEMORY, runtime_seconds=SECONDS, total_operation_cap=CAP,
            actual_arithmetic_observations=0, numeric_cache_values_used=False, fitted_constants=0,
            runtime_model_calls=0, hashes=False, unchanged_development_suites_rerun=0,
            whole_signed_bound_proved=False, RH_proved=False))
        meter.charge(2000000)
        parent = read(ROOT/INPUT)
        print('Frozen signed primitive grammar; solving exact identities and affordable-bound constraints.', flush=True)
        result = P.search(parent, meter)
        write(OUT/'proof_search.json', result)
        artifact = str(OUT.relative_to(ROOT))
        output = P.feedback(parent, result, artifact)
        print('Independent replay of all feasible identities and infeasible dual certificates.', flush=True)
        checked = C.verify_feedback(parent, result, output, artifact, meter)
        P.require(checked['verified'], 'all identities, costs, dual witnesses and source feedback verified')
        write(OUT/'verification.json', checked)
        write(OUT/'next_search_input.json', output)
        verify()
        search = result['search']
        exact = search['unconstrained_signed_elimination']
        report = dict(status='SIGNED_PRIMITIVE_ARGUMENTS_VERIFIED_WITH_OPEN_SIGNED_CORE',
            **result['statistics'], best_common_signed_prefix_bound=search['certificate']['bound'],
            required=search['requested'], baseline=search['baseline'],
            observable='absolute value of complete cumulative signed integral; not grouped absolute work or Gram',
            selected_trial=search['selected_trial'],
            requested_trial=next(t for t in search['trials'] if t['threshold']==search['requested']),
            signed_primitive_endpoint=exact.get('certificate', {}).get('endpoint_bound'),
            signed_primitive_remainder=exact.get('certificate', {}).get('residual_bound'),
            original_energy_restatement=result['exact_primitive_is_original_energy_restatement'],
            inherited_source_bindings=len(parent['generated_bound_obligations']),
            development_operations=development, study_operations=meter.operations,
            inclusive_operations=development+meter.operations, elapsed_seconds=time.monotonic()-started,
            main_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            full_component_bound_proved=False, whole_signed_bound_proved=False, RH_proved=False)
        write(OUT/'report.json', report)
        publication = OUT/'publication-001'; publication.mkdir()
        raw = (OUT/'next_search_input.json').read_bytes()
        for path in (publication/'next_search_input.json', ROOT/PUBLIC_INPUT):
            with path.open('xb') as stream:
                stream.write(raw)
        write(OUT.parent/'latest.json', dict(input=PUBLIC_INPUT, status=report['status'],
            report=str((OUT/'report.json').relative_to(ROOT)), whole_signed_bound_proved=False, RH_proved=False))
        print(json.dumps(report), flush=True)
    except Exception as error:
        write(OUT/'terminal_failure.json', dict(status='incomplete', error_type=type(error).__name__, error=str(error),
            operations=meter.operations, development_operations=development,
            whole_signed_bound_proved=False, RH_proved=False))
        raise


if __name__ == '__main__':
    main()

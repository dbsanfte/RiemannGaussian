"""Verify a saved primitive search after a checker-meter interface repair."""
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
BASE = ROOT/'core-signed-primitive-results/pilot-001'
OUT = BASE/'verification-001'
CAP, SECONDS, MEMORY = 1000000000, 900, 4*1024**3
CORRECTED = ['check_core_signed_primitive_search.py', 'test_check_core_signed_primitive_search.py',
             'core_signed_primitive_checker_development.json']
RECEIPTS = ['core_signed_primitive_search_development.json', 'core_signed_primitive_checker_development.json']
FILES = CORRECTED+['core_signed_primitive_search.py', 'verify_core_signed_primitive_publication.py',
    'core_signed_primitive_verification_protocol.txt', 'core_signed_primitive_search_protocol.txt',
    'CORE_SIGNED_PRIMITIVE_SEARCH_REVIEW_029.txt', INPUT, RECEIPTS[0]]
read, write = PRIOR.read, PRIOR.write


def verify_base():
    PRIOR.verify()
    P.require((ROOT/INPUT).read_bytes() == (PARENT/'publication-001/next_search_input.json').read_bytes(),
              'unchanged verified parent input')
    P.require(read(PARENT/'proof_verification.json')['verified'] and read(PARENT/'feedback_verification.json')['verified'],
              'accepted parent proof and full source')
    failed = read(BASE/'terminal_failure.json')
    P.require(failed['error_type']=='AttributeError' and failed['error']=="'Meter' object has no attribute 'number'",
              'preserved specific interface failure, not an arithmetic rejection')
    names = read(BASE/'source_files.json')
    P.require(set(CORRECTED) <= set(names), 'declared checker-only interface corrections')
    for name in names:
        if name not in CORRECTED:
            P.require((ROOT/name).read_bytes() == (BASE/'source_snapshot'/name).read_bytes(),
                      'unchanged original producer, rules and source '+name)


def verify():
    verify_base()
    for name in read(OUT/'source_files.json'):
        P.require((ROOT/name).read_bytes() == (OUT/'source_snapshot'/name).read_bytes(), 'frozen corrected verifier '+name)
    P.require((OUT/'producer_proof_search.json').read_bytes() == (BASE/'proof_search.json').read_bytes(),
              'same producer result without search rerun')


def main():
    import check_core_signed_primitive_search as C
    from run_core_bound_goal_search import validate_receipts
    started = time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, resource.getrlimit(resource.RLIMIT_AS)[1]))
    verify_base()
    development = validate_receipts([read(ROOT/name) for name in RECEIPTS])
    failed_work = read(BASE/'terminal_failure.json')['operations']
    meter = Meter(CAP-development-failed_work, SECONDS)
    OUT.mkdir(parents=True, exist_ok=False)
    try:
        (OUT/'source_snapshot').mkdir()
        for name in FILES:
            (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
        write(OUT/'source_files.json', FILES)
        (OUT/'producer_proof_search.json').write_bytes((BASE/'proof_search.json').read_bytes())
        write(OUT/'protocol.json', dict(schema='core-signed-primitive-saved-verification-v1',
            original_study=str(BASE.relative_to(ROOT)), corrected_source_files=CORRECTED,
            producer_search_reruns=0, numeric_source_observations=0, fitted_constants=0, hashes=False,
            development_operations=development, failed_study_operations=failed_work,
            operation_cap=CAP, seconds=SECONDS, memory_bytes=MEMORY))
        meter.charge(2000000)
        parent = read(ROOT/INPUT)
        result = read(OUT/'producer_proof_search.json')
        artifact = str(OUT.relative_to(ROOT))
        output = P.feedback(parent, result, artifact)
        print('Verifying the saved primitive result; producer search is not repeated.', flush=True)
        checked = C.verify_feedback(parent, result, output, artifact, meter)
        P.require(checked['verified'], 'all source-bound identities, costs and dual witnesses accepted')
        write(OUT/'verification.json', checked)
        write(OUT/'next_search_input.json', output)
        verify()
        search = result['search']; exact = search['unconstrained_signed_elimination']
        report = dict(status='SIGNED_PRIMITIVE_ARGUMENTS_VERIFIED_WITH_OPEN_SIGNED_CORE',
            **result['statistics'], best_common_signed_prefix_bound=search['certificate']['bound'],
            required=search['requested'], baseline=search['baseline'], selected_trial=search['selected_trial'],
            observable='absolute value of complete cumulative signed integral; not grouped absolute work or Gram',
            requested_trial=next(t for t in search['trials'] if t['threshold']==search['requested']),
            signed_primitive_endpoint=exact.get('certificate', {}).get('endpoint_bound'),
            signed_primitive_remainder=exact.get('certificate', {}).get('residual_bound'),
            original_energy_restatement=result['exact_primitive_is_original_energy_restatement'],
            inherited_source_bindings=len(parent['generated_bound_obligations']),
            development_operations=development, failed_study_operations=failed_work,
            verification_operations=meter.operations, inclusive_operations=development+failed_work+meter.operations,
            verification_elapsed_seconds=time.monotonic()-started,
            main_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            interface_failure_preserved=True, producer_search_reruns=0,
            full_component_bound_proved=False, whole_signed_bound_proved=False, RH_proved=False)
        write(OUT/'report.json', report)
        publication = OUT/'publication-001'; publication.mkdir()
        raw = (OUT/'next_search_input.json').read_bytes()
        for path in (publication/'next_search_input.json', ROOT/PUBLIC_INPUT):
            with path.open('xb') as stream:
                stream.write(raw)
        write(BASE.parent/'latest.json', dict(input=PUBLIC_INPUT, status=report['status'],
            report=str((OUT/'report.json').relative_to(ROOT)), whole_signed_bound_proved=False, RH_proved=False))
        print(json.dumps(report), flush=True)
    except Exception as error:
        write(OUT/'terminal_failure.json', dict(status='incomplete', error_type=type(error).__name__, error=str(error),
            operations=meter.operations, development_operations=development, failed_study_operations=failed_work,
            whole_signed_bound_proved=False, RH_proved=False))
        raise


if __name__ == '__main__':
    main()

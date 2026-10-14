"""One immutable search of supplied moment regions and full-source transfers."""
import json
from pathlib import Path
import resource
import time

import core_moment_region_search as P
import run_core_complete_convolution_search as PRIOR
from prime_bank_candidates import Meter

ROOT = Path(__file__).resolve().parent
INPUT = 'candidate10_complete_convolution_obligation.json'
PUBLIC_INPUT = 'candidate10_moment_region_obligation.json'
CONTEXT = 'core-moment-bound-results/pilot-001/context.json'
PARENT = ROOT/'core-complete-convolution-results/pilot-001'
OUT = ROOT/'core-moment-region-results/pilot-001'
CAP, SECONDS, MEMORY = 1000000000, 1800, 16*1024**3
RECEIPTS = ['core_moment_region_development.json', 'core_moment_region_checker_development.json']
FILES = ['core_moment_region_search.py', 'check_core_moment_region_search.py',
    'test_core_moment_region_search.py', 'test_check_core_moment_region_search.py',
    'run_core_moment_region_search.py', 'core_moment_region_search_protocol.txt',
    'CORE_MOMENT_REGION_REVIEW_033.txt', 'CORE_MOMENT_REGION_CHECK_033.txt',
    'prime_bank_candidates.py', INPUT, CONTEXT]+RECEIPTS
read, write = PRIOR.read, PRIOR.write


def require_input():
    P.require((ROOT/INPUT).read_bytes() == (PARENT/'publication-001/next_search_input.json').read_bytes(),
              'exact preceding accepted complete-convolution input')
    P.require(read(PARENT/'verification.json')['verified'], 'verified preceding study')


def verify():
    PRIOR.verify()
    require_input()
    for name in read(OUT/'source_files.json'):
        P.require((ROOT/name).read_bytes() == (OUT/'source_snapshot'/name).read_bytes(),
                  'unchanged frozen moment-region source '+name)


def main():
    import check_core_moment_region_search as C
    from run_core_bound_goal_search import validate_receipts
    started = time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, resource.getrlimit(resource.RLIMIT_AS)[1]))
    PRIOR.verify()
    require_input()
    receipts = [read(ROOT/name) for name in RECEIPTS]
    development = validate_receipts(receipts)
    P.require(all(r['edits_stopped'] for r in receipts), 'finalized new development sources')
    OUT.mkdir(parents=True, exist_ok=False)
    meter = Meter(CAP-development, SECONDS)
    try:
        for name in FILES:
            path = OUT/'source_snapshot'/name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((ROOT/name).read_bytes())
        write(OUT/'source_files.json', FILES)
        write(OUT/'protocol.json', dict(schema='core-moment-region-run-v1', input=INPUT, spec=P.DEFAULT_SPEC,
            memory_limit_bytes=MEMORY, runtime_seconds=SECONDS, operation_cap=CAP,
            actual_source_observations=0, runtime_model_calls=0, fitted_constants=0, hashes=False,
            supplied_rules=['CORE_MOMENT_REGION_REVIEW_033.txt', 'CORE_MOMENT_REGION_CHECK_033.txt'],
            whole_signed_bound_proved=False, RH_proved=False))
        meter.charge(2000000)
        parent, context = read(ROOT/INPUT), read(ROOT/CONTEXT)
        print('Searching every inherited pure residual target over the supplied moment regions and rational contours.', flush=True)
        result = P.search(parent, context, P.DEFAULT_SPEC, meter)
        write(OUT/'proof_search.json', result)
        print('Independently verifying moment certificates, analytic centering, source recovery and complete cube composition.', flush=True)
        checked = C.verify_search(parent, context, result, meter)
        P.require(checked['verified'], 'independent proof search verification')
        artifact = str(OUT.relative_to(ROOT))
        output = P.feedback(parent, result, artifact)
        feedback_check = C.verify_feedback(parent, result, output, artifact, meter)
        P.require(feedback_check['verified'], 'independent feedback verification')
        write(OUT/'verification.json', dict(verified=True, search=checked, feedback=feedback_check))
        write(OUT/'next_search_input.json', output)
        verify()
        selected = [dict(target_id=t['target_id'], newly_paid=t['new_source_payment'],
            sigma=t['trials'][t['selected']]['sigma'],
            energy_N_power=t['trials'][t['selected']]['recovered_energy_N_power'],
            U_power=t['trials'][t['selected']]['full_finite_factor_U_power'])
            for t in result['targets'] if t['selected'] is not None]
        report = dict(status='MOMENT_REGION_SEARCH_VERIFIED_WITH_OPEN_SIGNED_CORE', **result['statistics'],
            paid_components=selected, finite_cube_bound_proved=result['cube_composition']['finite_cube_bound_proved'],
            full_component_bound_proved=result['cube_composition']['complete_component_bound_proved'],
            original_fixed_sigma_low_Gram_proved=False,
            future_targets_requiring_more_than_moment_library=sum(t['optimistic_moment_diagnostic']['stronger_moment_library_alone_insufficient']
                for t in result['targets'] if not t['analytic_centered_bound_proved']),
            arithmetic_power_advantage=False, development_operations=development,
            study_operations=meter.operations, inclusive_operations=development+meter.operations,
            elapsed_seconds=time.monotonic()-started,
            main_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            formal_proof_assistant_verified=False, whole_signed_bound_proved=False, RH_proved=False)
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

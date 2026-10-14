"""Frozen, source-bound attempts at the pending uniform work-moment goals."""
import json
from pathlib import Path
import resource
import time

import core_work_moment_proof_search as P
import run_core_cutoff_prefix_projections as PRIOR
from prime_bank_candidates import Meter

ROOT = Path(__file__).resolve().parent
INPUT = 'candidate10_cutoff_prefix_projection_obligation.json'
PUBLIC_INPUT = 'candidate10_work_moment_proof_obligation.json'
PARENT = ROOT/'core-cutoff-prefix-projection-results/pilot-001'
OUT = ROOT/'core-work-moment-proof-results/pilot-001'
CAP, SECONDS, MEMORY = 4000000000, 1800, 4*1024**3
RECEIPTS = ['core_work_moment_proof_search_development.json', 'core_work_moment_proof_search_checker_development.json']
FILES = ['core_work_moment_proof_search.py', 'check_core_work_moment_proof_search.py',
    'test_core_work_moment_proof_search.py', 'test_check_core_work_moment_proof_search.py',
    'run_core_work_moment_proof_search.py', 'core_work_moment_proof_search_protocol.txt',
    'CORE_WORK_MOMENT_PROOF_RULE_REVIEW_028.txt', 'CORE_CUTOFF_PREFIX_PROJECTION_REVIEW_027.txt',
    'core_moment_bound_search.py', 'check_core_moment_bound_search.py', 'prime_bank_candidates.py', INPUT]+RECEIPTS
read, write = PRIOR.read, PRIOR.write


def require_input():
    P.require((ROOT/INPUT).read_bytes() == (PARENT/'publication-001/next_search_input.json').read_bytes(),
              'exact preceding publication with all252 pending moment bounds')
    P.require(read(PARENT/'report.json')['status'] ==
        'PREFIX_PROJECTIONS_AND_CONDITIONAL_GRAM_ROUTES_VERIFIED_WITH_OPEN_SIGNED_CORE',
        'verified preceding projection experiment')


def verify():
    PRIOR.verify(); require_input()
    for name in read(OUT/'source_files.json'):
        P.require((ROOT/name).read_bytes() == (OUT/'source_snapshot'/name).read_bytes(),
                  'unchanged frozen moment proof source '+name)


def main():
    import check_core_work_moment_proof_search as C
    from run_core_bound_goal_search import validate_receipts
    started = time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, resource.getrlimit(resource.RLIMIT_AS)[1]))
    PRIOR.verify(); require_input()
    development = validate_receipts([read(ROOT/name) for name in RECEIPTS])
    OUT.mkdir(parents=True, exist_ok=False)
    meter = Meter(CAP-development, SECONDS)
    try:
        (OUT/'source_snapshot').mkdir()
        for name in FILES: (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
        write(OUT/'source_files.json', FILES)
        write(OUT/'protocol.json', dict(schema='core-work-moment-proof-run-v1', input=INPUT, spec=P.DEFAULT_SPEC,
            memory_limit_bytes=MEMORY, runtime_seconds=SECONDS, total_operation_cap=CAP,
            actual_arithmetic_observations=0, numeric_cache_values_used=False, fitted_constants=0,
            runtime_model_calls=0, hashes=False, unchanged_development_suites_rerun=0,
            whole_signed_bound_proved=False, RH_proved=False))
        meter.charge(2000000)
        parent = read(ROOT/INPUT)
        print('Frozen proof grammar; attempting the actual uniform work-moment obligations.', flush=True)
        result = P.search(parent, P.DEFAULT_SPEC, meter)
        write(OUT/'proof_search.json', result)
        print('Proof attempts generated. Independently replaying every source, moment, cost and target comparison.', flush=True)
        artifact = str(OUT.relative_to(ROOT))
        output = P.feedback(parent, result, artifact)
        # This entry point includes verify_search, then checks the full feedback.
        # Repeating verify_search separately would recompute the same proof twice.
        feedback_check = C.verify_feedback(parent, result, output, artifact, meter)
        P.require(feedback_check['verified'], 'source-bound attempted estimates and complete feedback')
        write(OUT/'proof_verification.json', dict(verified=True,
            verifier='check_core_work_moment_proof_search.verify_feedback includes full verify_search',
            requested_Gram_bounds=result['statistics']['requested_Gram_bounds'],
            requested_Gram_bounds_proved=result['statistics']['requested_Gram_bounds_proved'],
            direct_grouped_bound=result['direct_attempts'][result['selected_direct']]['bound'],
            whole_signed_bound_proved=False, RH_proved=False))
        write(OUT/'feedback_verification.json', feedback_check)
        write(OUT/'next_search_input.json', output)
        verify()
        summaries = []
        for item in result['Gram_attempt_classes']:
            selected = item['candidates'][item['selected']]
            floor = min((a['coefficient_cost_floor'] for a in item['candidates']), key=P.cost)
            summaries.append(dict(id=item['id'], label_weight=item['label_weight'], selected=item['selected'],
                representation=selected['representation'], method=selected['method'], event_weight=selected['event_weight'],
                established=selected['bound'], best_coefficient_cost_floor=floor))
        report = dict(status='UNIFORM_WORK_MOMENT_PROOF_ATTEMPTS_VERIFIED_WITH_OPEN_SIGNED_CORE',
            **result['statistics'], best_direct=result['direct_attempts'][result['selected_direct']],
            Gram_proof_classes=summaries, inherited_source_bindings=len(parent['generated_bound_obligations']),
            actual_arithmetic_observations=0, numeric_cache_values_used=False, fitted_constants=0, runtime_model_calls=0,
            development_operations=development, study_operations=meter.operations,
            inclusive_operations=development+meter.operations, elapsed_seconds=time.monotonic()-started,
            main_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            full_component_bound_proved=False, whole_signed_bound_proved=False, RH_proved=False)
        write(OUT/'report.json', report)
        publication = OUT/'publication-001'; publication.mkdir()
        raw = (OUT/'next_search_input.json').read_bytes()
        for path in (publication/'next_search_input.json', ROOT/PUBLIC_INPUT):
            with path.open('xb') as stream: stream.write(raw)
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

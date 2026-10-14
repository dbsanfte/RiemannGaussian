"""Search the current source's convolution arguments once, then verify."""
import json
from pathlib import Path
import resource
import time

import core_convolution_argument_search as P
import run_core_bound_argument_search as PRIOR
from prime_bank_candidates import Meter

ROOT = Path(__file__).resolve().parent
INPUT = 'candidate10_bound_argument_obligation.json'
PUBLIC_INPUT = 'candidate10_convolution_argument_obligation.json'
PARENT = ROOT/'core-bound-argument-results/pilot-001'
OUT = ROOT/'core-convolution-argument-results/pilot-001'
CAP, SECONDS, MEMORY = 1000000000, 900, 4*1024**3
RECEIPTS = ['core_convolution_argument_search_development.json', 'core_convolution_argument_checker_development.json']
FILES = ['core_convolution_argument_search.py', 'check_core_convolution_argument_search.py',
    'test_core_convolution_argument_search.py', 'test_check_core_convolution_argument_search.py',
    'run_core_convolution_argument_search.py', 'core_convolution_argument_search_protocol.txt',
    'CORE_DILATION_COVARIANCE_REVIEW_031.txt', 'prime_bank_candidates.py', INPUT]+RECEIPTS
read, write = PRIOR.read, PRIOR.write


def require_input():
    P.require((ROOT/INPUT).read_bytes() == (PARENT/'publication-001/next_search_input.json').read_bytes(),
              'exact preceding accepted argument-search input')
    P.require(read(PARENT/'verification.json')['verified'], 'verified preceding argument study')


def verify():
    PRIOR.verify()
    require_input()
    for name in read(OUT/'source_files.json'):
        P.require((ROOT/name).read_bytes() == (OUT/'source_snapshot'/name).read_bytes(),
                  'unchanged frozen convolution-argument source '+name)


def main():
    import check_core_convolution_argument_search as C
    from run_core_bound_goal_search import validate_receipts
    started = time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, resource.getrlimit(resource.RLIMIT_AS)[1]))
    PRIOR.verify()
    require_input()
    receipts = [read(ROOT/name) for name in RECEIPTS]
    development = validate_receipts(receipts)
    P.require(all(r['edits_stopped'] for r in receipts), 'development sources finalized before freezing')
    OUT.mkdir(parents=True, exist_ok=False)
    meter = Meter(CAP-development, SECONDS)
    try:
        (OUT/'source_snapshot').mkdir()
        for name in FILES:
            (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
        write(OUT/'source_files.json', FILES)
        write(OUT/'protocol.json', dict(schema='core-convolution-argument-run-v1', input=INPUT,
            geometry_grammar=P.GEOMETRY_GRAMMAR, geometry_count=len(P.GEOMETRIES),
            memory_limit_bytes=MEMORY, runtime_seconds=SECONDS, operation_cap=CAP,
            numerical_source_observations=0, runtime_model_calls=0, fitted_constants=0, hashes=False,
            supplied_rules='CORE_DILATION_COVARIANCE_REVIEW_031.txt',
            whole_signed_bound_proved=False, RH_proved=False))
        meter.charge(2000000)
        parent = read(ROOT/INPUT)
        print('Solving floor identities, divisor arguments and the generated rational cutoff grammar.', flush=True)
        result = P.search(parent, meter)
        write(OUT/'proof_search.json', result)
        artifact = str(OUT.relative_to(ROOT))
        output = P.feedback(parent, result, artifact)
        print('Verifying every linear certificate, cost and complete inherited source.', flush=True)
        checked = C.verify_feedback(parent, result, output, artifact, meter)
        P.require(checked['verified'], 'independent convolution argument and feedback verification')
        write(OUT/'verification.json', checked)
        write(OUT/'next_search_input.json', output)
        verify()
        selected = result['selected_geometry']
        geometry = result['geometries'][selected]
        report = dict(status='CONVOLUTION_ARGUMENT_SEARCH_VERIFIED_WITH_OPEN_SIGNED_CORE',
            **result['statistics'], selected_geometry=selected,
            selected_cutoffs=dict(alpha=geometry['alpha'], beta=geometry['beta']),
            selected_one_e_coefficient=geometry['one_e_coefficient'], selected_finite_head=geometry['finite_head'],
            selected_spacing_cost=result['geometry_costs'][selected],
            auxiliary_period_bound=result['divisor_proofs'][0]['period_bound'],
            bounded_weight_comparison=result['divisor_proofs'][1]['period_bound'],
            period_obstruction=result['period_obstruction'], missing=result['missing'],
            inherited_source_bindings=len(parent['generated_bound_obligations']),
            development_operations=development, study_operations=meter.operations,
            inclusive_operations=development+meter.operations, elapsed_seconds=time.monotonic()-started,
            main_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            formal_proof_assistant_verified=False, whole_signed_bound_proved=False, RH_proved=False)
        write(OUT/'report.json', report)
        publication = OUT/'publication-001'
        publication.mkdir()
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

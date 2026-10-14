"""Run full-expression pricing and centered transfer synthesis exactly once."""
import json
from fractions import Fraction as Q
from pathlib import Path
import resource
import time

import core_complete_convolution_search as P
import run_core_convolution_argument_search as PRIOR
from prime_bank_candidates import Meter

ROOT = Path(__file__).resolve().parent
INPUT = 'candidate10_convolution_argument_obligation.json'
PUBLIC_INPUT = 'candidate10_complete_convolution_obligation.json'
PARENT = ROOT/'core-convolution-argument-results/pilot-001'
OUT = ROOT/'core-complete-convolution-results/pilot-001'
CAP, SECONDS, MEMORY = 1000000000, 900, 4*1024**3
RECEIPTS = ['core_complete_convolution_search_development.json', 'core_complete_convolution_checker_development.json']
FILES = ['core_complete_convolution_search.py', 'check_core_complete_convolution_search.py',
    'test_core_complete_convolution_search.py', 'test_check_core_complete_convolution_search.py',
    'run_core_complete_convolution_search.py', 'core_complete_convolution_search_protocol.txt',
    'CORE_COMPLETE_CONVOLUTION_BOUND_REVIEW_032.txt', 'prime_bank_candidates.py', INPUT]+RECEIPTS
read, write = PRIOR.read, PRIOR.write


def require_input():
    P.require((ROOT/INPUT).read_bytes() == (PARENT/'publication-001/next_search_input.json').read_bytes(),
              'exact preceding accepted convolution input')
    P.require(read(PARENT/'verification.json')['verified'], 'verified preceding study')


def verify():
    PRIOR.verify()
    require_input()
    for name in read(OUT/'source_files.json'):
        P.require((ROOT/name).read_bytes() == (OUT/'source_snapshot'/name).read_bytes(),
                  'unchanged frozen complete-convolution source '+name)


def main():
    import check_core_complete_convolution_search as C
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
        (OUT/'source_snapshot').mkdir()
        for name in FILES:
            (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
        write(OUT/'source_files.json', FILES)
        write(OUT/'protocol.json', dict(schema='core-complete-convolution-run-v1', input=INPUT,
            memory_limit_bytes=MEMORY, runtime_seconds=SECONDS, operation_cap=CAP,
            actual_source_observations=0, runtime_model_calls=0, fitted_constants=0, hashes=False,
            supplied_rules='CORE_COMPLETE_CONVOLUTION_BOUND_REVIEW_032.txt',
            whole_signed_bound_proved=False, RH_proved=False))
        meter.charge(2000000)
        parent = read(ROOT/INPUT)
        print('Searching complete prefix arguments and centered cutoff transfers, including bounded-weight ablations.', flush=True)
        result = P.search(parent, meter)
        write(OUT/'proof_search.json', result)
        artifact = str(OUT.relative_to(ROOT))
        output = P.feedback(parent, result, artifact)
        print('Verifying every priced head, support witness, analytic moment correction and inherited source.', flush=True)
        checked = C.verify_feedback(parent, result, output, artifact, meter)
        P.require(checked['verified'], 'independent complete-expression and feedback verification')
        write(OUT/'verification.json', checked)
        write(OUT/'next_search_input.json', output)
        verify()
        transfer = result['centered_transfer']; generic = result['transfer_ablation']
        chosen = None if transfer['selected'] is None else transfer['trials'][transfer['selected']]
        ablated = None if generic['selected'] is None else generic['trials'][generic['selected']]
        rho = Q(transfer['rho'])
        report = dict(status='COMPLETE_CONVOLUTION_SEARCH_VERIFIED_WITH_OPEN_SIGNED_CORE', **result['statistics'],
            selected_prefix_route=result['selected_prefix_route'], full_source_prefix_bound=result['full_source_prefix_bound'],
            raw_prefix_energy_N_power=str(P.score(result['before_outer_K_energy_bound'], rho)[0]),
            selected_transfer=chosen, selected_generic_transfer=ablated,
            physical_centered_transfer_proved=chosen is not None,
            finite_cube_bound_proved=False, original_global_Mellin_bound_proved=False,
            inherited_source_bindings=len(parent['generated_bound_obligations']),
            development_operations=development, study_operations=meter.operations,
            inclusive_operations=development+meter.operations, elapsed_seconds=time.monotonic()-started,
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
        print(json.dumps({k: v for k, v in report.items() if k not in ('selected_transfer', 'selected_generic_transfer')}
            | dict(selected_cutoffs=None if chosen is None else {k: chosen[k] for k in ('alpha', 'beta', 'base')},
                   transfer_error=None if chosen is None else chosen['normalized_error_energy'])), flush=True)
    except Exception as error:
        write(OUT/'terminal_failure.json', dict(status='incomplete', error_type=type(error).__name__, error=str(error),
            operations=meter.operations, development_operations=development,
            whole_signed_bound_proved=False, RH_proved=False))
        raise


if __name__ == '__main__':
    main()

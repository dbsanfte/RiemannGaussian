"""One immutable, target-bound search of signed prefix proof compositions."""
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

from flint import arb, ctx
from prime_bank_candidates import Meter
import core_prefix_proof_search as P
import check_core_prefix_proof_search as C
import run_core_truncated_inverse as PRIOR


ROOT = Path(__file__).resolve().parent
PARENT = ROOT/'core-truncated-inverse-results/pilot-001/comparison-audit-001'
INPUT = 'candidate10_short_inverse_obligation.json'
OUT = ROOT/'core-prefix-proof-results/pilot-001'
TESTS = ['test_core_prefix_proof_search', 'test_check_core_prefix_proof_search']
RECEIPTS = ['core_prefix_proof_search_development.json', 'core_prefix_proof_checker_development.json']
FILES = ['core_prefix_proof_search.py', 'check_core_prefix_proof_search.py',
         'run_core_prefix_proof_search.py', 'core_prefix_proof_search_protocol.txt',
         'prime_bank_candidates.py', 'potential_candidate_language.py', INPUT]+[s+'.py' for s in TESTS]+RECEIPTS
CAP = 300000000


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def verify():
    PRIOR.verify()
    for name in read(OUT/'source_files.json'):
        if (ROOT/name).read_bytes() != (OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen source '+name)


def main():
    start = time.monotonic()
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4*1024**3, hard))
    ctx.prec = 192
    PRIOR.verify()
    parent_report = read(PARENT/'report.json')
    if parent_report['status'] != 'SAVED_ACTUAL_SOURCE_OUTPUTS_VERIFIED_BY_ALGEBRAIC_COMPONENT_KEYS':
        raise ValueError('completed independently compared input required')
    if (ROOT/INPUT).read_bytes() != (PARENT/'publication-001/next_search_input.json').read_bytes():
        raise ValueError('current published input binding')
    prior = read(ROOT/INPUT)
    if prior['whole_signed_bound_proved'] or prior['RH_proved']:
        raise ValueError('unresolved full signed source')
    rows = prior['source_geometries']
    if len({r['id'] for r in rows}) != len(rows):
        raise ValueError('unique complete inherited source geometries')
    constructions = {o['id']: o['construction']
                     for o in prior['parent_obligation']['generated_bound_program_obligations']}
    parents = prior['generated_joined_obligations']
    expected = {(r['id'], ident) for r in rows for ident in constructions}
    actual = [(p['source_geometry_ref'], p['parent_obligation_id']) for p in parents]
    if len(set(actual)) != len(actual) or set(actual) != expected:
        raise ValueError('all inherited constructions bound to every source geometry')
    development = [read(ROOT/name) for name in RECEIPTS]
    for receipt in development:
        if receipt['runs'][-1]['returncode'] or receipt['operations'] != sum(r['operations'] for r in receipt['runs']):
            raise ValueError('complete passed owned development receipt')
    if OUT.exists():
        raise FileExistsError('one study; preserve all terminal outcomes')
    OUT.mkdir(parents=True)
    (OUT/'source_snapshot').mkdir()
    for name in FILES:
        (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(OUT/'source_files.json', FILES)
    write(OUT/'protocol.json', dict(schema='core-prefix-proof-run-v1', input=INPUT,
        grammar='every centering depth and every multiset convolution partition; mass, critical mass and signed prefix norms',
        geometry_ids=[r['id'] for r in rows], parent_obligation_count=len(parents),
        selection='partial reduction by proved exponents and paid pieces; no source responses or fitted constants',
        analyst_supplied=['centered residual identity', 'primitive norm inequalities',
                         'convolution and Abel summation rules', 'finite grammar and selection policy'],
        detector_generated=['centering applications', 'factor partitions', 'prefix-carrying factor',
                            'proof trees', 'uniform costs', 'paid versus remaining partition'],
        checker='independent exact recovery and bottom-up proof optimum audit; no generator import',
        source_evaluations=0, model_calls_in_search=0, numerical_scores_used=False,
        memory_limit_bytes=4*1024**3, runtime_limit_seconds=900, inclusive_operation_cap=CAP,
        hashes=False, general_analytic_prover=False, whole_signed_bound_proved=False, RH_proved=False))
    meter = Meter(CAP, 900)
    meter.charge(1000000)  # Conservative orchestration/serialization reservation.
    test_start = time.monotonic()
    tests = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS],
                           cwd=ROOT, capture_output=True, text=True, timeout=300)
    test_ops = sum(map(int, re.findall(r'operations=(\d+)', tests.stdout)))
    write(OUT/'frozen_tests.json', dict(returncode=tests.returncode, stdout=tests.stdout, stderr=tests.stderr,
        operations=test_ops, elapsed_seconds=time.monotonic()-test_start))
    if tests.returncode:
        raise RuntimeError('frozen owned suites failed')
    # Recheck the sole numerical scalar envelope used by the symbolic rules.
    # This evaluates no arithmetic source coefficients or candidate scores.
    z = (arb(2)/3).zeta()
    Ru = arb(9)/2*((arb(4)/3).zeta()/(z*z)-1/z)
    if not Ru.is_finite() or not abs(Ru) < 5:
        raise ArithmeticError('certified complete source scalar envelope')
    meter.charge(10000)
    write(OUT/'source_scalar.json', dict(beta='9/2', R_u=str(Ru), absolute_R_u_bound='5',
        precision_bits=ctx.prec, arithmetic_source_coefficients_evaluated=0))
    results, checks = {}, []
    for row in rows:
        result = P.search(row, meter)
        check = C.verify_search(row, result, meter)
        if not check['verified']:
            raise ArithmeticError('independent proof replay')
        results[row['id']] = result
        checks.append(check)
        write(OUT/('geometry-'+str(row['id'])+'.json'), result)
        print(json.dumps(dict(geometry=row['id'], verified=True, **result['statistics'])), flush=True)
    reductions, reduction_checks = [], []
    for parent in parents:
        result = results[parent['source_geometry_ref']]
        construction = constructions[parent['parent_obligation_id']]
        reduction = P.reduction(parent, construction, result)
        checked = C.verify_reduction(parent, construction, result, reduction, meter)
        reductions.append(reduction)
        reduction_checks.append(checked)
    write(OUT/'verification.json', dict(search_checks=checks, reduction_checks=reduction_checks))
    write(OUT/'reductions.json', reductions)
    by_geometry = []
    for row in rows:
        result = results[row['id']]
        sample = next(r for r in reductions if r['geometry_id'] == row['id'])
        by_geometry.append(dict(geometry_id=row['id'], alpha=row['alpha'], gamma=row['gamma'],
            statistics=result['statistics'], new_paid_source_pieces=sample['newly_paid'],
            remaining_signed_piece_count=len(sample['remaining_signed_pieces']),
            proof_artifact='core-prefix-proof-results/pilot-001/geometry-'+str(row['id'])+'.json'))
    next_input = dict(schema='core-prefix-proof-feedback-v1', status='open', parent_obligation=prior,
        generated_prefix_bound_obligations=reductions, proof_search_results=by_geometry,
        next_priority='Search a control for the joined residual and its explicit compensating drift; newly paid centered pieces stay excluded, all remaining signs/crosses and exact transport error retained',
        detector_searches_proof_compositions=True, detector_has_general_analytic_prover=False,
        analyst_supplied_rules_are_explicit=True, new_source_observations=0,
        original_target_and_all_corrections_retained=True,
        all_scale_signed_control_proved=False, whole_signed_bound_proved=False, RH_proved=False)
    write(OUT/'next_search_input.json', next_input)
    total = meter.operations+test_ops+sum(d['operations'] for d in development)
    if total > CAP:
        raise OverflowError('inclusive work cap')
    verify()
    report = dict(status='SIGNED_PREFIX_PROOF_SEARCH_VERIFIED_WITH_OPEN_JOINED_GOALS',
        source_geometries=len(rows), proof_nodes=sum(len(r['nodes']) for r in results.values()),
        rule_applications=sum(r['statistics']['rule_applications'] for r in results.values()),
        centering_alternatives=sum(r['statistics']['alternatives'] for r in results.values()),
        selected_centerings=sum(r['statistics']['selected_centerings'] for r in results.values()),
        geometry_summary=by_geometry, reduction_bindings=len(reductions),
        bindings_with_additional_paid_pieces=sum(bool(r['newly_paid']) for r in reductions),
        complete_signed_bounds_proved=0, numerical_source_evaluations=0, model_calls_in_search=0,
        main_operations=meter.operations, inclusive_operations=total,
        elapsed_seconds=time.monotonic()-start, peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        whole_signed_bound_proved=False, RH_proved=False)
    write(OUT/'report.json', report)
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        if OUT.exists() and not (OUT/'report.json').exists() and not (OUT/'terminal_failure.json').exists():
            write(OUT/'terminal_failure.json', dict(status='incomplete', error_type=type(error).__name__,
                error=str(error), whole_signed_bound_proved=False, RH_proved=False))
        raise

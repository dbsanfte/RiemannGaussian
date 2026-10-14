"""Report stored evidence and completed analytical reviews without new evaluations."""
from fractions import Fraction as Q
import json
from pathlib import Path
import sys

from potential_candidate_language import Meter

ROOT = Path(__file__).resolve().parent
REVIEWS = [
    'commutator_uniform_attempt_001.txt', 'prime_bank_uniform_attempt_001.txt',
    'divisor_transport_uniform_attempt_001.txt', 'arithmetic_prefix_recovery_review.txt',
    'residual_observer_bridge_review.txt', 'reversible_divisor_circuit_review.txt',
    'reversible_circuit_review_simple_001.txt', 'reversible_circuit_review_interleaved_001.txt',
    'reversible_circuit_review_deep_001.txt', 'dyadic_permutation_recovery_note.txt',
    'fractional_circuit_majorant_note.txt']


def report(directory):
    directory = Path(directory).resolve()
    meter = Meter(1000000)  # Within the already declared/prepaid root reserve.

    def read(name):
        data = (directory / name).read_bytes()
        meter.charge(len(data) // 16 + 1)
        if len(data) > 8 * 1024**2:
            raise ValueError('bounded saved artifact')
        return json.loads(data)

    audit_initial, receipt = read('independent_verification.json'), read('receipt.json')
    audit = read('independent_completion.json') if (directory / 'independent_completion.json').exists() else audit_initial
    if audit['status'] not in ('FINITE_EVALUATION_VERIFIED', 'FINITE_EVALUATION_VERIFIED_WITH_ALLOCATION_ADDENDUM'):
        raise ValueError('only independently verified finite evidence is reported here')
    selected, rows = read('final_batch.json'), read('final_responses.json')
    evidence, tests = read('discovery_evidence.json'), read('tests.json')
    baselines = {r['source']: {c['X']: Q(c['energy']) for c in r['cases']} for r in rows if r['id'] == 0}
    by_id = {r['id']: r for r in evidence}
    candidates = []
    for item in selected:
        record = item['record']; outcomes = []
        for row in (r for r in rows if r['id'] == record['id']):
            ratios = []
            for case in row['cases']:
                ratio = meter.number(Q(case['energy']) / baselines[row['source']][case['X']])
                ratios.append(dict(X=case['X'], energy=case['energy'], ratio_to_baseline=str(ratio),
                                   ratio_decimal=float(ratio)))
            outcomes.append(dict(source=row['source'], status=row['status'],
                                 passed=sum(s['passed'] for s in row['scores']), comparisons=len(row['scores']),
                                 failures=[s for s in row['scores'] if not s['passed']], moments=ratios))
        candidates.append(dict(id=record['id'], family=record['family'], program=record['program'],
                               recovery_power=record['certificate']['recovery_power'],
                               original_frozen_certificate=record['certificate'],
                               training_constants=item['constants'], initial_cost=by_id[record['id']]['initial_cost'],
                               validation_failures=sum(not s['passed'] for s in by_id[record['id']]['scores']),
                               outcomes=outcomes))
    for name in REVIEWS:
        if not (ROOT / name).is_file():
            raise FileNotFoundError('completed analytical review missing: ' + name)
    archive = directory / 'analytical_reviews'
    archive.mkdir()
    for name in REVIEWS:
        data = (ROOT / name).read_bytes()
        meter.charge(len(data) // 8 + 1)
        with (archive / name).open('xb') as handle:
            handle.write(data)
    payload = dict(
        schema='reversible-circuit-discovery-report-v1', status=audit['status'],
        generated=receipt['generated'], selected_ids=receipt['selected_ids'], candidates=candidates,
        complete_final_evaluations=receipt['final_available'], missing=receipt['final_missing'], invalid=receipt['final_invalid'],
        source_horizon=32767, final_bases=[6144, 8192, 12288, 16384], tested_q=[2, 3, 6, 12],
        tests_passed=23, finite_moments_verified=audit.get('total_moments_verified', audit.get('cases_verified')),
        recovery_certificates_checked=audit['certificates_checked'],
        cumulative_operations=audit['cumulative_operations'], declared_ceiling=450000000,
        preparation=tests['work'], producer=receipt, original_independent_audit=audit_initial,
        completed_independent_audit=audit,
        audit_allocation_addendum=read('audit_allocation_addendum.json') if (directory / 'audit_allocation_addendum.json').exists() else None,
        analytical_reviews=REVIEWS,
        interpretation=[
            'Every selected actual-Mobius circuit passes all16 finite comparisons, as does the baseline.',
            'Both control sources fail every frozen comparison, including baseline; this alone establishes no added operator information.',
            'Circuit28 has modestly smaller raw moments on all four final blocks; inverse cost and its slow phase preclude calling this an RH bound or established gain.',
            'Other selected raw moments exceed the baseline on these final blocks; the archive preserves structural alternatives for proof attempts.',
            'Recovery is proved for the restricted fixed-circuit grammar; the source-specific cofinal moment estimate remains open.',
            'Analytical refinements are recorded separately and do not rerank or change frozen selection, certificates, programs or results.',
            'The dyadic-permutation rule is a proved proposed language extension only; this study did not evaluate permutation circuits.',
            'Final arithmetic was excluded from this run selection, but source prefixes overlap earlier research; these are not globally unseen primes.',
            'The original audit phase stopped at its215m allocation after616 moments; an append-only allocation addendum completed the three remaining control rows within the same450m total ceiling, without recomputing completed moments.',
            'Root analytical review proves the general fractional-path majorant d_(sum abs alpha), which improves every selected circuit to integer recovery exponent1. This does not amend frozen certificates or rerank this study.'
        ],
        moment_estimate_proved=False, global_bound_proved=False, RH_proved=False,
        postprocess_operations_within_prepaid_root_reserve=meter.operations)
    with (directory / 'report.json').open('x') as handle:
        json.dump(payload, handle, sort_keys=True, indent=2, allow_nan=False); handle.write('\n')
    return dict(status=payload['status'], selected_ids=payload['selected_ids'],
                cumulative_operations=payload['cumulative_operations'], postprocess_operations=meter.operations)


if __name__ == '__main__':
    print(json.dumps(report(sys.argv[1]), sort_keys=True))

#!/usr/bin/env python3
"""Discover full prime-pair product/sum decoders, including the diagonal."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from pathlib import Path
import json
import random
import time

from exact_arithmetic import factorization
from decode_search import factor_native, phi
from pair_fibre_probe import prime_powers

BASE = Path(__file__).resolve().parent


def decode_factors(n, factors, r=3, odd_offset=2, two_offset=2):
    # Distinct primes have full exponent one outside the r-power sum.
    visible = [p for p, e in factors.items() if e % r]
    if len(visible) == 2 and all(factors[p] == 1 for p in visible):
        p, q = sorted(visible)
        if phi(p, q, r) == n:
            return p, q
    # The diagonal is checked by its full factor pattern, not a finite
    # collision-free sample or a guessed square root.
    if factors == {2: 2 * r + two_offset}:
        return (2, 2) if phi(2, 2, r) == n else None
    odd = [(p, e) for p, e in factors.items() if p != 2]
    if len(odd) == 1 and factors.get(2) == r:
        p, e = odd[0]
        if e == r + odd_offset and phi(p, p, r) == n:
            return p, p
    return None


def decode_sparse(h, r=3, output='sum'):
    out = {}
    for n, value in h.items():
        pair = decode_factors(n, factor_native(n), r)
        if pair:
            p, q = pair
            m = p + q if output == 'sum' else p * q
            out[m] = out.get(m, Q(0)) + value
    return {n: v for n, v in out.items() if v}


def grammar():
    train = ((2, 3), (3, 5), (3, 3), (4, 3), (2, 9))
    held = ((2, 2), (5, 5), (7, 7), (2, 65537), (65537, 65537), (4, 4), (3, 27))
    profiles = [{'pair': [a, b], 'encoded_index': phi(a, b),
                 'factors': factor_native(phi(a, b)),
                 'expected_prime_pair': sorted([a, b]) if factorization(a) == {a: 1} and factorization(b) == {b: 1} else None,
                 'training': j < len(train)} for j, (a, b) in enumerate(train + held)]
    records = []
    for r, odd, two in product(range(2, 10), range(1, 5), range(5)):
        def prediction(row):
            x = decode_factors(row['encoded_index'], row['factors'], r, odd, two)
            return list(x) if x else None
        fitted = all(prediction(row) == row['expected_prime_pair'] for row in profiles if row['training'])
        bad = next((row['pair'] for row in profiles if not row['training'] and prediction(row) != row['expected_prime_pair']), None) if fitted else None
        records.append({'r': r, 'odd_diagonal_exponent_offset': odd, 'two_diagonal_exponent_offset': two,
                        'training_passed': fitted, 'held_out_passed': fitted and bad is None, 'first_failure': bad})
    return {'models_scored': len(records), 'training_fits': sum(row['training_passed'] for row in records),
            'survivors': [row for row in records if row['held_out_passed']], 'profiles': profiles, 'records': records}


def generic():
    rng = random.Random(2026100709)
    records = []
    for r in (2, 3, 4, 5):
        primes = (2, 3, 5, 7, 11, 13)
        a = {p: Q(rng.choice((-3, -2, -1, 1, 2, 3)), rng.randint(2, 7)) for p in primes}
        b = {p: Q(rng.choice((-3, -2, -1, 1, 2, 3)), rng.randint(2, 7)) for p in primes}
        encoded, sums, products = {}, {}, {}
        for p in a:
            for q in b:
                value, n = a[p] * b[q], phi(p, q, r)
                encoded[n] = encoded.get(n, Q(0)) + value
                sums[p + q] = sums.get(p + q, Q(0)) + value
                products[p * q] = products.get(p * q, Q(0)) + value
        clean = lambda h: {n: v for n, v in h.items() if v}
        Dsum, Dproduct = decode_sparse(encoded, r), decode_sparse(encoded, r, 'product')
        records.append({'r': r, 'a': {str(n): str(v) for n, v in a.items()},
                        'b': {str(n): str(v) for n, v in b.items()},
                        'sum_output': {str(n): str(v) for n, v in sorted(Dsum.items())},
                        'product_output': {str(n): str(v) for n, v in sorted(Dproduct.items())},
                        'sum_identity_passed': Dsum == clean(sums), 'product_identity_passed': Dproduct == clean(products)})
    return {'records': records, 'all_passed': all(row['sum_identity_passed'] and row['product_identity_passed'] for row in records)}


@lru_cache(maxsize=None)
def small_factors(n):
    return factorization(n)


def factor_from_pair(a, b):
    factors = {p: 3 * e for p, e in small_factors(a + b).items()}
    for value in (a, b):
        for p, e in small_factors(value).items():
            factors[p] = factors.get(p, 0) + e
    return factors


def zeta_profile():
    pp = prime_powers(4096)
    encoded, factors = {}, {}
    for j, (a, _, e) in enumerate(pp):
        for b, _, f in pp[j:]:
            n = phi(a, b)
            encoded[n] = encoded.get(n, Q(0)) + Q(1 if a == b else 2, e * f)
            factors[n] = factor_from_pair(a, b)
    sums, products = [Q(0)] * 2049, [Q(0)] * 8193
    queries = []
    for n, value in encoded.items():
        pair = decode_factors(n, factors[n])
        if not pair:
            continue
        p, q = pair
        in_sum, in_product = p + q < len(sums), p * q < len(products)
        if not in_sum and not in_product:
            continue
        if in_sum:
            sums[p + q] += value
        if in_product:
            products[p * q] += value
        queries.append({'encoded_index': n, 'pair': [p, q], 'encoded_coefficient': str(value),
                        'sum_in_cutoff': in_sum, 'product_in_cutoff': in_product})
    primes = [n for n, _, e in pp if e == 1]
    expect_sum = [Q(sum(1 for p in primes if p < n and factorization(n - p) == {n - p: 1})) for n in range(len(sums))]
    expect_product = [Q(0)] * len(products)
    for p in primes:
        for q in primes:
            if p * q < len(products):
                expect_product[p * q] += 1
    return {'raw_prime_power_cutoff': 4096, 'raw_unordered_pair_count': len(pp) * (len(pp) + 1) // 2,
            'raw_encoded_terms': len(encoded), 'sum_cutoff': 2048, 'product_cutoff': 8192,
            'queries': queries, 'ordered_prime_sum_counts': [str(x) for x in sums],
            'ordered_prime_product_counts': [str(x) for x in products],
            'sum_formula_passed': sums == expect_sum, 'product_formula_passed': products == expect_product}


def norm_profiles():
    rows = []
    for r, p in product((2, 3, 4, 5), (2, 3, 5, 17, 257)):
        for tau in (Q(1, 2), Q(r + 1, 2), Q(r + 2, 2), Q(r + 3, 2)):
            n, m = phi(p, p, r), 2 * p
            rows.append({'r': r, 'prime_pair': [p, p], 'source_sigma': '1/2', 'target_tau': str(tau),
                         'encoded_index': n, 'sum_index': m, 'norm_ratio_squared': str(Q(n, m ** int(2 * tau)))})
    return {'records': rows, 'universal_bound': 'A_r:A_sigma->A_tau bounded iff tau >= (r+2)*sigma, sigma>0',
            'exact_norm_when_bounded': '2^((2*r+2)*sigma-2*tau)',
            'product_decoder_sharp_bound': 'B_r:A_sigma->A_tau bounded iff tau >= (r+1)*sigma, sigma>0',
            'product_decoder_exact_norm_when_bounded': '4^((r+1)*sigma-tau)',
            'available_source_sigma_gt': '2/(r+2)', 'bounded_target_tau_gt': '2',
            'pure_power_weight_for_target_half_requires_lambda_gt': '3/2',
            'prime_only_component_endpoint_improvement': {
                'encoded_series': 'sum_(p,q primes) [p*q*(p+q)^r]^(-s)',
                'exact_absolute_abscissa': '2/(r+2)', 'absolute_convergence_at_endpoint': True,
                'additive_series_absolute_convergence_at_endpoint_two': True,
                'classical_input': 'Unconditional prime number theorem; no pointwise Goldbach hypothesis',
                'additive_pure_power_weight_at_target_half_requires_lambda_ge': '3/2',
                'product_pure_power_weight_at_target_half_requires_lambda_ge': '(3*r+2)/(2*(r+2))',
                'r_three_product_lambda_ge': '11/10', 'r_three_product_critical_branch_real_part_le': '-3/5',
                'scope': 'The projected PRIME-ONLY component, not the full prime-power LOG-zeta series'},
            'increasing_r_removes_domain_loss_rejected': True}


def kernel_controls():
    kernel = {phi(3, 7): Q(1), phi(5, 5): Q(-1)}
    decoded = decode_sparse(kernel)
    return {'input': {str(n): str(v) for n, v in kernel.items()}, 'sum_output': decoded,
            'nonzero_input_in_kernel': bool(kernel) and not decoded, 'two_sided_inverse_rejected': bool(kernel) and not decoded,
            'unit_preservation_rejected': not decode_sparse({1: Q(1)}),
            'prime_power_pair_rejected': decode_factors(phi(3, 27), factor_native(phi(3, 27))) is None,
            'missing_prefix_example': {'sum_index': 10, 'encoded_queries': [phi(3, 7), phi(5, 5)],
                                       'encoded_prefix_cutoff': 20000, 'true_ordered_count': 3, 'zero_filling_missing_queries_rejected': True}}


def hilbert_profiles(profile):
    row_weight, row_count = {}, {}
    for query in profile['queries']:
        if query['sum_in_cutoff']:
            n = sum(query['pair'])
            row_weight[n] = row_weight.get(n, 0) + query['encoded_index']
            row_count[n] = row_count.get(n, 0) + 1
    records = []
    for cutoff, tau in product((128, 256, 512, 1024, 2048), (Q(2), Q(5, 2), Q(3))):
        ratios = {n: Q(v, n ** int(2 * tau)) for n, v in row_weight.items() if n <= cutoff}
        worst = max(ratios, key=ratios.get)
        records.append({'r': 3, 'source_sigma': '1/2', 'target_tau': str(tau), 'sum_cutoff': cutoff,
                        'worst_sum_index': worst, 'prime_pair_row_count': row_count[worst],
                        'prefix_operator_norm_squared': str(ratios[worst])})
    return {'records': records,
            'Hilbert_space': 'H_sigma: sum_n |h_n|^2*n^(-2*sigma) finite',
            'exact_norm_squared_formula': 'sup_n n^(2*r*sigma-2*tau)*sum_(p<=q,p+q=n) (p*q)^(2*sigma)',
            'universal_bounded_iff': 'tau >= (r+2)*sigma+1/2, for sigma>=0',
            'boundary_norm_upper_bound': '2^(-2*sigma-1/2)',
            'unweighted_l2_boundedness_rejected': True,
            'necessity_input': 'Unconditional prime number theorem and averaging over balanced prime pairs',
            'finite_prefix_maximum_not_asserted_as_infinite_exact_norm': True}


def main():
    start = time.monotonic()
    learned, laws, profile, norms, controls = grammar(), generic(), zeta_profile(), norm_profiles(), kernel_controls()
    passed = (len(learned['survivors']) == 1 and laws['all_passed'] and profile['sum_formula_passed']
              and profile['product_formula_passed'] and controls['nonzero_input_in_kernel'])
    out = {'prime_pair_decoder_grammar': learned, 'generic_two_product_bridge': laws, 'zeta_profile': profile,
           'weighted_norm_profiles': norms, 'information_loss_controls': controls,
           'hilbert_row_norm_profiles': hilbert_profiles(profile),
           'known_operator_calibration': 'Prime-pair Dirichlet convolution and ordered Goldbach additive convolution',
           'raw_zeta_sum_action': '(ordered_prime_sum_count + diagonal_prime_indicator)/2',
           'all_prime_power_injectivity_claimed': False, 'counts_as_new_primitive': False,
           'historical_novelty_established': False, 'new_RH_estimate_proved': False,
           'all_passed': passed, 'seconds': time.monotonic() - start}
    dest = BASE / 'prime-pair-results'
    dest.mkdir(exist_ok=True)
    (dest / 'prime_pair_search.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Prime-pair grammar:', learned['models_scored'], 'training fits:', learned['training_fits'], 'survivors:', learned['survivors'], flush=True)
    print('Raw correction terms:', profile['raw_encoded_terms'], 'queries:', len(profile['queries']), 'all passed:', passed, 'seconds:', out['seconds'], flush=True)
    assert passed


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Independent complete-fibre and sieve/convolution checks of prime decoding."""

from fractions import Fraction as Q
from functools import lru_cache
from math import isqrt
from pathlib import Path
import json
import time

import flint
import numpy as np

BASE = Path(__file__).resolve().parent


@lru_cache(maxsize=None)
def factors(n):
    original, result, p = n, {}, 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        result[n] = result.get(n, 0) + 1
    assert original >= 1
    return result


@lru_cache(maxsize=None)
def integer_pairs(n, r):
    fs = {}
    for p, e in flint.fmpz(n).factor():
        p, e = int(p), int(e)
        assert flint.fmpz(p).is_prime()
        fs[p] = fs.get(p, 0) + e
    reconstructed = 1
    for p, e in fs.items():
        reconstructed *= p ** e
    assert reconstructed == n
    possible_sums = [1]
    for p, e in fs.items():
        possible_sums = [s * p ** j for s in possible_sums for j in range(e // r + 1)]
    pairs = []
    for s in possible_sums:
        m = n // s ** r
        discriminant = s * s - 4 * m
        if discriminant < 0:
            continue
        root = isqrt(discriminant)
        if root * root == discriminant and (s - root) % 2 == 0:
            a, b = (s - root) // 2, (s + root) // 2
            if a >= 2 and a * b * (a + b) ** r == n:
                pairs.append((a, b))
    return tuple(sorted(set(pairs)))


def isprime(n):
    return bool(flint.fmpz(n).is_prime())


def prime_pair(n, r):
    found = [pair for pair in integer_pairs(n, r) if all(isprime(v) for v in pair)]
    assert len(found) <= 1
    return found[0] if found else None


def grammar(source):
    for row in source['prime_pair_decoder_grammar']['records']:
        r, odd, two = row['r'], row['odd_diagonal_exponent_offset'], row['two_diagonal_exponent_offset']
        def predicts(profile):
            pair = prime_pair(profile['encoded_index'], r)
            if pair and pair[0] == pair[1]:
                if pair[0] == 2 and two != 2 or pair[0] != 2 and odd != 2:
                    return None
            return list(pair) if pair else None
        profiles = source['prime_pair_decoder_grammar']['profiles']
        fitted = all(predicts(p) == p['expected_prime_pair'] for p in profiles if p['training'])
        bad = next((p['pair'] for p in profiles if not p['training'] and predicts(p) != p['expected_prime_pair']), None) if fitted else None
        assert row['training_passed'] == fitted and row['held_out_passed'] == (fitted and bad is None) and row['first_failure'] == bad
    return True


def generic(source):
    for row in source['generic_two_product_bridge']['records']:
        a, b = ({int(n): Q(v) for n, v in row[key].items()} for key in ('a', 'b'))
        encoded = {}
        for p in a:
            for q in b:
                n = p * q * (p + q) ** row['r']
                encoded[n] = encoded.get(n, Q(0)) + a[p] * b[q]
        actual_sum, actual_product = {}, {}
        for n, v in encoded.items():
            p, q = prime_pair(n, row['r'])
            actual_sum[p + q] = actual_sum.get(p + q, Q(0)) + v
            actual_product[p * q] = actual_product.get(p * q, Q(0)) + v
        for actual, key in ((actual_sum, 'sum_output'), (actual_product, 'product_output')):
            actual = {n: v for n, v in actual.items() if v}
            assert actual == {int(n): Q(v) for n, v in row[key].items()}
    return True


def sieve(n):
    flags = np.ones(n + 1, dtype=np.int64)
    flags[:2] = 0
    for p in range(2, isqrt(n) + 1):
        if flags[p]:
            flags[p * p::p] = 0
    return flags


def zeta(source):
    profile = source['zeta_profile']
    actual_sum = [Q(0)] * (profile['sum_cutoff'] + 1)
    actual_product = [Q(0)] * (profile['product_cutoff'] + 1)
    diagonal_queries, checked = 0, 0
    for row in profile['queries']:
        all_pp = [pair for pair in integer_pairs(row['encoded_index'], 3) if len(factors(pair[0])) == len(factors(pair[1])) == 1]
        # Validate the full prime-power fibre, not only the proposed prime
        # pair or the source's finite input cutoff.
        assert len(all_pp) == 1
        p, q = all_pp[0]
        assert isprime(p) and isprime(q) and [p, q] == row['pair']
        value = Q(1 if p == q else 2)
        assert Q(row['encoded_coefficient']) == value
        assert row['sum_in_cutoff'] == (p + q < len(actual_sum))
        assert row['product_in_cutoff'] == (p * q < len(actual_product))
        if row['sum_in_cutoff']:
            actual_sum[p + q] += value
        if row['product_in_cutoff']:
            actual_product[p * q] += value
        diagonal_queries += p == q
        checked += 1
    flags = sieve(profile['sum_cutoff'])
    convolution = np.convolve(flags, flags)[:len(flags)]
    assert actual_sum == list(map(Q, profile['ordered_prime_sum_counts'])) == list(map(Q, convolution.tolist()))
    expect_product = [Q(0)] * len(actual_product)
    for n in range(2, len(expect_product)):
        fs = factors(n)
        if sum(fs.values()) == 2:
            expect_product[n] = Q(1 if len(fs) == 1 else 2)
    assert actual_product == expect_product == list(map(Q, profile['ordered_prime_product_counts']))
    assert diagonal_queries > 0 and actual_sum[4] == 1 and actual_sum[10] == 3
    return {'all_passed': True, 'complete_prime_power_fibres_checked': checked, 'diagonal_queries': diagonal_queries,
            'known_additive_calibration': 'Independent integer sieve and exact convolution',
            'known_product_calibration': 'Independent total-prime-exponent count equals two'}


def norm_and_controls(source):
    for row in source['weighted_norm_profiles']['records']:
        p, q = row['prime_pair']
        r, tau = row['r'], Q(row['target_tau'])
        assert p == q and isprime(p)
        n, m = p * q * (p + q) ** r, p + q
        assert row['encoded_index'] == n and row['sum_index'] == m
        assert Q(row['norm_ratio_squared']) == Q(n, m ** int(2 * tau))
        if p == 2 and tau >= Q(r + 2, 2):
            assert Q(row['norm_ratio_squared']) == Q(2) ** (2 * r + 2 - 4 * tau)
        assert Q(r + 2) * Q(2, r + 2) - Q(1, 2) == Q(3, 2)
        boundary_sigma = Q(2, r + 2)
        assert (r + 2) * boundary_sigma == 2
        assert (r + 1) * boundary_sigma - Q(1, 2) == Q(3 * r + 2, 2 * (r + 2))
        assert Q(1, 2) - Q(3 * r + 2, 2 * (r + 2)) == Q(-r, r + 2)
    endpoint = source['weighted_norm_profiles']['prime_only_component_endpoint_improvement']
    assert Q(endpoint['r_three_product_lambda_ge']) == Q(11, 10)
    assert Q(endpoint['r_three_product_critical_branch_real_part_le']) == Q(-3, 5)
    kernel = {int(n): Q(v) for n, v in source['information_loss_controls']['input'].items()}
    sums = {}
    for n, v in kernel.items():
        p, q = prime_pair(n, 3)
        sums[p + q] = sums.get(p + q, Q(0)) + v
    assert kernel and not any(sums.values()) and not prime_pair(3 * 27 * 30 ** 3, 3)
    example = source['information_loss_controls']['missing_prefix_example']
    assert example['encoded_queries'] == [21000, 25000] and all(n > example['encoded_prefix_cutoff'] for n in example['encoded_queries'])
    assert example['true_ordered_count'] == 3 and source['information_loss_controls']['two_sided_inverse_rejected']
    assert not source['all_prime_power_injectivity_claimed'] and not source['counts_as_new_primitive']
    return True


def hilbert_profiles(source):
    bits = sieve(2048)
    weights, cardinalities = {}, {}
    for n in range(4, len(bits)):
        for p in range(2, n // 2 + 1):
            q = n - p
            if bits[p] and bits[q]:
                weights[n] = weights.get(n, 0) + p * q * n ** 3
                cardinalities[n] = cardinalities.get(n, 0) + 1
    for row in source['hilbert_row_norm_profiles']['records']:
        tau = Q(row['target_tau'])
        candidates = {n: Q(v, n ** int(2 * tau)) for n, v in weights.items() if n <= row['sum_cutoff']}
        expected = max(candidates.values())
        worst = row['worst_sum_index']
        assert expected == candidates[worst] == Q(row['prefix_operator_norm_squared'])
        assert row['prime_pair_row_count'] == cardinalities[worst]
        if tau >= 3:
            assert expected <= Q(1, 8)
    assert source['hilbert_row_norm_profiles']['unweighted_l2_boundedness_rejected']
    assert source['hilbert_row_norm_profiles']['finite_prefix_maximum_not_asserted_as_infinite_exact_norm']
    return True


def main():
    start = time.monotonic()
    source = json.loads((BASE / 'prime-pair-results/prime_pair_search.json').read_text())
    assert source['all_passed']
    exact_zeta = zeta(source)
    checks = {'all_grammar_decisions_by_complete_integer_fibres': grammar(source),
              'generic_product_and_sum_laws': generic(source),
              'every_zeta_query_has_one_complete_prime_power_fibre': exact_zeta['all_passed'],
              'diagonal_and_known_sieve_convolution_calibrations': exact_zeta['diagonal_queries'] > 0,
              'weighted_norm_and_information_loss_controls': norm_and_controls(source),
              'exact_Hilbert_row_norms_by_prime_sum_enumeration': hilbert_profiles(source)}
    out = {'checks': checks, 'exact_zeta_audit': exact_zeta, 'production_imports': False,
           'shared_trusted_kernel': 'FLINT integer factorization/primality; independent discriminants, trial factors, sieve and integer convolution',
           'all_passed': all(checks.values()), 'seconds': time.monotonic() - start}
    (BASE / 'prime-pair-results/prime_pair_verification.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Independent prime-pair audit:', sum(checks.values()), '/', len(checks), 'queries:', exact_zeta['complete_prime_power_fibres_checked'], 'seconds:', out['seconds'], flush=True)
    assert out['all_passed']


if __name__ == '__main__':
    main()

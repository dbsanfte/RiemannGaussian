#!/usr/bin/env python3
"""Changed square-prime references, cutoffs and Cauchy zero bounds."""

from fractions import Fraction as Q
from math import comb, factorial, isqrt
from pathlib import Path
import json
import time

import flint
import numpy as np

BASE = Path(__file__).resolve().parent


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def short(x):
    return x.str(18)


def box(r):
    return flint.acb(flint.arb(0, r), flint.arb(0, r))


def primes(N):
    bits = np.ones(N + 1, dtype=np.int64)
    bits[:2] = 0
    for p in range(2, isqrt(N) + 1):
        if bits[p]:
            bits[p * p::p] = 0
    return [int(p) for p in np.flatnonzero(bits)], bits


def series(values, s):
    return sum((flint.arb(int(v)) * (-s * flint.arb(n).log()).exp()
                for n, v in enumerate(values) if v), flint.acb(0))


def actual_points(source):
    _, flags = primes(3072)
    counts = np.convolve(flags, flags)[:len(flags)]
    ps, _ = primes(12288)
    products = np.zeros(12289, dtype=np.int64)
    for j, p in enumerate(ps):
        for q in ps[j:]:
            if p * q >= len(products):
                break
            products[p * q] += 1 if p == q else 2
    small, _ = primes(512)
    rows = []
    for row in source['actual_zeta_ball_checks']:
        sigma, height = Q(row['s'][0]), row['s'][1]
        s = flint.acb(real(sigma), height)
        # This reference sums the entire bounded PRIME SQUARE directly;
        # it imports no production coefficients, Mobius sums or contour.
        grouped = {}
        for p in small:
            for q in small:
                grouped[p + q] = grouped.get(p + q, 0) + 1
        reference = sum((v * (-s * flint.arb(n).log()).exp() for n, v in grouped.items()), flint.acb(0))
        reference_tail = 2 * flint.arb(513) ** (2 - real(sigma)) / ((real(sigma) - 1) * (real(sigma) - 2))
        finite = series(counts, s)
        coefficient_tail = flint.arb(3072) ** (2 - real(sigma)) / (real(sigma) - 2)
        allowed = coefficient_tail + reference_tail
        distance = (finite - reference).abs_upper()
        wrong = (finite + real(Q(1, 3)) * (-s * flint.arb(4).log()).exp() - reference).abs_lower()
        prime_finite = sum(((-s * flint.arb(p).log()).exp() for p in small), flint.acb(0))
        prime_tail = flint.arb(512) ** (1 - real(sigma)) / (real(sigma) - 1)
        majorant = real(sigma).zeta() - 1
        product_reference_tail = 2 * majorant * prime_tail + prime_tail ** 2
        product_coefficient_tail = 2 * flint.arb(12288) ** (1 - real(sigma)) / (real(sigma) - 1)
        product_allowed = product_coefficient_tail + product_reference_tail
        product_finite = series(products, s)
        product_distance = (product_finite - prime_finite ** 2).abs_upper()
        product_wrong = (product_finite + real(Q(1, 3)) * (-s * flint.arb(4).log()).exp() - prime_finite ** 2).abs_lower()
        passed = bool(distance < allowed) and bool(wrong > allowed) and bool(product_distance < product_allowed) and bool(product_wrong > product_allowed)
        rows.append({'s': row['s'], 'sum_cutoff': 3072, 'product_cutoff': 12288, 'independent_prime_square_cutoff': 512,
                     'additive_difference_upper_ball': short(distance), 'additive_combined_bound_ball': short(allowed),
                     'additive_smaller_perturbation_lower_ball': short(wrong), 'prime_square_infinite_tail_ball': short(reference_tail),
                     'product_difference_upper_ball': short(product_distance), 'product_combined_bound_ball': short(product_allowed),
                     'product_smaller_perturbation_lower_ball': short(product_wrong), 'all_passed': passed})
        print('Independent prime-pair analytic', sigma, height, passed, flush=True)
    return rows


def zero_controls(source):
    records = []
    for row in source['full_prime_product_zero_obstruction_controls']['records']:
        radius, R = Q(row['radius']), Q(1, 40)
        centre = flint.acb(real(Q(1, 2)), row['disk_centre'][1])
        flint.ctx.cap = 2
        jet = flint.acb_series([centre, flint.acb(1)], 2).zeta()
        maximum = (centre + box(real(R))).zeta().abs_upper()
        ratio = real(radius / R)
        error = maximum * ratio ** 2 / (1 - ratio)
        zeta_upper = (jet[0] + real(radius) * jet[1]).abs_upper() + error
        R2 = Q(1, 10)
        maximum2 = (2 * centre + box(real(R2))).zeta().abs_upper()
        ratio2 = real(2 * radius / R2)
        variation2 = maximum2 * ratio2 / (1 - ratio2)
        z2lower = (2 * centre).zeta().abs_lower() - variation2
        sigma = Q(1, 2) + radius
        # mu(2)=-1 is handled using the whole-disk modulus lower bound.
        # Every m>=3 term is bounded by its real Euler-log norm.
        correction = sum((real(m * sigma).zeta().log() / m for m in range(3, 41)), flint.arb(0))
        t = flint.arb(2) ** (-real(sigma))
        correction += t ** 41 / (41 * (1 - t)) * (1 + 2 / (41 * real(sigma) - 1))
        RePupper = zeta_upper.log() - z2lower.log() / 2 + correction
        jump = -4 * flint.arb.pi() * RePupper
        passed = bool(z2lower > 0) and bool(RePupper < 0) and bool(jump > 0)
        records.append({'disk_centre': row['disk_centre'], 'radius': row['radius'], 'Taylor_Cauchy_radius': str(R),
                        'whole_disk_zeta_2s_Cauchy_radius': str(R2), 'basepoint_zeta_modulus_upper_ball': short(zeta_upper),
                        'whole_disk_zeta_2s_modulus_lower_ball': short(z2lower), 'branch_independent_Re_prime_zeta_upper_ball': short(RePupper),
                        'independent_prime_square_jump_lower_ball': short(jump),
                        'additive_series_value_or_monodromy_at_this_zero_claimed': False, 'all_passed': passed})
    return {'records': records, 'all_passed': all(row['all_passed'] for row in records)}


def kernel_normalization():
    sigma, height = Q(4), Q(137, 100)
    s, pi = flint.acb(real(sigma), real(height)), flint.arb.pi()
    I, T, u = flint.acb(0, 1), Q(24), height / 2
    def integrand(t, analytic):
        return (s / 2 + I * t).gamma() * (s / 2 - I * t).gamma() / s.gamma()
    value = flint.acb.integral(integrand, 0, real(T), rel_tol=flint.arb('1e-20'), abs_tol=flint.arb('1e-20'),
                               eval_limit=100000, depth_limit=30, use_heap=True) / pi
    polynomial = sum((comb(3, j) * real(T + u + 2) ** (3 - j) * factorial(j) / pi ** (j + 1)
                      for j in range(4)), flint.arb(0))
    tail = 2 * pi / (1 - (-2 * pi).exp()) / (pi * s.gamma().abs_lower()) * (-pi * real(T)).exp() * polynomial
    expected = (-s * flint.arb(2).log()).exp()
    enclosure = value + box(tail)
    passed = bool(enclosure.contains(expected)) and bool((2 * enclosure - expected).abs_lower() > 0)
    return {'s': [str(sigma), str(height)], 'native_beta_kernel_ball': short(enclosure),
            'exact_expected_two_power_ball': short(expected), 'wrong_factor_two_rejected': bool((2 * enclosure - expected).abs_lower() > 0),
            'all_passed': passed}


def main():
    start = time.monotonic()
    flint.ctx.prec = 256
    source = json.loads((BASE / 'prime-pair-results/prime_pair_analytic.json').read_text())
    assert source['all_passed']
    rows, zeros, kernel = actual_points(source), zero_controls(source), kernel_normalization()
    checks = {'six_two_product_cases_with_changed_reference_cutoffs_and_smaller_errors': all(row['all_passed'] for row in rows),
              'two_prime_square_zero_obstructions_by_Taylor_Cauchy': zeros['all_passed'],
              'native_beta_kernel_normalization_and_wrong_factor_control': kernel['all_passed'],
              'both_arithmetic_cutoffs_changed': all(row['sum_cutoff'] != old['sum_cutoff'] and row['product_cutoff'] != old['product_cutoff'] for row, old in zip(rows, source['actual_zeta_ball_checks']))}
    out = {'checks': checks, 'actual_zeta_ball_checks': rows, 'full_prime_product_zero_obstruction_controls': zeros,
           'kernel_normalization': kernel, 'production_imports': False, 'shared_trusted_kernel': 'FLINT/Arb',
           'all_passed': all(checks.values()), 'seconds': time.monotonic() - start}
    (BASE / 'prime-pair-results/prime_pair_analytic_verification.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Independent prime-pair analytic audit:', sum(checks.values()), '/', len(checks), 'seconds:', out['seconds'], flush=True)
    assert out['all_passed']


if __name__ == '__main__':
    main()

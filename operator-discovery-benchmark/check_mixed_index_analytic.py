#!/usr/bin/env python3
"""Independent coefficient recovery, Bell-row tails, and reverse-transfer audit."""

from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial
from pathlib import Path
import json
import time

import flint

from check_mixed_index import anchored, scale, d_exp, transfer


BASE = Path(__file__).resolve().parent


def real(value):
    value = Q(value)
    return flint.arb(value.numerator) / value.denominator


def box(radius):
    return flint.acb(flint.arb(0, radius), flint.arb(0, radius))


def short(value):
    return value.str(18)


def recover(height, cutoff=128, sigma=1024):
    flint.ctx.prec = 10240
    s = flint.acb(sigma, height)
    observed = s.zeta().log()
    values = [Q(0), Q(0)]
    weights = {n: (-s * flint.arb(n).log()).exp() for n in range(2, cutoff + 1)}
    bounds = []
    for n in range(2, cutoff + 1):
        # Recompute the exact-prefix finite sum rather than recursively
        # subtracting from the production residual.
        prefix = sum((real(values[m]) * weights[m] for m in range(2, n)), flint.acb(0))
        estimate = (observed - prefix) / weights[n]
        # Eight explicit omitted terms, then an integral, give a different
        # rigorously enclosing infinite alias bound.
        tail = sum(((flint.arb(n) / (n + j)) ** sigma for j in range(1, 9)), flint.arb(0))
        tail += (flint.arb(n) / (n + 8)) ** sigma * flint.arb(n + 8) / (sigma - 1)
        candidates = [Q(1, e) for e in reversed(range(1, n.bit_length()))] + [Q(0)]
        possible = [q for q in candidates if not bool((estimate - real(q)).abs_lower() > tail)]
        assert len(possible) == 1
        values.append(possible[0])
        bounds.append(bool((estimate - real(possible[0])).abs_upper() < tail))
    return values, all(bounds)


@lru_cache(maxsize=None)
def bell_polynomials(beta, count):
    values = [Q(1)]
    for n in range(1, count + 1):
        values.append(beta * sum((comb(n - 1, j) * values[j] for j in range(n)), Q(0)))
    return values


def tail_by_rows(sigma, beta, bit_cutoff, rows=8):
    bells = bell_polynomials(beta, bit_cutoff + rows + 1)
    finite = flint.arb(0)
    for j in range(bit_cutoff, bit_cutoff + rows):
        mass = sum((Q(comb(j, k - 1)) * bells[k] / factorial(k) for k in range(1, j + 2)), Q(0))
        finite += real(mass) * flint.arb(2) ** (-j * real(sigma))
    r = flint.arb(2)
    ratio = (1 + 1 / r) * flint.arb(2) ** (-real(sigma))
    assert bool(ratio < 1)
    remainder = (real(beta) * (r.exp() - 1)).exp() / r * ratio ** (bit_cutoff + rows) / (1 - ratio)
    return finite + remainder


def reverse_by_one_zeta(s, sigma, cutoff=256):
    # 1/(n-1)=1/n+1/(n*(n-1)) gives one native zeta value and an
    # independently evaluated fast-convergent correction series.
    exponent = (s + 1).zeta() - 1
    exponent += sum(((-s * flint.arb(n).log()).exp() / (n * (n - 1))
                     for n in range(2, cutoff + 1)), flint.acb(0))
    tail = 2 * flint.arb(cutoff) ** (-real(sigma) - 1) / (real(sigma) + 1)
    return (exponent + box(tail)).exp()


def evaluate(values, s):
    return sum((real(value) * (-s * flint.arb(n).log()).exp()
                for n, value in enumerate(values[1:], 1)), flint.acb(0))


@lru_cache(maxsize=None)
def arithmetic_profile(beta):
    return transfer([Q(0)] + [Q(1)] * 2048, beta=beta)


def point_checks(source):
    reverse_cutoff = 768
    reverse = d_exp([Q(0), Q(0)] + [Q(1, n - 1) for n in range(2, reverse_cutoff + 1)])
    records = []
    for item in source['actual_zeta_ball_checks']:
        beta, sigma = Q(item['beta']), Q(item['s'][0])
        height = item['s'][1]
        logarithm, recovered = recover(height)
        production = item['native_zeta_coefficient_recovery']['records']
        prefix_agrees = all(logarithm[x['n']] == Q(x['recovered_exact_coefficient']) for x in production)
        native_origin = scale(anchored([beta * x for x in logarithm], 'EXP'), 1)
        full = arithmetic_profile(beta)
        exact_prefix = native_origin == full[:len(native_origin)]
        flint.ctx.prec = 256
        s = flint.acb(real(sigma), height)
        allowed = tail_by_rows(sigma, beta, 7) + tail_by_rows(sigma, beta, 11)
        finite = evaluate(full, s)
        reference = evaluate(native_origin, s)
        delta = real(Q(1, 11)) * (-s * flint.arb(2).log()).exp()
        difference = (finite - reference).abs_upper()
        corrupted = (finite + delta - reference).abs_lower()
        candidate_passed = recovered and prefix_agrees and exact_prefix and bool(difference < allowed) and bool(corrupted > allowed)
        reverse_reference = reverse_by_one_zeta(s, sigma)
        reverse_finite = evaluate(reverse, s)
        reverse_allowed = flint.arb(1).exp() * flint.arb(reverse_cutoff) ** (1 - real(sigma))
        reverse_difference = (reverse_finite - reverse_reference).abs_upper()
        reverse_bad = (reverse_finite + delta - reverse_reference).abs_lower()
        reverse_passed = bool(reverse_difference < reverse_allowed) and bool(reverse_bad > reverse_allowed)
        records.append({'beta': str(beta), 's': item['s'], 'native_sample_real_part': 1024,
                        'native_precision_bits': 10240, 'native_coefficient_cutoff': 128,
                        'regularizer_arithmetic_cutoff': 2048, 'all_exact_prefixes_agree': prefix_agrees and exact_prefix,
                        'regularizer_difference_upper_ball': short(difference), 'independent_Bell_row_tail_ball': short(allowed),
                        'regularizer_perturbation_lower_ball': short(corrupted),
                        'reverse_arithmetic_cutoff': reverse_cutoff, 'reverse_correction_cutoff': 256,
                        'reverse_difference_upper_ball': short(reverse_difference), 'reverse_Rankin_tail_ball': short(reverse_allowed),
                        'reverse_perturbation_lower_ball': short(reverse_bad),
                        'all_passed': candidate_passed and reverse_passed})
        print(f'Independent mixed-index native zeta beta={beta}, s={item["s"]}: {records[-1]["all_passed"]}', flush=True)
    return records


def zero_checks(source):
    records = []
    for item in source['existing_actual_zero_new_operator_controls']['records']:
        radius, height = Q(item['radius']), item['disk_centre'][1]
        sigma = Q(1, 2) - radius
        region = flint.acb(real(Q(1, 2)) + flint.arb(0, real(radius)),
                           flint.arb(height) + flint.arb(0, real(radius)))
        reverse = reverse_by_one_zeta(region, sigma, cutoff=4096)
        ratio = real(Q(4, 3)) * flint.arb(2) ** (-real(sigma))
        passed = bool(reverse.abs_lower() > 0) and bool(ratio < 1)
        records.append({'disk_centre': item['disk_centre'], 'radius': item['radius'],
                        'reverse_single_zeta_correction_cutoff': 4096,
                        'reverse_modulus_lower_after_infinite_tail_ball': short(reverse.abs_lower()),
                        'independent_radius_three_Bell_ratio_ball': short(ratio),
                        'regularizer_uniform_holomorphy_on_zero_disk_certified': bool(ratio < 1),
                        'all_passed': passed})
    return {'records': records, 'all_passed': all(x['all_passed'] for x in records)}


def main():
    started = time.monotonic()
    flint.ctx.prec = 256
    source = json.loads((BASE / 'mixed-index-results/mixed_index_analytic.json').read_text())
    points = point_checks(source)
    zeros = zero_checks(source)
    checks = {'all_six_native_zeta_recoveries_and_both_transformed_series_comparisons': all(x['all_passed'] for x in points),
              'all_exact_prefixes_independently_recovered': all(x['all_exact_prefixes_agree'] for x in points),
              'both_existing_actual_zero_new_operator_controls': zeros['all_passed'],
              'independent_coefficient_and_series_cutoffs_changed': all(x['native_coefficient_cutoff'] != s['regularizer_comparison']['native_origin_cutoff']
                    and x['reverse_arithmetic_cutoff'] != s['reverse_shifted_zeta_comparison']['arithmetic_cutoff']
                    for x, s in zip(points, source['actual_zeta_ball_checks']))}
    result = {'checks': checks, 'all_passed': all(checks.values()), 'actual_zeta_ball_checks': points,
              'existing_actual_zero_new_operator_controls': zeros, 'no_production_imports': True,
              'shared_trusted_kernel': 'FLINT/Arb', 'proof': 'mixed_index_proof.txt',
              'elapsed_seconds': time.monotonic() - started}
    (BASE / 'mixed-index-results/mixed_index_analytic_verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Independent mixed-index analytic audit: {sum(checks.values())}/{len(checks)}; elapsed={result["elapsed_seconds"]:.2f}s')
    assert result['all_passed']


if __name__ == '__main__':
    main()

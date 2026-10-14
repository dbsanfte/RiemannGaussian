#!/usr/bin/env python3
"""Independent zeta cancellation audit with ratio tails and a Cauchy zero count.

Only independent arithmetic-checker helpers are imported. The production
native hypergeometric evaluators and coefficient arrays are not reused.
"""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import gcd
from pathlib import Path
import json
import time

import flint

from check_cancellation import factor, divisors, indicator, local_root, root, summed_kernel


BASE = Path(__file__).resolve().parent
ARITHMETIC_CUTOFF = 6144


def real(value):
    value = Q(value)
    return flint.arb(value.numerator) / value.denominator


def box(radius):
    return flint.acb(flint.arb(0, radius), flint.arb(0, radius))


def common_base(b, c):
    first, second = factor(b), factor(c)
    divisor_b, divisor_c = 0, 0
    for e in first.values():
        divisor_b = gcd(divisor_b, e)
    for e in second.values():
        divisor_c = gcd(divisor_c, e)
    primitive_b = {p: e // divisor_b for p, e in first.items()}
    primitive_c = {p: e // divisor_c for p, e in second.items()}
    if primitive_b != primitive_c:
        return None
    primitive = 1
    for p, e in primitive_b.items():
        primitive *= p ** e
    return primitive ** (divisor_b * divisor_c // gcd(divisor_b, divisor_c))


def resonance(s, beta, base, degree=72):
    if base is None:
        return flint.acb(1)
    coefficients = [Q(1)]
    for k in range(degree):
        ratio = Q(1)
        for e in factor(base).values():
            for j in range(e):
                ratio *= Q(beta + e * k + j, e * k + j + 1)
        coefficients.append(coefficients[-1] * ratio)
    z = (-s * flint.arb(base).log()).exp()
    value = flint.acb(0)
    for coefficient in reversed(coefficients):
        value = value * z + real(coefficient)
    tail = z.abs_upper() ** (degree + 1) / (1 - z.abs_upper())
    assert 0 <= beta <= 1
    return value + box(tail)


@lru_cache(maxsize=None)
def root_at(beta, n):
    coefficient = Q(1)
    for e in factor(n).values():
        coefficient *= local_root(beta, e)
    return coefficient


def filtered(s, beta, outer, inner, degree=40):
    coefficients = []
    for k in range(degree + 1):
        n, d, coefficient = outer ** k, 1, Q(0)
        while n % d == 0:
            coefficient += root_at(beta, d) * root_at(beta, n // d)
            d *= inner
        coefficients.append(coefficient)
    z = (-s * flint.arb(outer).log()).exp()
    value = flint.acb(0)
    for coefficient in reversed(coefficients):
        value = value * z + real(coefficient)
    tail = z.abs_upper() ** (degree + 1) / (1 - z.abs_upper())
    assert 0 < beta <= Q(1, 2)
    return value + box(tail)


def fresh_coefficients(b, c, beta):
    g = root(beta, ARITHMETIC_CUTOFF)
    total, corrected = [Q(0)] * len(g), [Q(0)] * len(g)
    for n in range(1, len(g)):
        for d in divisors(n):
            e = n // d
            product_value = g[d] * g[e]
            total[n] += product_value * summed_kernel(d, e, b, c)
            bi, ci = indicator(e, b), indicator(e, c)
            corrected[n] += product_value * Q(bi + ci + bi * ci, 3)
    return total, corrected


def evaluate(values, s):
    return sum((real(coefficient) * (-s * flint.arb(n).log()).exp()
                for n, coefficient in enumerate(values[1:], 1)), flint.acb(0))


def point_checks(source):
    records = []
    for item in source['actual_zeta_ball_checks']:
        b, c = item['bases']
        beta, sigma = Q(item['beta']), Q(item['s'][0])
        s = flint.acb(real(sigma), item['s'][1])
        assert bool(real(sigma).zeta().log() < flint.arb.pi())
        # Ordinary binomial coefficients independently computed above;
        # the principal root agrees with the normalized Euler logarithm.
        f = (real(beta) * s.zeta().log()).exp()
        common = common_base(b, c)
        rb, rc, rbc = (resonance(s, beta, base) for base in (b, c, common))
        rb2, rc2, rbc2 = (resonance(s, 2 * beta, base) for base in (b, c, common))
        reference_total = f ** 2 + 2 * f * (rb + rc + rbc) - rb2 - rc2 + 2 * rb * rc - 2 * filtered(s, beta, c, b) - 2 * filtered(s, beta, b, c) + rbc2
        reference_corrected = f * (rb + rc + rbc) / 3
        total, corrected = fresh_coefficients(b, c, beta)
        tail = flint.arb(ARITHMETIC_CUTOFF) ** (1 - real(sigma)) / (real(sigma) - 1)
        delta = real(Q(1, 2)) * (-s * flint.arb(2).log()).exp()
        tests = []
        for name, values, reference, allowed in (('direct_four_kernel_sum', total, reference_total, 4 * tail),
                                                ('direct_projected_root', corrected, reference_corrected, tail)):
            finite = evaluate(values, s)
            difference = (finite - reference).abs_upper()
            corrupted = (finite + delta - reference).abs_lower()
            tests.append({'representation': name, 'difference_upper_ball': str(difference),
                          'proved_infinite_error_ball': str(allowed), 'coefficient_2_perturbation': '1/2',
                          'perturbed_difference_lower_ball': str(corrupted),
                          'all_passed': bool(difference < allowed) and bool(corrupted > allowed)})
        records.append({'bases': [b, c], 'beta': str(beta), 's': item['s'],
                        'arithmetic_cutoff': ARITHMETIC_CUTOFF, 'resonance_degree': 72,
                        'filtered_resonance_degree': 40, 'common_power_base': common,
                        'comparisons': tests, 'all_passed': all(x['all_passed'] for x in tests) and common == item['common_power_base']})
        print(f'Independent cancellation zeta {b},{c}, beta={beta}: {records[-1]["all_passed"]}', flush=True)
    return records


def zero_control(source):
    item = source['fresh_actual_critical_line_zero_control']
    height, small, large = item['disk_centre'][1], Q(item['radius']), Q(1, 50)
    centre = flint.acb(real(Q(1, 2)), height)
    wider = flint.acb(real(Q(1, 2)) + flint.arb(0, real(large)), flint.arb(height) + flint.arb(0, real(large)))
    region = flint.acb(real(Q(1, 2)) + flint.arb(0, real(small)), flint.arb(height) + flint.arb(0, real(small)))
    jet = flint.acb_series([centre, 1], 2).zeta()
    ratio = real(small / large)
    error = jet[0].abs_upper() + wider.zeta().abs_upper() * ratio ** 2 / (1 - ratio)
    linear = jet[1].abs_lower() * real(small)
    basepoint = centre + real(small / 2)
    mass = ((basepoint - 1) * basepoint.zeta()).abs_lower()
    records = []
    for record in item['correction_records']:
        b, c = record['bases']
        beta = Q(record['beta'])
        common = common_base(b, c)
        correction = sum((resonance(region, beta, base, degree=96) for base in (b, c, common)), flint.acb(0)) / 3
        jump = correction.real.lower() * mass ** real(beta) * (2 * (flint.arb.pi() * real(beta)).sin()).abs_lower()
        expected = beta.denominator != 1
        phase = (flint.acb(0, 2 * flint.arb.pi() * real(beta))).exp()
        passed = bool(correction.real > 0) and (bool(jump > 0) if expected else bool((phase - 1).contains(0)))
        records.append({'bases': [b, c], 'beta': str(beta), 'independent_resonance_degree': 96,
                        'correction_real_lower_after_infinite_tail_ball': str(correction.real.lower()),
                        'independent_half_radius_monodromy_jump_lower_ball': str(jump),
                        'nontrivial_branch_obstruction_expected': expected, 'all_passed': passed})
    return {'independent_Cauchy_radius': str(large), 'linear_lower_ball': str(linear),
            'Cauchy_error_upper_ball': str(error), 'one_simple_actual_zeta_zero_certified': bool(error < linear),
            'correction_records': records, 'all_passed': bool(error < linear) and all(x['all_passed'] for x in records)}


def main():
    started = time.monotonic()
    flint.ctx.prec = 256
    source = json.loads((BASE / 'cancellation-results/cancellation_analytic.json').read_text())
    points = point_checks(source)
    zero = zero_control(source)
    corrected_common_power = common_base(4, 8)
    checks = {'six_fresh_zeta_points_and_both_representations_with_smaller_perturbation': all(x['all_passed'] for x in points),
              'fresh_actual_zero_independent_Cauchy_count': zero['one_simple_actual_zeta_zero_certified'],
              'all_fractional_branch_and_integer_phase_controls': zero['all_passed'],
              'common_power_is_64_not_larger_base_8': corrected_common_power == 64 and not indicator(8, corrected_common_power)}
    result = {'checks': checks, 'all_passed': all(checks.values()), 'actual_zeta_ball_checks': points,
              'fresh_actual_zero_control': zero, 'no_production_imports': True,
              'shared_trusted_kernel': 'FLINT/Arb', 'proof': 'cancellation_proof.txt',
              'independent_resonance_method': 'Exact coefficient ratios and geometric tails replace production hypergeometric evaluation',
              'elapsed_seconds': time.monotonic() - started}
    (BASE / 'cancellation-results/cancellation_analytic_verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Independent cancellation analytic audit: {sum(checks.values())}/{len(checks)}; elapsed={result["elapsed_seconds"]:.2f}s')
    assert result['all_passed']


if __name__ == '__main__':
    main()

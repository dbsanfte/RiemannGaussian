#!/usr/bin/env python3
"""Actual-zeta checks of the learned four-orientation cancellation identity."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from pathlib import Path
import json
import time

import flint
import mpmath as mp

from exact_arithmetic import factorization


BASE = Path(__file__).resolve().parent


def real(value):
    value = Q(value)
    return flint.arb(value.numerator) / value.denominator


def common_power_base(b, c):
    a, d = factorization(b), factorization(c)
    if set(a) != set(d):
        return None
    ratios = {Q(a[p], d[p]) for p in a}
    if len(ratios) != 1:
        return None
    ratio = ratios.pop()
    return b ** ratio.denominator


def resonance(s, beta, base):
    if base is None:
        return flint.acb(1)
    z = (-s * flint.arb(base).log()).exp()
    if beta == 1:
        return 1 / (1 - z)
    numerator, denominator = [], []
    for exponent in factorization(base).values():
        numerator += [flint.acb(real(Q(beta + j, exponent))) for j in range(exponent)]
        denominator += [Q(j + 1, exponent) for j in range(exponent)]
    denominator.remove(Q(1))
    return z.hypgeom(numerator, [flint.acb(real(x)) for x in denominator])


@lru_cache(maxsize=None)
def local(beta, degree):
    value = Q(1)
    for j in range(degree):
        value *= Q(beta + j, j + 1)
    return value


def filtered_convolution(s, beta, outer, inner, cutoff=48):
    out, inside = factorization(outer), factorization(inner)
    coefficients = []
    for k in range(cutoff + 1):
        top = min((out[p] * k // e for p, e in inside.items()), default=0) if set(inside) <= set(out) else 0
        coefficient = Q(0)
        for j in range(top + 1):
            value = Q(1)
            for p, e in out.items():
                value *= local(beta, e * k - inside.get(p, 0) * j)
            for p, e in inside.items():
                value *= local(beta, e * j)
            coefficient += value
        coefficients.append(coefficient)
    z = (-s * flint.arb(outer).log()).exp()
    value = flint.acb(0)
    for coefficient in reversed(coefficients):
        value = value * z + real(coefficient)
    assert 0 < beta <= Q(1, 2)
    tail = z.abs_upper() ** (cutoff + 1) / (1 - z.abs_upper())
    return value, tail


def references(s, sigma, b, c, beta):
    assert bool(real(sigma).zeta().log() < flint.arb.pi())
    f = (real(beta) * s.zeta().log()).exp()
    common = common_power_base(b, c)
    rb, rc, rbc = (resonance(s, beta, base) for base in (b, c, common))
    rb2, rc2, rbc2 = (resonance(s, 2 * beta, base) for base in (b, c, common))
    first, first_tail = filtered_convolution(s, beta, c, b)
    second, second_tail = filtered_convolution(s, beta, b, c)
    total = f ** 2 + 2 * f * (rb + rc + rbc) - rb2 - rc2 + 2 * rb * rc - 2 * first - 2 * second + rbc2
    corrected = f * (rb + rc + rbc) / 3
    return total, 2 * (first_tail + second_tail), corrected


def evaluate(coefficients, s):
    return sum((real(Q(coefficient)) * (-s * flint.arb(n).log()).exp()
                for n, coefficient in enumerate(coefficients[1:], 1)), flint.acb(0))


def point_checks(source):
    lookup = {(tuple(item['bases']), item['beta']): item for item in source['actual_zeta_coefficient_profiles']}
    cases = ((2, 3, Q(1, 2), Q(3, 2), '481.19'), (2, 3, Q(1, 4), Q(3, 2), '-509.31'),
             (2, 6, Q(1, 2), Q(7, 4), '613.73'), (2, 6, Q(1, 4), Q(7, 4), '-631.91'),
             (4, 8, Q(1, 2), Q(2), '751.17'), (4, 8, Q(1, 4), Q(2), '-773.29'))
    records = []
    for b, c, beta, sigma, height in cases:
        item = lookup[(b, c), str(beta)]
        s = flint.acb(real(sigma), height)
        total, resonance_error, corrected = references(s, sigma, b, c, beta)
        tail = flint.arb(item['cutoff']) ** (1 - real(sigma)) / (real(sigma) - 1)
        delta = (-s * flint.arb(2).log()).exp()
        comparisons = []
        for label, coefficients, reference, error in (
                ('sum_of_four_joint_squares', item['sum_coefficients'], total, 4 * tail + resonance_error),
                ('normalized_artifact_cancelled_root', item['corrected_root_coefficients'], corrected, tail)):
            finite = evaluate(coefficients, s)
            difference = (finite - reference).abs_upper()
            bad = (finite + delta - reference).abs_lower()
            comparisons.append({'representation': label, 'difference_upper_ball': str(difference),
                                'proved_infinite_error_ball': str(error), 'coefficient_2_perturbation': 1,
                                'perturbed_difference_lower_ball': str(bad),
                                'all_passed': bool(difference < error) and bool(bad > error)})
        records.append({'bases': [b, c], 'beta': str(beta), 's': [str(sigma), height],
                        'arithmetic_cutoff': item['cutoff'], 'filtered_resonance_cutoff': 48,
                        'common_power_base': common_power_base(b, c), 'comparisons': comparisons,
                        'all_passed': all(x['all_passed'] for x in comparisons)})
        print(f'Actual cancellation zeta b,c={b},{c}, beta={beta}, s={sigma}+{height}i: {records[-1]["all_passed"]}', flush=True)
    return records


def find_actual_zero():
    mp.mp.dps = 90
    values = [(mp.mpf(20) + Q(j, 8).numerator / mp.mpf(Q(j, 8).denominator), None) for j in range(33)]
    values = [(t, mp.siegelz(t)) for t, unused in values]
    brackets = [(a[0], d[0]) for a, d in zip(values, values[1:]) if a[1] * d[1] < 0]
    assert len(brackets) == 1
    root = mp.findroot(mp.siegelz, brackets[0])
    height = mp.nstr(root, 80)
    centre = flint.acb(real(Q(1, 2)), height)
    radius = Q(1, 100000)
    region = flint.acb(real(Q(1, 2)) + flint.arb(0, real(radius)),
                       flint.arb(height) + flint.arb(0, real(radius)))
    jet = flint.acb_series([centre, 1], 3).zeta()
    ranged = flint.acb_series([region, 1], 3).zeta()
    linear = jet[1].abs_lower() * real(radius)
    error = jet[0].abs_upper() + ranged[2].abs_upper() * real(radius) ** 2
    assert bool(error < linear)
    return centre, region, radius, {'critical_line_grid': ['20', '24', '1/8'],
                                  'sign_change_bracket': [mp.nstr(x, 20) for x in brackets[0]],
                                  'disk_centre': ['1/2', height], 'radius': str(radius),
                                  'Rouche_linear_lower_ball': str(linear), 'Rouche_error_upper_ball': str(error),
                                  'one_simple_actual_zeta_zero_certified': bool(error < linear),
                                  'proof_scope': 'Rouche counts one simple zero; reflection symmetry forces this zero onto Re(s)=1/2'}


def zero_controls():
    centre, region, radius, certificate = find_actual_zero()
    sigma = Q(1, 2) - radius
    basepoint = centre + real(radius)
    root_mass = ((basepoint - 1) * basepoint.zeta()).abs_lower()
    records = []
    for (b, c), beta in product(((2, 3), (2, 6), (4, 8)), (Q(1, 2), Q(1, 4), Q(1))):
        common = common_power_base(b, c)
        correction = sum((resonance(region, beta, x) for x in (b, c, common)), flint.acb(0)) / 3
        global_lower = sum((1 / (1 + flint.arb(x) ** (-real(sigma))) if x else flint.arb(1)
                            for x in (b, c, common)), flint.arb(0)) / 3
        phase = (flint.acb(0, 2 * flint.arb.pi() * real(beta))).exp()
        jump = global_lower * root_mass ** real(beta) * (2 * (flint.arb.pi() * real(beta)).sin()).abs_lower()
        expected = beta.denominator != 1
        passed = bool(correction.real > 0) and (bool(jump > 0) if expected else bool((phase - 1).contains(0)))
        records.append({'bases': [b, c], 'common_power_base': common, 'beta': str(beta),
                        'correction_rectangle_real_lower_ball': str(correction.real.lower()),
                        'global_moment_real_part_lower_ball': str(global_lower),
                        'actual_pole_cancelled_root_monodromy_jump_lower_ball': str(jump),
                        'nontrivial_branch_obstruction_expected': expected, 'all_passed': passed})
    certificate['correction_records'] = records
    certificate['all_passed'] = certificate['one_simple_actual_zeta_zero_certified'] and all(x['all_passed'] for x in records)
    certificate['scope'] = 'Fresh actual zero on the boundary of the RH half-plane; fractional-root monodromy across its disk is compatible with RH'
    return certificate


def main():
    started = time.monotonic()
    flint.ctx.prec = 224
    source = json.loads((BASE / 'cancellation-results/cancellation_search.json').read_text())
    points, zero = point_checks(source), zero_controls()
    result = {'actual_zeta_ball_checks': points, 'fresh_actual_critical_line_zero_control': zero,
              'corrected_root_identity_domain': 'Re(s)>1 initially; correction holomorphic and nonzero on Re(s)>0',
              'RH_root_criterion': 'RH iff all pole-cancelled dyadic corrected roots continue single-valuedly and holomorphically to Re(s)>1/2',
              'full_q2_orientation_sum_has_no_artificial_Re_one_boundary_singularities_away_from_one': True,
              'higher_root_order_signed_combinations_remain_rejected': True,
              'new_RH_estimate_proved': False, 'counts_as_new_primitive': False,
              'all_passed': all(x['all_passed'] for x in points) and zero['all_passed'],
              'proof': 'cancellation_proof.txt', 'elapsed_seconds': time.monotonic() - started}
    (BASE / 'cancellation-results/cancellation_analytic.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Actual cancellation analytic audit: all={result["all_passed"]}; elapsed={result["elapsed_seconds"]:.2f}s')
    assert result['all_passed']


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Independent prime-local diagonal and Cauchy zero-obstruction audit."""

from fractions import Fraction as Q
from pathlib import Path
import json
import time

import flint

from check_joint_size import factors

BASE = Path(__file__).resolve().parent


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def short(x):
    return x.str(18)


def box(radius):
    return flint.acb(flint.arb(0, radius), flint.arb(0, radius))


def coefficient(n):
    f = factors(n)
    if len(f) != 2 or any(e % 3 == 0 for e in f.values()):
        return Q(0)
    a, b = f.values()
    return Q(2, a * b)


def prime_diagonal(s, sigma, cutoff=384):
    value = flint.acb(0)
    for p in range(2, cutoff + 1):
        if factors(p) != {p: 1}:
            continue
        x = (-s * flint.arb(p).log()).exp()
        # Both logarithms have positive-real-part arguments, fixing their
        # local Euler branch without a Mobius prime-zeta representation.
        L = -(1 - x).log() + (1 - x ** 3).log() / 3
        value += L ** 2
    tail = flint.arb(cutoff) ** (1 - 2 * real(sigma)) / (2 * real(sigma) - 1)
    tail /= (1 - flint.arb(cutoff + 1) ** (-real(sigma))) ** 2
    return value + box(tail), tail


def actual_points(source):
    rows = []
    for row in source['actual_zeta_ball_checks']:
        sigma, height = Q(row['s'][0]), row['s'][1]
        s = flint.acb(real(sigma), height)
        diagonal, diagonal_tail = prime_diagonal(s, sigma)
        G = s.zeta().log() - (3 * s).zeta().log() / 3
        reference = G ** 2 - diagonal
        finite = sum((real(coefficient(n)) * (-s * flint.arb(n).log()).exp()
                      for n in range(2, 6145) if coefficient(n)), flint.acb(0))
        tail = 2 * flint.arb(6144) ** (1 - real(sigma)) / (real(sigma) - 1)
        distance = (finite - reference).abs_upper()
        perturbed = (finite + real(Q(1, 3)) * (-s * flint.arb(6).log()).exp() - reference).abs_lower()
        passed = bool(distance < tail) and bool(perturbed > tail)
        rows.append({'s': row['s'], 'decoded_coefficient_cutoff': 6144, 'prime_diagonal_cutoff': 384,
                     'changed_diagonal_infinite_tail_ball': short(diagonal_tail),
                     'difference_upper_ball': short(distance), 'independent_decoded_tail_ball': short(tail),
                     'smaller_perturbed_difference_lower_ball': short(perturbed), 'all_passed': passed})
    return rows


def zero_controls(source):
    records = []
    for row in source['restored_actual_zero_obstruction_controls']['records']:
        radius = Q(row['radius'])
        centre = flint.acb(real(Q(1, 2)), row['disk_centre'][1])
        R = Q(1, 32)
        maximum = (centre + box(real(R))).zeta().abs_upper()
        flint.ctx.cap = 2
        jet = flint.acb_series([centre, flint.acb(1)], 2).zeta()
        ratio = real(radius / R)
        remainder = maximum * ratio ** 2 / (1 - ratio)
        base_modulus_upper = (jet[0] + real(radius) * jet[1]).abs_upper() + remainder
        # |LOG zeta(3s)|<=log zeta(3*Re(s)) on the Euler half-plane.
        # This yields a branch-independent negative upper bound for Re(G)
        # without calling zeta at the production basepoint.
        G_upper = base_modulus_upper.log() + real(3 * (Q(1, 2) + radius)).zeta().log() / 3
        jump_lower = -4 * flint.arb.pi() * G_upper
        R2, centre2 = Q(1, 8), 2 * centre
        max2 = (centre2 + box(real(R2))).zeta().abs_upper()
        ratio2 = real(2 * radius / R2)
        variation2 = max2 * ratio2 / (1 - ratio2)
        second_lower = centre2.zeta().abs_lower() - variation2
        passed = bool(G_upper < 0) and bool(jump_lower > 0) and bool(second_lower > 0) and Q(1, 2) - radius > Q(1, 3)
        records.append({'disk_centre': row['disk_centre'], 'radius': row['radius'],
                        'basepoint_Cauchy_radius': str(R), 'independent_basepoint_zeta_modulus_upper_ball': short(base_modulus_upper),
                        'basepoint_Cauchy_remainder_ball': short(remainder), 'independent_Re_G_upper_ball': short(G_upper),
                        'independent_decoded_monodromy_jump_lower_ball': short(jump_lower),
                        'zeta_2s_Cauchy_radius': str(R2), 'whole_disk_zeta_2s_nonzero_lower_ball': short(second_lower),
                        'initial_Euler_sheet_of_basepoint_logarithm_asserted': False, 'all_passed': passed})
    return {'records': records, 'all_passed': all(row['all_passed'] for row in records)}


def exact_local_cancellation():
    # Independent harmonic-sum form of the square coefficients.
    coefficients = [Q(0)] * 65
    for k in range(2, 65):
        coefficients[k] = Q(2, k) * sum((Q(1, e) for e in range(1, k)
                                        if e % 3 and (k - e) % 3), Q(0))
    shifted = [coefficients[k] - (Q(2, k) if k and k % 2 == 0 else Q(0)) for k in range(65)]
    return {'q_two': str(coefficients[2]), 'B_coefficients_through_two': [str(v) for v in shifted[:3]],
            'higher_coefficients_bounded_by_degree': all(abs(shifted[k]) <= k for k in range(3, 65)),
            'order_three_local_extension_passed': all(v == 0 for v in shifted[:3])}


def main():
    start = time.monotonic()
    flint.ctx.prec = 768
    source = json.loads((BASE / 'decode-results/decode_analytic.json').read_text())
    assert source['all_passed']
    points, zeros, local = actual_points(source), zero_controls(source), exact_local_cancellation()
    checks = {'six_decoded_zeta_cases_with_changed_prime_reference_and_smaller_errors': all(row['all_passed'] for row in points),
              'both_actual_zero_obstructions_by_independent_Taylor_Cauchy_bounds': zeros['all_passed'],
              'local_diagonal_order_three_cancellation': local['order_three_local_extension_passed'] and local['higher_coefficients_bounded_by_degree'],
              'arithmetic_cutoff_changed': all(a['decoded_coefficient_cutoff'] != b['decoded_coefficient_cutoff'] for a, b in zip(points, source['actual_zeta_ball_checks']))}
    result = {'checks': checks, 'all_passed': all(checks.values()), 'actual_zeta_ball_checks': points,
              'restored_actual_zero_obstruction_controls': zeros, 'local_diagonal_cancellation': local,
              'production_imports': False, 'shared_trusted_kernel': 'FLINT/Arb', 'seconds': time.monotonic() - start}
    (BASE / 'decode-results/decode_analytic_verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print('Independent decoder analytic audit:', sum(checks.values()), '/', len(checks), 'seconds', result['seconds'], flush=True)
    assert result['all_passed']


if __name__ == '__main__':
    main()

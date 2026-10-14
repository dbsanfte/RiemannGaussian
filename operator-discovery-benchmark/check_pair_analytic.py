#!/usr/bin/env python3
"""Independent arithmetic double sums and full-disk nonlinear-pair audit."""

from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json
import time

import flint

from check_pair import apply
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
    fs = factors(n)
    return Q(1, list(fs.values())[0]) if len(fs) == 1 else Q(0)


def square_sum(s, sigma, cutoff=80):
    # Output-index grouping, independent of the production Mellin integral
    # and of its input-pair enumeration.
    grouped = {}
    values = [(n, coefficient(n)) for n in range(2, cutoff + 1) if coefficient(n)]
    for x, v in values:
        for y, w in values:
            image = (x + y) ** 3 * x * y
            grouped[image] = grouped.get(image, Q(0)) + v * w
    finite = sum((real(v) * (-s * flint.arb(n).log()).exp() for n, v in grouped.items()), flint.acb(0))
    a = real(5 * sigma / 2)
    # Changed tail: compute the exact weighted prefix of LOG zeta and
    # enclose its remaining positive series by native subtraction.
    prefix = sum((real(v) / flint.arb(n) ** a for n, v in values), flint.arb(0))
    total = a.zeta().log()
    residual = (total - prefix).abs_upper()
    tail = flint.arb(8) ** (-real(sigma)) * (2 * prefix * residual + residual ** 2)
    return finite, tail


@lru_cache(maxsize=None)
def arithmetic_profile(beta, family):
    return apply([Q(0)] + [Q(1)] * 6144, beta=beta, family=family)


def actual_points(source):
    records = []
    # The independent correction norm replaces log zeta by zeta-1.
    norm = (real(Q(5, 2)).zeta() - 1) ** 2 / 8
    for row in source['actual_zeta_ball_checks']:
        sigma, height = Q(row['s'][0]), row['s'][1]
        beta, family = Q(row['beta']), row['family']
        c = beta * beta if family == 'input' else beta
        s = flint.acb(real(sigma), height)
        direct, kernel_tail = square_sum(s, sigma)
        reference = (real(beta) * s.zeta().log() + real(c) * (direct + box(kernel_tail))).exp()
        finite = sum((real(v) * (-s * flint.arb(n).log()).exp()
                      for n, v in enumerate(arithmetic_profile(beta, family)[1:], 1) if v), flint.acb(0))
        tail = (1 + 1 / (real(sigma) - 1)) * flint.arb(6144) ** (1 - real(sigma)) * (real(c) * norm).exp()
        distance = (finite - reference).abs_upper()
        wrong = (finite + real(Q(1, 3)) * (-s * flint.arb(2).log()).exp() - reference).abs_lower()
        # Smaller first-kernel-coefficient perturbation is separately
        # tested against the direct square-sum infinite tail.
        kernel_wrong = real(Q(1, 5)) * flint.arb(256) ** (-real(sigma))
        kernel_check = bool(kernel_wrong > 2 * kernel_tail)
        records.append({'beta': str(beta), 'family': family, 'correction_amplitude': str(c), 's': row['s'],
                        'arithmetic_cutoff': 6144, 'prime_power_square_cutoff': 80,
                        'reference': 'One native zeta value times exponent of an independent grouped prime-power double sum',
                        'difference_upper_ball': short(distance), 'independent_full_coefficient_tail_ball': short(tail),
                        'smaller_perturbed_difference_lower_ball': short(wrong),
                        'independent_kernel_infinite_tail_ball': short(kernel_tail),
                        'smaller_kernel_perturbation_modulus_ball': short(kernel_wrong),
                        'all_passed': bool(distance < tail) and bool(wrong > tail) and kernel_check})
        print('Independent nonlinear pair zeta case', row['s'], records[-1]['all_passed'], flush=True)
    return records


def actual_zeros(source):
    records = []
    for row in source['existing_actual_zero_new_operator_controls']['records']:
        sigma = Q(1, 2) - Q(row['radius'])
        height = row['disk_centre'][1]
        centre = flint.acb(real(Q(1, 2)), height)
        finite, tail = square_sum(centre, Q(1, 2), cutoff=96)
        # The saved printed balls include their rounding error. Compare
        # them to a separate convergent arithmetic enclosure, while the
        # whole-disk zero-free certificate uses a different majorant.
        native = flint.acb(*(flint.arb(v) for v in row['centre_native_correction_components']))
        centre_distance = (native - finite).abs_upper()
        uniform = (real(5 * sigma / 2).zeta() - 1) ** 2 / flint.arb(8) ** real(sigma)
        roots = []
        for family in ('input', 'output'):
            for beta, phase in ((Q(1, 2), flint.arb(2)), (Q(1, 4), flint.arb(2).sqrt()), (Q(1), flint.arb(0))):
                c = beta * beta if family == 'input' else beta
                lower = (-real(c) * uniform).exp()
                jump = phase * lower
                roots.append({'beta': str(beta), 'family': family, 'correction_amplitude': str(c),
                              'independent_whole_disk_correction_lower_ball': short(lower),
                              'independent_monodromy_factor_lower_ball': short(jump),
                              'all_passed': bool(lower > 0) and (bool(jump > 0) if beta != 1 else jump.is_zero())})
        assert row['centre_native_correction_ball'] != 'nan + nanj'
        records.append({'disk_centre': row['disk_centre'], 'radius': row['radius'],
                        'prime_power_square_cutoff': 96, 'centre_direct_correction_ball': short(finite + box(tail)),
                        'native_centre_comparison_upper_ball': short(centre_distance),
                        'independent_centre_tail_ball': short(tail),
                        'changed_whole_disk_majorant': '8^(-sigma)*(zeta(5*sigma/2)-1)^2',
                        'whole_disk_majorant_ball': short(uniform), 'records': roots,
                        'phase_bound_scope': row['phase_bound_scope'],
                        'all_passed': bool(centre_distance < tail) and all(r['all_passed'] for r in roots)})
    return {'records': records, 'all_passed': all(r['all_passed'] for r in records)}


def kernel_normalization_control(source):
    # Re-check the factor 1/pi using a real positive instance. A native
    # beta integral isolates the classical normalization independently of
    # any zeta routine or production integration code.
    r, x, y, sigma = 3, 2, 3, Q(2)
    A, I = flint.acb(r * real(sigma) / 2), flint.acb(0, 1)
    def integrand(t, analytic):
        z = A + I * t
        return z.gamma() * (r * real(sigma) - z).gamma() / flint.arb(r * real(sigma)).gamma() * (-z * flint.arb(x).log() - (r * real(sigma) - z) * flint.arb(y).log()).exp()
    finite = flint.acb.integral(integrand, -24, 24, abs_tol=flint.arb('1e-42'), rel_tol=flint.arb('1e-42')) / (2 * flint.arb.pi())
    # Both gamma factors are at real part 3, so recurrence from Gamma(1+it)
    # gives an exact degree-five polynomial exponential envelope.
    from math import comb, factorial
    pi, p, T, b = flint.arb.pi(), 5, 24, 3
    tail = flint.arb(6) ** (-real(3)) / flint.arb(6).gamma() * (2 / (1 - (-2 * pi).exp()))
    tail *= (-pi * T).exp() * sum((comb(p, j) * flint.arb(T + b) ** (p - j) * factorial(j) / pi ** (j + 1) for j in range(p + 1)), flint.arb(0))
    expected = flint.arb(x + y) ** (-r * real(sigma))
    distance, wrong = (finite - expected).abs_upper(), (2 * finite - expected).abs_lower()
    return {'test_pair': [x, y], 's': '2', 'Mellin_beta_integral_ball': short(finite), 'expected_kernel_ball': short(expected),
            'proved_contour_tail_ball': short(tail), 'correct_distance_upper_ball': short(distance),
            'wrong_normalization_distance_lower_ball': short(wrong),
            'all_passed': bool(distance < tail) and bool(wrong > tail)}


def main():
    start = time.monotonic()
    flint.ctx.prec = 384
    source = json.loads((BASE / 'pair-results/pair_analytic.json').read_text())
    assert source['all_passed']
    points, zeros, normalization = actual_points(source), actual_zeros(source), kernel_normalization_control(source)
    phase = flint.acb(0, 2 * flint.arb.pi())
    ell = flint.acb(real(Q(1, 3)), real(Q(1, 7)))
    ratio = ((ell + phase) ** 2 - ell ** 2).exp()
    checks = {'six_zeta_bridges_changed_cutoffs_and_smaller_perturbations': all(r['all_passed'] for r in points),
              'whole_disk_ordinary_root_controls_with_changed_majorant': zeros['all_passed'],
              'independent_beta_Mellin_integral_normalization': normalization['all_passed'],
              'known_r_zero_root_blind_monodromy_rejected': bool((ratio - 1).abs_lower() > 0),
              'all_arithmetic_and_pair_cutoffs_changed': all(a['arithmetic_cutoff'] != b['arithmetic_cutoff'] and a['prime_power_square_cutoff'] != b['direct_prime_power_cutoff'] for a, b in zip(points, source['actual_zeta_ball_checks']))}
    result = {'checks': checks, 'all_passed': all(checks.values()), 'actual_zeta_ball_checks': points,
              'existing_actual_zero_new_operator_controls': zeros, 'independent_kernel_normalization_control': normalization,
              'production_imports': False, 'shared_trusted_kernel': 'FLINT/Arb 0.9.0',
              'elapsed_seconds': time.monotonic() - start}
    (BASE / 'pair-results/pair_analytic_verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print('Independent nonlinear pair analytic audit:', sum(checks.values()), '/', len(checks), 'seconds', result['elapsed_seconds'], flush=True)
    assert result['all_passed']


if __name__ == '__main__':
    main()

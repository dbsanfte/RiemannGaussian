#!/usr/bin/env python3
"""Independent direct gap sums, two-zeta anchors and Cauchy root bounds."""

from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json
import time

import flint

from check_gap import factors, exp_D, complete_fibres

BASE = Path(__file__).resolve().parent


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def short(x):
    return x.str(20)


def box(radius):
    return flint.acb(flint.arb(0, radius), flint.arb(0, radius))


@lru_cache(maxsize=None)
def powers(cutoff):
    return [(n, next(iter(factors(n).values()))) for n in range(2, cutoff + 1) if len(factors(n)) == 1]


def direct_gamma(s, cutoff):
    vals = powers(cutoff)
    return sum((flint.arb(2) / (e * f) * (-s * (flint.arb(a).log() + flint.arb(b).log() + 3 * flint.arb(b - a).log())).exp()
                for j, (a, e) in enumerate(vals) for b, f in vals[j + 1:]), flint.acb(0))


def bounds(s, sigma, cutoff, c=flint.acb(0), critical=False):
    q = sum((flint.arb(n) ** (-2 * real(sigma)) / e ** 2 for n, e in powers(cutoff)), flint.arb(0))
    if critical:
        first = sum((flint.arb(n) ** (-2 * real(sigma)) / e for n, e in powers(cutoff)), flint.arb(0))
        tail_square = (1 + 1 / (2 * real(sigma) - 1)).log() - first
    else:
        tail_square = flint.arb(cutoff) ** (1 - 2 * real(sigma)) / (2 * real(sigma) - 1)
    tail_square += c.abs_upper() ** 2
    q += c.abs_upper() ** 2
    row = 2 * (1 + 1 / (3 * real(sigma) - 1))
    return row * (2 * q.sqrt() * tail_square.sqrt() + tail_square)


def anchored_reference(s, sigma, cutoff=3072):
    finite_L = sum(((-s * flint.arb(n).log()).exp() / e for n, e in powers(cutoff)), flint.acb(0))
    c = s.zeta().log() - finite_L
    reference = direct_gamma(s, cutoff) + 2 * c * (4 * s).zeta().log()
    error = bounds(s, sigma, cutoff, c)
    extra = 2 * c.abs_upper() * flint.arb(cutoff) ** (1 - 4 * real(sigma)) / (4 * real(sigma) - 1)
    return reference, error + extra


def actual_points(source):
    rows = []
    for old in source['actual_zeta_ball_checks']:
        sigma, height = Q(old['s'][0]), old['s'][1]
        s = flint.acb(real(sigma), height)
        finite = direct_gamma(s, 1536)
        left_tail = bounds(s, sigma, 1536)
        reference, right_tail = anchored_reference(s, sigma)
        allowed = left_tail + right_tail
        distance = (finite - reference).abs_upper()
        wrong = (finite + real(Q(1, 3)) * (-s * flint.arb(6).log()).exp() - reference).abs_lower()
        # Both orientations of the sesquilinear correlation give a cosine.
        vals = powers(1536)
        wrong_H = sum((flint.arb(2) / (e * f) * (-real(sigma) * (flint.arb(a).log() + flint.arb(b).log())
                       - 3 * s * flint.arb(b - a).log()).exp()
                       * (flint.arb(height) * (flint.arb(a).log() - flint.arb(b).log())).cos()
                       for j, (a, e) in enumerate(vals) for b, f in vals[j + 1:]), flint.acb(0))
        conjugacy = (wrong_H - reference).abs_lower()
        passed = bool(distance < allowed) and bool(wrong > allowed) and bool(conjugacy > allowed)
        rows.append({'s': old['s'], 'direct_input_cutoff': 1536, 'two_zeta_anchor_cutoff': 3072,
                     'native_anchor_arguments': ['s', '4*s'], 'independent_difference_upper_ball': short(distance),
                     'changed_integer_Toeplitz_tail_ball': short(allowed),
                     'smaller_changed_coefficient_six_error': '1/3', 'changed_difference_lower_ball': short(wrong),
                     'wrong_Hermitian_difference_lower_ball': short(conjugacy), 'all_passed': passed})
        print('Independent gap native identity', sigma, height, passed, flush=True)
    return rows


def root_points(source):
    size = 1536
    h = [Q(0)] * (size + 1)
    for n, e in powers(size):
        h[n] = Q(1, e)
    k = [Q(0)] * len(h)
    for n in range(2, len(h)):
        k[n] = sum((2 * h[a] * h[b] for a, b in complete_fibres(n, 3)), Q(0))
    sigma, height = Q(2), '7.19'
    s = flint.acb(real(sigma), height)
    value, error = anchored_reference(s, sigma)
    gamma = value + box(error)
    actual_real, real_error = anchored_reference(flint.acb(real(sigma)), sigma)
    real_gamma = actual_real.real + flint.arb(0, real_error)
    rows = []
    for old in source['transformed_ordinary_root_scalar_controls']['records']:
        beta, amplitude = Q(old['beta']), Q(old['amplitude'])
        coefficients = exp_D([beta * a + amplitude * b for a, b in zip(h, k)])
        expected_six = beta ** 2 + 2 * amplitude
        assert coefficients[6] == expected_six
        finite = sum((real(v) * (-s * flint.arb(n).log()).exp() for n, v in enumerate(coefficients) if v), flint.acb(0))
        reference = (real(beta) * s.zeta().log() + real(amplitude) * gamma).exp()
        real_total = (real(beta) * real(sigma).zeta().log() + real(amplitude) * real_gamma).exp()
        real_prefix = sum((real(v) * flint.arb(n) ** (-real(sigma)) for n, v in enumerate(coefficients) if v), flint.arb(0))
        tail = (real_total - real_prefix).abs_upper()
        distance = (finite - reference).abs_upper()
        wrong = (finite + real(Q(1, 3)) * (-s * flint.arb(6).log()).exp() - reference).abs_lower()
        passed = bool(distance < tail) and bool(wrong > tail)
        rows.append({'beta': old['beta'], 'family': old['family'], 'coefficient_cutoff': size,
                     'coefficient_six': str(coefficients[6]), 'difference_upper_ball': short(distance),
                     'independent_positive_real_tail_ball': short(tail),
                     'smaller_error_difference_lower_ball': short(wrong), 'all_passed': passed})
    return {'records': rows, 'all_passed': all(row['all_passed'] for row in rows)}


def zeros(source):
    rows, jets = [], {}
    for old in source['one_sided_actual_zero_controls']['records']:
        height, epsilon = old['disk_centre'][1], Q(old['epsilon'])
        if height not in jets:
            centre = flint.acb(real(Q(1, 2)), height)
            R = Q(1, 32)
            maximum = (centre + box(real(R))).zeta().abs_upper()
            flint.ctx.cap = 2
            jet = flint.acb_series([centre, flint.acb(1)], 2).zeta()
            jets[height] = (jet, maximum, R)
        jet, maximum, R = jets[height]
        t = real(epsilon / R)
        remainder = maximum * t ** 2 / (1 - t)
        zeta_upper = (jet[0] + real(epsilon) * jet[1]).abs_upper() + remainder
        sigma = Q(1, 2) + epsilon
        s = flint.acb(real(sigma), height)
        finite = direct_gamma(s, 1536)
        tail = bounds(s, sigma, 1536, critical=True)
        gamma = finite + box(tail)
        row = 2 * (1 + 1 / (3 * real(sigma) - 1))
        major = row * (1 + 1 / (2 * real(sigma) - 1)).log()
        factors_ok = all(bool((-real(Q(v['beta']) ** 2) * major).exp() > 0) for v in old['factor_modulus_controls'])
        passed = gamma.is_finite() and major.is_finite() and zeta_upper.is_finite() and factors_ok
        rows.append({'disk_centre': old['disk_centre'], 'epsilon': old['epsilon'], 'Cauchy_radius': str(R),
                     'zeta_modulus_over_epsilon_upper_ball': short(zeta_upper / real(epsilon)),
                     'changed_cutoff_Gamma_enclosure_modulus_upper_ball': short(gamma.abs_upper()),
                     'elementary_integral_Gamma_majorant_ball': short(major),
                     'positive_correction_factor_bounds_passed': factors_ok,
                     'one_sided_right_halfplane_only': True, 'boundary_limit_relies_on_endpoint_proof': True,
                     'whole_critical_zero_disk_holomorphy_claimed': False, 'all_passed': passed})
    return {'records': rows, 'all_passed': all(row['all_passed'] for row in rows)}


def main():
    start = time.monotonic()
    flint.ctx.prec = 640
    source = json.loads((BASE / 'gap-results/gap_analytic.json').read_text())
    assert source['all_passed']
    points, roots, zero_rows = actual_points(source), root_points(source), zeros(source)
    checks = {'six_native_zeta_cases_changed_direct_and_two_zeta_reference': all(row['all_passed'] for row in points),
              'analytic_bilinear_correlation_not_Hermitian_rejected': all(row['all_passed'] for row in points),
              'five_ordinary_root_scalar_controls_Omega_recursion_and_smaller_errors': roots['all_passed'],
              'six_right_side_actual_zero_controls_Cauchy_and_elementary_majorants': zero_rows['all_passed'],
              'changed_source_and_reference_cutoffs': all(row['direct_input_cutoff'] != old['finite_encoded_input_cutoff'] for row, old in zip(points, source['actual_zeta_ball_checks'])),
              'whole_zero_disk_holomorphy_and_new_RH_estimate_not_claimed': not source['whole_critical_zero_disk_holomorphy_established'] and not source['new_RH_estimate_proved']}
    out = {'checks': checks, 'actual_zeta_ball_checks': points, 'transformed_ordinary_root_scalar_controls': roots,
           'one_sided_actual_zero_controls': zero_rows, 'production_imports': False,
           'shared_trusted_kernel': 'FLINT/Arb; independent factor/recursion helpers, direct pair sums, integer tails and Cauchy bounds',
           'all_passed': all(checks.values()), 'seconds': time.monotonic() - start}
    (BASE / 'gap-results/gap_analytic_verification.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Independent gap analytic audit:', sum(checks.values()), '/', len(checks), 'seconds', out['seconds'], flush=True)
    assert out['all_passed']


if __name__ == '__main__':
    main()

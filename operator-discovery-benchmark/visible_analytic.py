#!/usr/bin/env python3
"""Certified native-zeta identities for the residue-visible product decoder."""

from fractions import Fraction as Q
from pathlib import Path
import json
import time

import flint

from exact_arithmetic import factorization
from visible_search import local_coefficients

BASE = Path(__file__).resolve().parent


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def short(x):
    return x.str(20)


def box(radius):
    return flint.acb(flint.arb(0, radius), flint.arb(0, radius))


def mobius(n):
    fs = factorization(n)
    return 0 if any(e > 1 for e in fs.values()) else (-1) ** len(fs)


def native_prime_zeta(s, sigma, cutoff=24):
    assert sigma > 1
    value = sum((real(Q(mobius(m), m)) * (m * s).zeta().log()
                 for m in range(1, cutoff + 1) if mobius(m)), flint.acb(0))
    t = flint.arb(2) ** (-real(sigma))
    tail = t ** (cutoff + 1) / ((cutoff + 1) * (1 - t))
    tail *= 1 + 2 / ((cutoff + 1) * real(sigma) - 1)
    return value + box(tail), tail


def native_remainder(s, sigma, r=3, degree=64, mobius_cutoff=24):
    assert r * sigma > 1
    cs = local_coefficients(r, degree)
    value, mobius_tail = flint.acb(0), flint.arb(0)
    for k in range(r, degree + 1):
        if cs[k]:
            P, tail = native_prime_zeta(k * s, k * sigma, mobius_cutoff)
            value += real(cs[k]) * P
            mobius_tail += abs(real(cs[k])) * tail
    t = flint.arb(2) ** (-real(sigma))
    tail = t ** (degree + 1) / (1 - t)
    tail *= 1 + 2 / ((degree + 1) * real(sigma) - 1)
    return value + box(tail), {'r': r, 'local_degree': degree, 'Mobius_cutoff': mobius_cutoff,
                              'total_Mobius_error_ball': short(mobius_tail),
                              'local_degree_infinite_tail_ball': short(tail)}


def local_root_filter(x, r):
    h = -(1 - x).log()
    mean = flint.acb(0)
    for j in range(r):
        omega = flint.acb(0, 2 * flint.arb.pi() * j / r).exp()
        mean += (-(1 - omega * x).log()) ** 2 / r
    J = h ** 2 - mean
    H = h + (1 - x ** r).log() / r
    return J - H ** 2


def root_filter_remainder(s, sigma, cutoff=2048, r=3, leading_subtraction=False):
    value = flint.acb(0)
    c = local_coefficients(r, r)[r]
    for p in range(2, cutoff + 1):
        if not flint.fmpz(p).is_prime():
            continue
        x = (-s * flint.arb(p).log()).exp()
        value += local_root_filter(x, r) - (real(c) * x ** r if leading_subtraction else 0)
    if leading_subtraction:
        P, _ = native_prime_zeta(r * s, r * sigma, 32)
        value += real(c) * P
    exponent = (r + bool(leading_subtraction)) * sigma
    assert exponent > 1
    tail = flint.arb(cutoff) ** (1 - real(exponent)) / (real(exponent) - 1)
    tail /= 1 - flint.arb(cutoff + 1) ** (-real(sigma))
    return value, tail


def actual_points(source):
    profile = next(row for row in source['zeta_profiles'] if row['r'] == 3)
    values = list(map(Q, profile['decoded_coefficients']))
    cutoff = profile['decoded_cutoff']
    cases = ((Q(5, 3), '3.71'), (Q(2), '-5.83'), (Q(7, 3), '8.17'),
             (Q(5, 3), '-10.97'), (Q(2), '13.13'), (Q(7, 3), '-15.83'))
    rows = []
    for sigma, height in cases:
        s = flint.acb(real(sigma), height)
        R, info = native_remainder(s, sigma)
        G = s.zeta().log() - (3 * s).zeta().log() / 3
        reference = G ** 2 + R
        finite = sum((real(v) * (-s * flint.arb(n).log()).exp()
                      for n, v in enumerate(values) if v), flint.acb(0))
        tail = 2 * flint.arb(cutoff) ** (1 - real(sigma)) / (real(sigma) - 1)
        distance = (finite - reference).abs_upper()
        wrong = (finite + real(Q(1, 2)) * (-s * flint.arb(4).log()).exp() - reference).abs_lower()
        passed = bool(distance < tail) and bool(wrong > tail)
        rows.append({'s': [str(sigma), height], 'r': 3, 'decoded_cutoff': cutoff,
                     'scalar_formula': '(LOG zeta(s)-LOG zeta(3s)/3)^2+R_3(s)',
                     'native_reference': info, 'difference_upper_ball': short(distance),
                     'decoded_infinite_tail_ball': short(tail),
                     'changed_coefficient_four_error': '1/2', 'changed_difference_lower_ball': short(wrong),
                     'all_passed': passed})
        print('Visible full native-zeta identity', sigma, height, passed, flush=True)
    return rows


def deep_remainder_points():
    cases = ((Q(3, 8), '1.91'), (Q(2, 5), '-4.29'), (Q(5, 12), '6.71'),
             (Q(3, 8), '-8.53'), (Q(2, 5), '10.91'), (Q(5, 12), '-13.31'))
    rows = []
    for sigma, height in cases:
        s = flint.acb(real(sigma), height)
        R, info = native_remainder(s, sigma)
        local, tail = root_filter_remainder(s, sigma, leading_subtraction=True)
        distance = (local - R).abs_upper()
        wrong = (local + real(Q(1, 2)) * (-s * flint.arb(8).log()).exp() - R).abs_lower()
        passed = bool(distance < tail) and bool(wrong > tail)
        rows.append({'s': [str(sigma), height], 'r': 3, 'correction_only': True,
                     'native_reference': info, 'root_of_unity_prime_cutoff': 2048,
                     'leading_prime_zeta_Mobius_cutoff': 32, 'leading_term_subtracted_before_prime_sum': True,
                     'difference_upper_ball': short(distance), 'residual_prime_infinite_tail_ball': short(tail),
                     'changed_coefficient_eight_error': '1/2', 'changed_difference_lower_ball': short(wrong),
                     'ordinary_decoded_Dirichlet_convergence_here_claimed': False, 'all_passed': passed})
        print('Visible subcritical correction', sigma, height, passed, flush=True)
    return {'records': rows, 'all_passed': all(row['all_passed'] for row in rows)}


def actual_zero_controls():
    rows = []
    certificates = (('size-results/size_analytic_probe.json', 'actual_critical_line_zero_control'),
                    ('cancellation-results/cancellation_analytic.json', 'fresh_actual_critical_line_zero_control'))
    for filename, key in certificates:
        old = json.loads((BASE / filename).read_text())[key]
        assert old['all_passed']
        radius, height = Q(old['radius']), old['disk_centre'][1]
        centre = flint.acb(real(Q(1, 2)), height)
        base, region = centre + real(radius), centre + box(real(radius))
        for r in (3, 4, 5, 7):
            sigma = Q(1, 2) + radius
            real_G = abs(base.zeta()).log() - abs((r * base).zeta()).log() / r
            jump = 4 * flint.arb.pi() * real_G.abs_lower()
            correction, info = native_remainder(region, Q(1, 2) - radius, r)
            log_rs = (r * base).zeta().log()
            anomaly = (-flint.acb(0, 4 * flint.arb.pi()) * log_rs / r).abs_upper()
            anomaly_bound = 4 * flint.arb.pi() / r * real(r * sigma).zeta().log()
            passed = (bool(real_G < 0) and bool(jump > 0) and correction.is_finite()
                      and Q(1, 2) - radius > Q(1, r) and bool(anomaly < anomaly_bound))
            rows.append({'disk_centre': old['disk_centre'], 'radius': old['radius'], 'r': r,
                         'existing_simple_zero_certificate_reused': True,
                         'basepoint_real_part': str(sigma), 'branch_independent_Re_G_ball': short(real_G),
                         'decoded_log_monodromy_jump_lower_ball': short(jump),
                         'whole_disk_correction_modulus_upper_ball': short(correction.abs_upper()),
                         'whole_disk_correction_reference': info,
                         'whole_disk_Re_s_gt_one_over_r': True,
                         'zeta_2s_nonzero_gate_needed': False,
                         'monodromy_difference_from_LOG_zeta_squared': '-4*pi*i*LOG zeta(r*s)/r',
                         'monodromy_difference_upper_ball': short(anomaly),
                         'height_independent_monodromy_difference_bound_ball': short(anomaly_bound),
                         'initial_Euler_sheet_of_LOG_zeta_s_asserted': False,
                         'decoded_single_valued_holomorphy_rejected': passed, 'all_passed': passed})
            print('Visible root obstruction', r, height, passed, flush=True)
    return {'records': rows, 'all_passed': all(row['all_passed'] for row in rows)}


def parameter_limit():
    sigma, height = Q(3, 2), '2.79'
    s = flint.acb(real(sigma), height)
    L, rows = s.zeta().log(), []
    for r in (3, 4, 5, 7, 11, 13):
        R, info = native_remainder(s, sigma, r)
        Lrs = (r * s).zeta().log()
        U = (L - Lrs / r) ** 2 + R
        euler_L = real(r * sigma).zeta().log()
        R_bound = (real(r * sigma).zeta() - 1) / (1 - flint.arb(2) ** (-real(sigma)))
        bound = 2 * L.abs_upper() * euler_L / r + euler_L ** 2 / r ** 2 + R_bound
        actual = (U - L ** 2).abs_upper()
        rows.append({'s': [str(sigma), height], 'r': r, 'native_remainder_reference': info,
                     'difference_from_LOG_zeta_squared_upper_ball': short(actual),
                     'parameter_limit_majorant_ball': short(bound),
                     'compact_limit_requires_a_chosen_zero_free_LOG_zeta_branch': True,
                     'all_passed': bool(actual < bound)})
    return {'records': rows, 'all_passed': all(row['all_passed'] for row in rows)}


def main():
    start = time.monotonic()
    flint.ctx.prec = 512
    source = json.loads((BASE / 'visible-results/visible_search.json').read_text())
    assert source['all_passed']
    points, deep, zeros, limits = actual_points(source), deep_remainder_points(), actual_zero_controls(), parameter_limit()
    # For every native P(k*s) call above, k*Re(s)>=9/8. The bound on
    # the Euler log is below pi, so its principal value is the Euler log.
    branch = bool(real(Q(9, 8)).zeta().log() < flint.arb.pi())
    out = {'actual_zeta_ball_checks': points, 'deep_correction_ball_checks': deep,
           'restored_actual_zero_obstruction_controls': zeros, 'parameter_limit_controls': limits,
           'principal_Euler_log_gate_at_nine_eighths': branch,
           'correction_holomorphic_domain': 'Re(s)>1/r', 'ordinary_decoded_absolute_abscissa': '1',
           'same_prime_diagonal_cancellation_proved': True,
           'full_encoded_endpoint_convergence_proved_by_PNT': True,
           'full_encoded_endpoint_abscissa': '2/(r+2)',
           'pole_cancelled_continuation_is_RH_equivalent': True,
           'new_RH_estimate_proved': False, 'historical_novelty_established': False,
           'all_passed': all(row['all_passed'] for row in points) and deep['all_passed'] and zeros['all_passed'] and limits['all_passed'] and branch,
           'seconds': time.monotonic() - start}
    (BASE / 'visible-results/visible_analytic.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Visible analytic source audit:', out['all_passed'], 'seconds', out['seconds'], flush=True)
    assert out['all_passed']


if __name__ == '__main__':
    main()

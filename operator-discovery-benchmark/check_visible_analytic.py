#!/usr/bin/env python3
"""Independent harmonic, prime-local and Cauchy audit; no producer imports."""

from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json
import time

import flint

BASE = Path(__file__).resolve().parent


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def short(x):
    return x.str(20)


def box(radius):
    return flint.acb(flint.arb(0, radius), flint.arb(0, radius))


@lru_cache(maxsize=None)
def factors(n):
    fs = {}
    for p, e in flint.fmpz(n).factor():
        p, e = int(p), int(e)
        assert flint.fmpz(p).is_prime()
        fs[p] = fs.get(p, 0) + e
    product = 1
    for p, e in fs.items():
        product *= p ** e
    assert product == n
    return fs


def harmonic(k):
    return sum((Q(1, j) for j in range(1, k + 1)), Q(0))


def c_coefficient(r, k):
    if k < 2:
        return Q(0)
    masked_harmonic = sum((Q(1, e) for e in range(1, k) if e % r and (k - e) % r), Q(0))
    return Q(2, k) * ((harmonic(k - 1) if k % r else 0) - masked_harmonic)


@lru_cache(maxsize=None)
def decoded_coefficient(n, r=3):
    fs = factors(n)
    if len(fs) == 1:
        k = next(iter(fs.values()))
        return Q(2, k) * harmonic(k - 1) if k % r else Q(0)
    if len(fs) == 2:
        e, f = fs.values()
        return Q(2, e * f) if e % r and f % r else Q(0)
    return Q(0)


def mobius(n):
    fs = factors(n)
    return 0 if any(e != 1 for e in fs.values()) else (-1) ** len(fs)


def prime_zeta(s, sigma, cutoff=48):
    assert sigma > 1
    value = sum((real(Q(mobius(m), m)) * (m * s).zeta().log()
                 for m in range(1, cutoff + 1) if mobius(m)), flint.acb(0))
    a = real(sigma)
    tail = flint.arb(2) ** (-(cutoff + 1) * a) * (1 + 2 / ((cutoff + 1) * a - 1))
    tail /= (cutoff + 1) * (1 - flint.arb(2) ** (-a))
    return value + box(tail)


def harmonic_remainder(s, sigma, r=3, degree=80, cutoff=36):
    value = flint.acb(0)
    for k in range(r, degree + 1):
        c = c_coefficient(r, k)
        if c:
            value += real(c) * prime_zeta(k * s, k * sigma, cutoff)
    a = real(sigma)
    tail = flint.arb(2) ** (-(degree + 1) * a) / (1 - flint.arb(2) ** (-a))
    tail *= 1 + 2 / ((degree + 1) * a - 1)
    return value + box(tail)


def local_remainder(x, r):
    # Filter the square by averaging rotations, then subtract the square
    # of the individually filtered logarithm. No coefficient convolution.
    logarithms = [-(1 - flint.acb(0, 2 * flint.arb.pi() * j / r).exp() * x).log()
                  for j in range(r)]
    J = logarithms[0] ** 2 - sum((v ** 2 for v in logarithms), flint.acb(0)) / r
    G = logarithms[0] + (1 - x ** r).log() / r
    return J - G ** 2


def prime_local_remainder(s, sigma, r=3, cutoff=384, subtract_leading=False):
    value = flint.acb(0)
    leading = -Q(2, r) * harmonic(r - 1)
    for p in range(2, cutoff + 1):
        if not flint.fmpz(p).is_prime():
            continue
        x = (-s * flint.arb(p).log()).exp()
        value += local_remainder(x, r) - (real(leading) * x ** r if subtract_leading else 0)
    if subtract_leading:
        value += real(leading) * prime_zeta(r * s, r * sigma)
    exponent = real((r + bool(subtract_leading)) * sigma)
    tail = flint.arb(cutoff) ** (1 - exponent) / (exponent - 1)
    tail /= 1 - flint.arb(cutoff + 1) ** (-real(sigma))
    return value, tail


def actual_points(source):
    rows = []
    for row in source['actual_zeta_ball_checks']:
        sigma, height = Q(row['s'][0]), row['s'][1]
        s = flint.acb(real(sigma), height)
        local, prime_tail = prime_local_remainder(s, sigma)
        G = s.zeta().log() - (3 * s).zeta().log() / 3
        reference = G ** 2 + local + box(prime_tail)
        finite = sum((real(decoded_coefficient(n)) * (-s * flint.arb(n).log()).exp()
                      for n in range(2, 12289) if decoded_coefficient(n)), flint.acb(0))
        tail = 2 * flint.arb(12288) ** (1 - real(sigma)) / (real(sigma) - 1)
        distance = (finite - reference).abs_upper()
        wrong = (finite + real(Q(1, 3)) * (-s * flint.arb(4).log()).exp() - reference).abs_lower()
        passed = bool(distance < tail) and bool(wrong > tail)
        rows.append({'s': row['s'], 'r': 3, 'decoded_cutoff': 12288, 'prime_local_cutoff': 384,
                     'root_filter_prime_infinite_tail_ball': short(prime_tail),
                     'independent_difference_upper_ball': short(distance), 'decoded_infinite_tail_ball': short(tail),
                     'smaller_changed_coefficient_four_error': '1/3', 'changed_difference_lower_ball': short(wrong),
                     'all_passed': passed})
        print('Independent visible full identity', sigma, height, passed, flush=True)
    return rows


def deep_points(source):
    rows = []
    for row in source['deep_correction_ball_checks']['records']:
        sigma, height = Q(row['s'][0]), row['s'][1]
        s = flint.acb(real(sigma), height)
        harmonic_R = harmonic_remainder(s, sigma)
        local, tail = prime_local_remainder(s, sigma, cutoff=4096, subtract_leading=True)
        distance = (local - harmonic_R).abs_upper()
        wrong = (local + real(Q(1, 3)) * (-s * flint.arb(8).log()).exp() - harmonic_R).abs_lower()
        passed = bool(distance < tail) and bool(wrong > tail) and Q(1, 3) < sigma < Q(1, 2)
        rows.append({'s': row['s'], 'correction_only': True, 'prime_local_cutoff': 4096,
                     'harmonic_local_degree': 80, 'harmonic_prime_zeta_Mobius_cutoff': 36,
                     'leading_prime_zeta_Mobius_cutoff': 48, 'independent_difference_upper_ball': short(distance),
                     'independent_prime_infinite_tail_ball': short(tail),
                     'smaller_changed_coefficient_eight_error': '1/3', 'changed_difference_lower_ball': short(wrong),
                     'ordinary_decoded_convergence_claimed': False, 'all_passed': passed})
        print('Independent visible deep correction', sigma, height, passed, flush=True)
    return {'records': rows, 'all_passed': all(row['all_passed'] for row in rows)}


def zero_controls(source):
    rows, central_bounds = [], {}
    for row in source['restored_actual_zero_obstruction_controls']['records']:
        radius, r, height = Q(row['radius']), row['r'], row['disk_centre'][1]
        if height not in central_bounds:
            centre = flint.acb(real(Q(1, 2)), height)
            R = Q(1, 48)
            M = (centre + box(real(R))).zeta().abs_upper()
            flint.ctx.cap = 2
            jet = flint.acb_series([centre, flint.acb(1)], 2).zeta()
            t = real(radius / R)
            remainder = M * t ** 2 / (1 - t)
            modulus = (jet[0] + real(radius) * jet[1]).abs_upper() + remainder
            central_bounds[height] = (modulus, remainder)
        modulus, remainder = central_bounds[height]
        sigma = Q(1, 2) + radius
        log_majorant = real(r * sigma).zeta() - 1
        G_upper = modulus.log() + log_majorant / r
        jump = -4 * flint.arb.pi() * G_upper
        min_sigma = Q(1, 2) - radius
        R_majorant = (real(r * min_sigma).zeta() - 1) / (1 - flint.arb(2) ** (-real(min_sigma)))
        anomaly_bound = 4 * flint.arb.pi() * log_majorant / r
        passed = bool(G_upper < 0) and bool(jump > 0) and R_majorant.is_finite() and min_sigma > Q(1, r)
        rows.append({'disk_centre': row['disk_centre'], 'radius': row['radius'], 'r': r,
                     'Cauchy_radius': '1/48', 'independent_basepoint_modulus_upper_ball': short(modulus),
                     'Cauchy_remainder_ball': short(remainder), 'independent_Re_G_upper_ball': short(G_upper),
                     'independent_monodromy_jump_lower_ball': short(jump),
                     'whole_disk_absolute_correction_majorant_ball': short(R_majorant),
                     'height_independent_monodromy_difference_bound_ball': short(anomaly_bound),
                     'zeta_2s_nonzero_gate_needed': False,
                     'initial_Euler_sheet_of_LOG_zeta_s_asserted': False, 'all_passed': passed})
    return {'records': rows, 'all_passed': all(row['all_passed'] for row in rows)}


def local_and_limit_audit(source):
    exact = True
    for r in (3, 4, 5, 7, 11, 13):
        cs = [c_coefficient(r, k) for k in range(81)]
        exact &= all(c == 0 for c in cs[:r]) and cs[r] == -Q(2, r) * harmonic(r - 1)
        exact &= all(abs(c) <= 1 for c in cs)
    # Evaluate at a different height and real part; the universal compact
    # estimate itself is proved in visible_proof.txt, not by these points.
    sigma, height = Q(7, 4), '-3.39'
    s, rows = flint.acb(real(sigma), height), []
    L = s.zeta().log()
    for r in (3, 4, 5, 7, 11, 13):
        local, tail = prime_local_remainder(s, sigma, r)
        Lrs = (r * s).zeta().log()
        U = (L - Lrs / r) ** 2 + local + box(tail)
        zmajor = real(r * sigma).zeta() - 1
        Rmajor = zmajor / (1 - flint.arb(2) ** (-real(sigma)))
        bound = 2 * L.abs_upper() * zmajor / r + zmajor ** 2 / r ** 2 + Rmajor
        actual = (U - L ** 2).abs_upper()
        rows.append({'s': [str(sigma), height], 'r': r,
                     'independent_limit_difference_upper_ball': short(actual),
                     'independent_limit_majorant_ball': short(bound), 'all_passed': bool(actual < bound)})
    return {'exact_local_audit_passed': bool(exact), 'parameter_limit_records': rows,
            'all_passed': bool(exact) and all(row['all_passed'] for row in rows)}


def main():
    start = time.monotonic()
    flint.ctx.prec = 768
    source = json.loads((BASE / 'visible-results/visible_analytic.json').read_text())
    assert source['all_passed']
    points, deep = actual_points(source), deep_points(source)
    zeros, limits = zero_controls(source), local_and_limit_audit(source)
    checks = {'six_full_zeta_identities_by_root_filter_and_changed_cutoff': all(row['all_passed'] for row in points),
              'six_subcritical_remainder_identities_and_smaller_error_rejections': deep['all_passed'],
              'eight_actual_zero_obstructions_by_Taylor_Cauchy_bounds': zeros['all_passed'],
              'harmonic_cancellation_and_independent_parameter_limit_controls': limits['all_passed'],
              'changed_arithmetic_cutoff_and_smaller_perturbations': all(row['decoded_cutoff'] != old['decoded_cutoff'] for row, old in zip(points, source['actual_zeta_ball_checks'])),
              'ordinary_subcritical_convergence_and_new_RH_estimate_not_claimed': not source['new_RH_estimate_proved'] and all(row['correction_only'] for row in deep['records'])}
    out = {'checks': checks, 'actual_zeta_ball_checks': points, 'deep_correction_ball_checks': deep,
           'restored_actual_zero_obstruction_controls': zeros, 'local_and_limit_audit': limits,
           'production_imports': False, 'shared_trusted_kernel': 'FLINT/Arb with independent harmonic coefficients, prime-local reference and Cauchy bounds',
           'all_passed': all(checks.values()), 'seconds': time.monotonic() - start}
    (BASE / 'visible-results/visible_analytic_verification.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Independent visible analytic audit:', sum(checks.values()), '/', len(checks), 'seconds', out['seconds'], flush=True)
    assert out['all_passed']


if __name__ == '__main__':
    main()

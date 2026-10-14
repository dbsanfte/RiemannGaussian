#!/usr/bin/env python3
"""Native-zeta Mellin bridges for both prime-pair decoders and zero controls."""

from fractions import Fraction as Q
from math import ceil, comb, factorial, isqrt
from pathlib import Path
import argparse
import hashlib
import json
import time

import flint

from exact_arithmetic import factorization

BASE = Path(__file__).resolve().parent


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def short(x):
    return x.str(18)


def box(r):
    return flint.acb(flint.arb(0, r), flint.arb(0, r))


def mobius(n):
    f = factorization(n)
    return 0 if any(e > 1 for e in f.values()) else (-1) ** len(f)


def prime_zeta_polynomial(s, M=24, analytic=False):
    return sum((real(Q(mobius(m), m)) * (m * s).zeta().log(analytic=analytic)
                for m in range(1, M + 1) if mobius(m)), flint.acb(0))


def mobius_tail(sigma, M=24):
    t = flint.arb(2) ** (-real(sigma))
    return t ** (M + 1) / ((M + 1) * (1 - t)) * (1 + 2 / ((M + 1) * real(sigma) - 1))


def native_goldbach(s, sigma, height, M=24):
    a, u = sigma / 2, abs(Q(height)) / 2
    b, T = Q(ceil(2 * a), 2), u + 24
    p = int(2 * b - 1)
    A, denominator = s / 2, s.gamma()
    pi, I = flint.arb.pi(), flint.acb(0, 1)
    L = real(a).zeta().log()
    assert L < pi

    def integrand(t, analytic):
        plus, minus = A + I * t, A - I * t
        return (plus.gamma() * minus.gamma() / denominator
                * prime_zeta_polynomial(plus, M, analytic)
                * prime_zeta_polynomial(minus, M, analytic))

    # Integrate only the finite Mobius polynomial. Its approximation
    # error is bounded separately on the REAL contour, so an error
    # ball for real arguments is never assumed valid on complex nodes.
    start = time.monotonic()
    segments = ceil(4 * T)
    finite = flint.acb(0)
    for j in range(segments):
        finite += flint.acb.integral(integrand, real(T * j / segments), real(T * (j + 1) / segments),
                                    rel_tol=flint.arb('1e-15'), abs_tol=flint.arb('1e-15') / segments,
                                    eval_limit=200000, depth_limit=35, use_heap=True)
        if j and j % 32 == 0:
            print('Native prime-pair contour', sigma, height, j, '/', segments, flush=True)
    finite /= pi
    C = 2 * pi / (1 - (-2 * pi).exp())
    polynomial = sum((comb(p, j) * real(T + u + b) ** (p - j) * factorial(j) / pi ** (j + 1)
                      for j in range(p + 1)), flint.arb(0))
    contour_tail = (C / (pi * denominator.abs_lower()) * (real(a).gamma() / real(b).gamma()) ** 2
                    * L ** 2 * (-pi * real(T)).exp() * polynomial)
    delta = mobius_tail(a, M)
    # Cauchy--Schwarz and the gamma Fourier/Parseval identity give the
    # whole-line L1 kernel bound, independent of a numeric contour.
    kernel_mass = real(sigma).gamma() / (flint.arb(2) ** real(sigma) * denominator.abs_lower())
    mobius_error = kernel_mass * (2 * L * delta + delta ** 2)
    enclosure = finite + box(contour_tail + mobius_error)
    assert enclosure.is_finite()
    return enclosure, {'prime_Mobius_cutoff': M, 'contour_T': str(T), 'initial_segments': segments,
                       'finite_integral_ball': short(finite), 'proved_contour_tail_ball': short(contour_tail),
                       'proved_Mobius_integral_error_ball': short(mobius_error),
                       'gamma_kernel_L1_majorant_ball': short(kernel_mass), 'seconds': time.monotonic() - start}


def finite_series(coefficients, s):
    return sum((real(v) * (-s * flint.arb(n).log()).exp() for n, v in enumerate(coefficients) if v), flint.acb(0))


def actual_points(source, keep=None):
    profile = source['zeta_profile']
    sums, products = (list(map(Q, profile[key])) for key in ('ordered_prime_sum_counts', 'ordered_prime_product_counts'))
    cases = ((Q(3), '2.41'), (Q(4), '-4.67'), (Q(5), '6.97'),
             (Q(3), '-9.41'), (Q(4), '11.71'), (Q(5), '-13.97'))
    rows = []
    for sigma, height in cases:
        key = (str(sigma), height)
        if keep and key in keep:
            rows.append(keep[key])
            print('Reused passed prime-pair bridge', *key, flush=True)
            continue
        s = flint.acb(real(sigma), height)
        reference, info = native_goldbach(s, sigma, height)
        finite = finite_series(sums, s)
        tail = flint.arb(profile['sum_cutoff']) ** (2 - real(sigma)) / (real(sigma) - 2)
        difference = (finite - reference).abs_upper()
        perturb = (finite + real(Q(1, 2)) * (-s * flint.arb(4).log()).exp() - reference).abs_lower()
        additive_diagonal = sum(((-s * flint.arb(2 * p).log()).exp()
                                 for p in range(2, profile['sum_cutoff'] // 2 + 1) if factorization(p) == {p: 1}), flint.acb(0))
        omitted = (finite - additive_diagonal - reference).abs_lower()
        prime = prime_zeta_polynomial(s) + box(mobius_tail(sigma))
        product_reference = prime ** 2
        product_finite = finite_series(products, s)
        product_tail = 2 * flint.arb(profile['product_cutoff']) ** (1 - real(sigma)) / (real(sigma) - 1)
        product_difference = (product_finite - product_reference).abs_upper()
        product_perturb = (product_finite + real(Q(1, 2)) * (-s * flint.arb(4).log()).exp() - product_reference).abs_lower()
        product_diagonal = sum(((-2 * s * flint.arb(p).log()).exp()
                                for p in range(2, isqrt(profile['product_cutoff']) + 1) if factorization(p) == {p: 1}), flint.acb(0))
        product_omitted = (product_finite - product_diagonal - product_reference).abs_lower()
        passed = (bool(difference < tail) and bool(perturb > tail) and bool(omitted > tail)
                  and bool(product_difference < product_tail) and bool(product_perturb > product_tail)
                  and bool(product_omitted > product_tail))
        rows.append({'s': [str(sigma), height], 'native_Mellin_reference': info,
                     'sum_cutoff': profile['sum_cutoff'], 'product_cutoff': profile['product_cutoff'],
                     'additive_difference_upper_ball': short(difference), 'additive_tail_ball': short(tail),
                     'additive_perturbed_lower_ball': short(perturb), 'additive_diagonal_omitted_lower_ball': short(omitted),
                     'product_difference_upper_ball': short(product_difference), 'product_tail_ball': short(product_tail),
                     'product_perturbed_lower_ball': short(product_perturb), 'product_diagonal_omitted_lower_ball': short(product_omitted),
                     'all_passed': passed})
        print('Prime-pair native-zeta bridge', sigma, height, passed, 'seconds:', info['seconds'], flush=True)
    return rows


def zero_controls():
    old = json.loads((BASE / 'decode-results/decode_analytic.json').read_text())
    assert old['all_passed']
    rows = []
    for record in old['restored_actual_zero_obstruction_controls']['records']:
        radius, sigma = Q(record['radius']), Q(1, 2) + Q(record['radius'])
        centre = flint.acb(real(Q(1, 2)), record['disk_centre'][1])
        base, region = centre + real(radius), centre + box(real(radius))
        ReP = sum((real(Q(mobius(m), m)) * abs((m * base).zeta()).log()
                   for m in range(1, 49) if mobius(m)), flint.arb(0))
        ReP += flint.arb(0, mobius_tail(sigma, 48))
        z2lower = (2 * region).zeta().abs_lower()
        jump = 4 * flint.arb.pi() * ReP.abs_lower()
        passed = bool(base.zeta().abs_lower() > 0) and bool(ReP < 0) and bool(jump > 0) and bool(z2lower > 0)
        rows.append({'disk_centre': record['disk_centre'], 'radius': record['radius'],
                     'reused_simple_zero_certificate': True, 'branch_independent_Re_prime_zeta_ball': short(ReP),
                     'multiplicative_prime_square_monodromy_jump_lower_ball': short(jump),
                     'whole_disk_zeta_2s_nonzero_lower_ball': short(z2lower),
                     'encoded_Gamma_holomorphic': True, 'prime_product_square_single_valued_holomorphy_rejected': passed,
                     'additive_series_value_or_monodromy_at_this_zero_claimed': False, 'all_passed': passed})
        print('Full prime-product zero obstruction', record['disk_centre'][1], passed, flush=True)
    return {'records': rows, 'all_passed': all(row['all_passed'] for row in rows)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--retry-failed', action='store_true')
    args = parser.parse_args()
    start = time.monotonic()
    flint.ctx.prec = 192
    source = json.loads((BASE / 'prime-pair-results/prime_pair_search.json').read_text())
    assert source['all_passed']
    fingerprint = hashlib.sha256(json.dumps(source['zeta_profile'], sort_keys=True).encode()).hexdigest()
    previous_path = BASE / 'prime-pair-results/prime_pair_analytic.json'
    keep = {}
    if args.retry_failed:
        previous = json.loads(previous_path.read_text())
        assert previous.get('coefficient_profile_sha256') == fingerprint
        keep = {tuple(row['s']): row for row in previous['actual_zeta_ball_checks'] if row['all_passed']}
    cases, zeros = actual_points(source, keep), zero_controls()
    out = {'actual_zeta_ball_checks': cases, 'full_prime_product_zero_obstruction_controls': zeros,
           'product_identity': 'P(s)^2', 'additive_identity': 'sum_(p,q primes) (p+q)^(-s)',
           'product_absolute_abscissa': '1', 'additive_absolute_abscissa': '2',
           'additive_Mellin_bridge_Re_s_gt_two_proved': True,
           'additive_critical_strip_continuation_or_RH_estimate_proved': False,
           'historical_novelty_established': False, 'new_RH_estimate_proved': False,
           'coefficient_profile_sha256': fingerprint,
           'all_passed': all(row['all_passed'] for row in cases) and zeros['all_passed'],
           'seconds': time.monotonic() - start}
    (BASE / 'prime-pair-results/prime_pair_analytic.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Prime-pair analytic source:', out['all_passed'], 'seconds:', out['seconds'], flush=True)
    assert out['all_passed']


if __name__ == '__main__':
    main()

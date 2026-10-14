#!/usr/bin/env python3
"""Native-zeta scalar shear checks and whole critical-zero correction bounds."""

from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json
import time

import flint

from exact_arithmetic import formal_exp
from laplacian_search import primes, kernel
from pair_fibre_probe import prime_powers
from prime_pair_analytic import prime_zeta_polynomial, mobius_tail

BASE = Path(__file__).resolve().parent


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def short(x):
    return x.str(20)


def box(radius):
    return flint.acb(flint.arb(0, radius), flint.arb(0, radius))


def paired_tail(sigma, S, cutoff, exclude_two=False):
    """Bound omitted prime pairs by integer gaps; sigma is a lower bound."""
    A = cutoff // 2
    sig, d = real(sigma), 6 * real(sigma) - 2
    u = 2 - 4 * sigma
    if u > -1:
        C = real(1 if u >= 0 else 1 / (u + 1))
        balanced = S ** 2 * C * flint.arb(A) ** (-d) / d
    elif u == -1:
        v = 2 * sig + 1
        balanced = S ** 2 * flint.arb(A) ** (-v) * ((1 + flint.arb(A).log()) / v + 1 / v ** 2)
    else:
        balanced = S ** 2 * (4 * sig - 2).zeta() * flint.arb(A) ** (-2 * sig - 1) / (2 * sig + 1)
    first = sum((flint.arb(p) ** (-2 * sig) for p in primes(A) if not exclude_two or p != 2), flint.arb(0))
    small = 4 * first * flint.arb(A) ** (1 - 4 * sig) / (4 * sig - 1)
    large = 4 / (4 * sig - 1) * flint.arb(A) ** (-d) / d
    return balanced + small + large


def direct_gamma(s, cutoff):
    ps = primes(cutoff)
    xs = [(-s * flint.arb(p).log()).exp() for p in ps]
    gap = {d: (-4 * s * flint.arb(d).log()).exp() for d in range(1, cutoff)}
    return sum(((xs[j] - xs[k]) ** 2 * gap[q - p]
                for j, p in enumerate(ps) for k, q in enumerate(ps) if j < k), flint.acb(0))


def poly_gamma(s, cutoff, absolute=False):
    mask, x, y = ([flint.acb(0)] * (cutoff + 1) for _ in range(3))
    for p in primes(cutoff):
        mask[p] = flint.acb(1)
        x[p] = (-s * flint.arb(p).log()).exp()
        y[p] = x[p] ** 2
    diagonal = flint.acb_poly(y) * flint.acb_poly(list(reversed(mask)))
    cross = flint.acb_poly(x) * flint.acb_poly(list(reversed(x)))
    sign = 2 if absolute else -2
    return sum(((diagonal[cutoff + d] + diagonal[cutoff - d] + sign * cross[cutoff + d])
                * (-4 * s * flint.arb(d).log()).exp()
                for d in range(1, cutoff)), flint.acb(0))


def native_anchor(s, sigma, cutoff=1024, degree=8, M=32):
    """Restore only edges from prime 2 to primes beyond the finite graph."""
    restore, rising = flint.acb(0), flint.acb(1)
    two = (-s * flint.arb(2).log()).exp()
    for k in range(degree + 1):
        if k:
            rising *= (4 * s + k - 1) / k
        tails = []
        for j in (4, 5, 6):
            arg = j * s + k
            native = prime_zeta_polynomial(arg, M) + box(mobius_tail(j * sigma + k, M))
            finite = sum(((-arg * flint.arb(p).log()).exp() for p in primes(cutoff)), flint.acb(0))
            tails.append(native - finite)
        restore += rising * 2 ** k * (two ** 2 * tails[0] - 2 * two * tails[1] + tails[2])
    sig, S = real(sigma), s.abs_upper()
    ratio = flint.arb(4) / (cutoff + 1)
    remainder = (4 * flint.arb(2) ** (-2 * sig) * flint.arb(2) ** (4 * S)
                 * ratio ** (degree + 1) / (1 - ratio)
                 * flint.arb(cutoff) ** (1 - 4 * sig) / (4 * sig - 1))
    value = poly_gamma(s, cutoff) + restore
    tail = paired_tail(sigma, S, cutoff, exclude_two=True) + remainder
    return value + box(tail), {'prime_graph_cutoff': cutoff, 'native_prime_zeta_arguments': ['4*s+k', '5*s+k', '6*s+k'],
                               'binomial_degree': degree, 'Mobius_cutoff': M,
                               'paired_infinite_tail_ball': short(tail),
                               'native_prime_two_tail_restoration_ball': short(restore),
                               'binomial_remainder_ball': short(remainder)}


@lru_cache(maxsize=None)
def coefficient_frames(size=4096, beta=Q(1), amplitude=Q(1)):
    h, prime = ([Q(0)] * (size + 1) for _ in range(2))
    for n, _, e in prime_powers(size):
        h[n] = Q(1, e)
        if e == 1:
            prime[n] = Q(1)
    extra = kernel(prime, prime)
    actual = formal_exp([beta * a + amplitude * b for a, b in zip(h, extra)])
    major = formal_exp([abs(beta) * a + abs(amplitude) * abs(b) for a, b in zip(h, extra)])
    return actual, major


def finite_series(coefs, s):
    return sum((real(v) * (-s * flint.arb(n).log()).exp() for n, v in enumerate(coefs) if v), flint.acb(0))


def absolute_total(sigma, cutoff=1024):
    sig = real(sigma)
    finite = poly_gamma(flint.acb(sig), cutoff, absolute=True).real
    P = prime_zeta_polynomial(flint.acb(sig), 40).real + flint.arb(0, mobius_tail(sigma, 40))
    T = P - sum((flint.arb(p) ** (-sig) for p in primes(cutoff)), flint.arb(0))
    norm = ((real(Q(3, 2)) ** sig) + (real(Q(2, 3)) ** sig) + 2) / 2
    error = norm * (2 * P * T + T ** 2)
    return finite + flint.arb(0, error.abs_upper())


def scalar_case(sigma, height, beta=Q(1), family='input', size=4096):
    amplitude = beta ** 2 if family == 'input' else beta
    s = flint.acb(real(sigma), height)
    coefficients, major = coefficient_frames(size, beta, amplitude)
    finite = finite_series(coefficients, s)
    gamma, info = native_anchor(s, sigma)
    actual = (real(beta) * s.zeta().log() + real(amplitude) * gamma).exp()
    total = (real(abs(beta)) * real(sigma).zeta().log() + real(abs(amplitude)) * absolute_total(sigma)).exp()
    prefix = finite_series(major, flint.acb(real(sigma))).real
    tail = (total - prefix).abs_upper()
    difference = (finite - actual).abs_upper()
    wrong = (finite + real(Q(1, 2)) * (-s * flint.arb(4).log()).exp() - actual).abs_lower()
    passed = bool(difference < tail) and bool(wrong > tail)
    row = {'s': [str(sigma), height], 'beta': str(beta), 'family': family, 'amplitude': str(amplitude),
           'coefficient_cutoff': size, 'native_reference': info, 'difference_upper_ball': short(difference),
           'absolute_EXP_majorant_minus_major_prefix_tail_ball': short(tail),
           'changed_coefficient_four_error': '1/2', 'changed_difference_lower_ball': short(wrong),
           'all_passed': passed}
    print('Laplacian ordinary-zeta scalar', sigma, height, beta, family, passed, flush=True)
    return row


def zero_controls():
    rows = []
    for filename, key in (('size-results/size_analytic_probe.json', 'actual_critical_line_zero_control'),
                          ('cancellation-results/cancellation_analytic.json', 'fresh_actual_critical_line_zero_control')):
        old = json.loads((BASE / filename).read_text())[key]
        assert old['all_passed']
        centre = flint.acb(real(Q(1, 2)), old['disk_centre'][1])
        radius = Q(old['radius'])
        s = centre + box(real(radius))
        sigma = Q(1, 2) - radius
        finite = direct_gamma(s, 2048)
        tail = paired_tail(sigma, s.abs_upper(), 2048)
        enclosure = finite + box(tail)
        M = enclosure.abs_upper()
        factors = [{'beta': str(beta), 'modulus_lower_ball': short((-real(beta ** 2) * M).exp()),
                    'modulus_upper_ball': short((real(beta ** 2) * M).exp()),
                    'strictly_positive_lower': bool((-real(beta ** 2) * M).exp() > 0)}
                   for beta in (Q(1), Q(1, 2), Q(1, 4))]
        passed = enclosure.is_finite() and all(row['strictly_positive_lower'] for row in factors)
        rows.append({'disk_centre': old['disk_centre'], 'radius': old['radius'], 'reused_simple_zero': True,
                     'entire_rectangle_real_part_lower': str(sigma), 'prime_graph_cutoff': 2048,
                     'finite_grouped_value_ball': short(finite), 'grouped_infinite_tail_ball': short(tail),
                     'whole_disk_Gamma_modulus_upper_ball': short(M), 'input_root_factor_bounds': factors,
                     'whole_zero_disk_correction_holomorphic': True, 'new_zero_located': False,
                     'root_exponent_preserved': 'm*beta; m=1 on this reused disk', 'all_passed': passed})
        print('Laplacian whole-zero correction', old['disk_centre'][1][:14], passed, flush=True)
    return {'records': rows, 'all_passed': all(row['all_passed'] for row in rows)}


def main():
    start = time.monotonic()
    flint.ctx.prec = 512
    source = json.loads((BASE / 'laplacian-results/laplacian_search.json').read_text())
    assert source['all_passed']
    cases = ((Q(2), '2.73'), (Q(7, 3), '-4.97'), (Q(5, 2), '7.31'),
             (Q(2), '-9.59'), (Q(7, 3), '11.83'), (Q(5, 2), '-14.17'))
    points = [scalar_case(sig, height) for sig, height in cases]
    roots = [scalar_case(Q(2), '7.43', beta, family) for beta, family in
             ((Q(1), 'input'), (Q(1, 2), 'input'), (Q(1, 2), 'output'), (Q(1, 4), 'input'), (Q(1, 4), 'output'))]
    zeros = zero_controls()
    out = {'actual_zeta_ball_checks': points, 'ordinary_root_scalar_controls': {'records': roots, 'all_passed': all(row['all_passed'] for row in roots)},
           'whole_actual_zero_correction_controls': zeros, 'grouped_correction_holomorphic_domain': 'Re(s)>1/3',
           'ordinary_correction_absolute_abscissa': '1/2, endpoint convergent',
           'ordinary_transformed_positive_beta_absolute_abscissa': '1',
           'native_LOG_zeta_s_anchor_below_Re_one_used': False,
           'positive_Hermitian_form_equals_holomorphic_correction_claimed': False,
           'counts_as_new_primitive': False, 'historical_novelty_established': False, 'new_RH_estimate_proved': False,
           'all_passed': all(row['all_passed'] for row in points + roots) and zeros['all_passed'], 'seconds': time.monotonic() - start}
    (BASE / 'laplacian-results/laplacian_analytic.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Laplacian analytic source:', out['all_passed'], 'seconds', out['seconds'], flush=True)
    assert out['all_passed']


if __name__ == '__main__':
    main()

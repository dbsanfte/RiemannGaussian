#!/usr/bin/env python3
"""Prototype a certified Mellin--Barnes bridge for prime-sum couplings."""

from fractions import Fraction as Q
from math import ceil, comb, factorial
from time import monotonic
import flint

from exact_arithmetic import factorization


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def logarithmic_coefficient(n):
    f = factorization(n)
    return Q(1, next(iter(f.values()))) if len(f) == 1 else Q(0)


def native_pair(s, sigma, height, r=3, margin=24, tolerance='1e-24'):
    """Centered beta Mellin integral plus a proved infinite contour tail."""
    a, u = Q(r) * sigma / 2, abs(Q(height) * r / 2)
    b = Q(ceil(2 * a), 2)
    p = int(2 * b - 1)
    T = u + margin
    A, B = r * s / 2, (r + 2) * s / 2
    denominator = (r * s).gamma()
    pi, I = flint.arb.pi(), flint.acb(0, 1)
    assert (real((r + 2) * sigma / 2).zeta().log() < pi)

    def integrand(t, analytic):
        plus, minus = A + I * t, A - I * t
        return (plus.gamma() * minus.gamma() / denominator
                * (B + I * t).zeta().log(analytic=analytic)
                * (B - I * t).zeta().log(analytic=analytic))

    start = monotonic()
    # Near Re(B)=1 a single large starting interval gives nonfinite native
    # zeta/log enclosures before adaptive subdivision can begin. Explicit
    # small initial segments keep those rectangles in the Euler-log region.
    segments = ceil(8 * T) if (r + 2) * sigma / 2 < Q(3, 2) else 1
    integral = flint.acb(0)
    for j in range(segments):
        integral += flint.acb.integral(integrand, real(T * j / segments), real(T * (j + 1) / segments),
                                      rel_tol=flint.arb(tolerance), abs_tol=flint.arb(tolerance) / segments,
                                      eval_limit=200000, depth_limit=35, use_heap=True)
    integral /= pi
    C = 2 * pi / (1 - (-2 * pi).exp())
    L = real((r + 2) * sigma / 2).zeta().log()
    polynomial_integral = sum((comb(p, j) * real(T + u + b) ** (p - j)
                               * factorial(j) / pi ** (j + 1) for j in range(p + 1)), flint.arb(0))
    tail = (C / (pi * denominator.abs_lower()) * (real(a).gamma() / real(b).gamma()) ** 2
            * L ** 2 * (-pi * real(T)).exp() * polynomial_integral)
    enclosure = integral + flint.acb(flint.arb(0, tail), flint.arb(0, tail))
    return enclosure, {'seconds': monotonic() - start, 'T': str(T), 'tail': tail.str(18),
                       'finite_integral': integral.str(18), 'gamma_majorant_b': str(b),
                       'initial_integration_segments': segments}


def direct_pair(s, sigma, cutoff=64, r=3):
    pp = [(n, logarithmic_coefficient(n)) for n in range(2, cutoff + 1)]
    pp = [(n, g) for n, g in pp if g]
    finite = sum((real(g * h) * (-s * flint.arb(x * y * (x + y) ** r).log()).exp()
                  for x, g in pp for y, h in pp), flint.acb(0))
    exponent = real((r + 2) * sigma / 2)
    L = exponent.zeta().log()
    residual = flint.arb(cutoff) ** (1 - exponent) / (exponent - 1)
    tail = 2 ** (-r * real(sigma)) * 2 * L * residual
    return finite, tail


if __name__ == '__main__':
    flint.ctx.prec = 192
    sigma, height = Q(5, 3), '3.11'
    s = flint.acb(real(sigma), height)
    reference, info = native_pair(s, sigma, height)
    finite, tail = direct_pair(s, sigma)
    print(info, flush=True)
    print('native', reference.str(18), 'direct', finite.str(18), 'tail', tail.str(18),
          'distance', (reference - finite).abs_upper().str(18),
          'passed', bool((reference - finite).abs_upper() < tail), flush=True)

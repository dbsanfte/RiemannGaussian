#!/usr/bin/env python3
"""Optional independent rational and analytic regression checks; not CI.

Integrate finite binomial polynomials directly over rational intervals,
then compare the complete polynomial/phase/division integration against
Arb's independent complex quadrature on a small finite polynomial example.
"""
from fractions import Fraction
import json
import math

from flint import acb, arb, arb_poly, ctx, fmpq
from probe_riesz_owner_integral import exp_integral, integrate_piece, display
from riesz_owner_moments import band_moments, integer_beta_cdf
from riesz_response_spline import Piece


def rational_checks():
    checks = 0
    for M, lo, hi in [(7, 2, 5), (13, 7, 9), (20, 4, 18)]:
        center, scale = Fraction(1, 2), Fraction(1, 6)
        left, right = center-scale, center+scale
        moments = band_moments(M, lo, hi, arb(1)/2, arb(1)/6, 13)
        for k, value in enumerate(moments):
            exact = Fraction(0)
            for j in range(lo, hi+1):
                for b in range(M-j+1):
                    for z in range(k+1):
                        power = j+b+z+1
                        exact += (math.comb(M, j)*math.comb(M-j, b)*(-1)**b
                                  *math.comb(k, z)*(-center)**(k-z)/scale**k
                                  *(right**power-left**power)/power)
            truth = fmpq(exact.numerator, exact.denominator)
            mid, radius = value.mid().fmpq(), value.rad().fmpq()
            assert mid-radius <= truth <= mid+radius
            checks += 1
    return checks


def analytic_checks():
    M, lo, hi = 20, 8, 13
    r, T, lam = arb(1)/25, arb(7), arb(693)/1000
    piece = Piece(arb(10), arb(41)/4, arb_poly([1, 2, -3]), arb(0))
    value, error, _ = integrate_piece(piece, r, T, lam, M, lo, hi, 64)
    left = (1-r*piece.right)/(1-r)
    right = (1-r*piece.left)/(1-r)

    def integrand(x, analytic):
        p = (1-r)*x
        s = (1-p)/r
        v = s-piece.left
        polynomial = 1+2*v-3*v*v
        band = sum(math.comb(M, j)*x**j*(1-x)**(M-j) for j in range(lo, hi+1))
        factor = ((T*(1-p)/40000).exp()+6*(T/40000).exp()*(3*T*p/500).cos())/lam
        return band/x*factor*polynomial

    reference = acb.integral(integrand, left, right,
                             abs_tol=arb('1e-100'), rel_tol=arb('1e-100'))
    assert reference.is_finite() and reference.imag.contains(0)
    enclosed = value+arb(0, error)
    assert enclosed.overlaps(reference.real)
    assert enclosed.rad() < arb('1e-90') and reference.real.rad() < arb('1e-95')
    # Integer-beta evaluation has an unrelated special-function reference.
    for a, b, x in [(8, 13, arb(1)/2), (14, 7, arb(3)/5), (2, 5, arb(2)/3)]:
        assert integer_beta_cdf(x, a, b).overlaps(x.beta_lower(a, b, regularized=True))
    return dict(signed_polynomial_phase_integral=display(enclosed),
                independent_complex_quadrature=display(reference.real),
                remainder=display(error), beta_references=3)


if __name__ == '__main__':
    ctx.prec = 1024
    print(json.dumps(dict(rational_moments=rational_checks(), analytic=analytic_checks(),
                         scope='Optional small-case checks, not a carrier bound')), flush=True)

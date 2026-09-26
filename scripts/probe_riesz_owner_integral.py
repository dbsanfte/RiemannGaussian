#!/usr/bin/env python3
"""Optional enclosed OWNER integral of the full signed continuous response.

Both radial T and least share r are fixed here. All count signs, the empty
atoms, the moving Riesz length, the conditional factorial band and the
physical owner mask 1/2<p<3/5 remain inside the integral. Polynomial moments
and explicit Taylor/density remainders pay the owner integration error.
This is not the radial/beta integral, an arithmetic bound or a Lean proof.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import time

from flint import acb, acb_poly, arb, arb_poly, ctx, fmpz
from probe_riesz_continuous_balls import ContinuousCascade
from riesz_continuous_projection import compress_model, count_allowance, response_interval
from riesz_owner_moments import band_moments
from riesz_response_spline import ResponseSpline


def display(value):
    with ctx.workprec(192):
        return str(value+0)


def exp_integral(poly, z, center, scale, moments, order):
    """Integral of poly(y)/x * exp(z*x), x=center+scale*y.

    The division residual is a literal polynomial. Taylor multiplication
    is done before discarding its high orders. Every retained coefficient
    is integrated with sign against the exact positive band measure.
    """
    quotient = []
    for k in range(order+1):
        quotient.append((poly[k]-(scale*quotient[-1] if k else 0))/center)
    quotient = arb_poly(quotient)
    division_residual = poly-arb_poly([center, scale])*quotient
    division_error = sum(abs(c) for c in division_residual.coeffs())/(center-scale)
    beta = z*scale
    coefficients, term = [], acb(1)
    for k in range(order+1):
        coefficients.append(term)
        term *= beta/(k+1)
    product = acb_poly(quotient)*acb_poly(coefficients)
    value = sum(product[k]*moments[k] for k in range(order+1))
    tail = sum(abs(product[k]) for k in range(order+1, product.degree()+1))
    exponential_error = abs(term)*abs(beta.real).exp()
    error = (tail+sum(abs(c) for c in quotient.coeffs())*exponential_error
             +division_error*abs(beta.real).exp())
    factor = (z*center).exp()
    return factor*value, (abs(factor)*moments[0]*error).upper()


def integrate_piece(piece, r, T, lam, M, lo, hi, order):
    half_s = (piece.right-piece.left)/2
    center_s = piece.left+half_s
    center = (1-r*center_s)/(1-r)
    scale = r*half_s/(1-r)
    moments = band_moments(M, lo, hi, center, scale, order+1)
    poly = piece.poly(arb_poly([half_s, -half_s]))
    growth_z = acb(-T*(1-r)/40000)
    phase_z = acb(0, 3*T*(1-r)/500)
    first, first_error = exp_integral(poly, growth_z, center, scale, moments, order)
    second, second_error = exp_integral(poly, phase_z, center, scale, moments, order)
    assert first.imag.contains(0)
    front = (T/40000).exp()/lam
    value = front*(first.real+6*second.real)
    truncation_error = front*(first_error+6*second_error)
    density_error = front*7*moments[0]*piece.error/(center-scale)
    return value, (truncation_error+density_error).upper(), dict(
        mass=display(moments[0]), truncation_error=display(truncation_error),
        density_error=display(density_error), value=display(value))


def run(n, face, degree, bits, order, compression, reference_nodes=0):
    ctx.prec, ctx.threads = bits, 1
    start = time.monotonic()
    u = arb(10001)/20000
    T = (n+1)/u
    h = (n+99)//100-2 if face == 0 else n//25-1
    r = arb(h+1)/(n+2)  # exact mean of this retained beta face
    X = (fmpz(20000)**n)//((fmpz(10001)**n)*(n+1))+2
    lam = 2*arb(X).log()/T
    gap = (1-lam)/r
    s_lo, s_hi = arb(2)/(5*r), arb(1)/(2*r)
    end = math.ceil(float(s_hi.upper()))+1
    model = ContinuousCascade([acb(-T*r/40000), acb(0, 3*T*r/500),
                               acb(0, -3*T*r/500)], [1, 3, 3], end, 4, degree)
    compress_model(model, arb(compression))
    spline = ResponseSpline(model, gap, s_lo, s_hi)
    # Independent local convolution at three interior points of every piece.
    checks = 0
    for piece in spline.pieces:
        for fraction in (arb(1)/4, arb(1)/2, arb(3)/4):
            s = piece.left+fraction*(piece.right-piece.left)
            direct = response_interval(model, s, s-gap)
            assert spline.value(s).overlaps(direct), 'Spline/convolution disagreement'
            checks += 1
    print('spline', json.dumps(dict(pieces=len(spline.pieces), checks=checks,
                                   seconds=time.monotonic()-start)), flush=True)
    M, lo, hi = n-h, (21*n+39)//40, 23*n//40
    total, error, rows = arb(0), arb(0), []
    for index, piece in enumerate(spline.pieces):
        value, budget, audit = integrate_piece(piece, r, T, lam, M, lo, hi, order)
        total += value
        error += budget
        rows.append(audit)
        print('piece', index+1, len(spline.pieces), display(value), display(budget), flush=True)
    enclosure = total+arb(0, error.upper())
    assert enclosure.is_finite()
    reference = None
    if reference_nodes:
        from riesz_owner_gauss import owner_rule
        with ctx.workprec(max(bits, 32*reference_nodes)):
            rule, _ = owner_rule(M, lo, hi, reference_nodes)
        approximate = arb(0)
        for x, w in rule:
            p = (1-r)*x
            if arb(1)/2 < p < arb(3)/5:
                s, d = (1-p)/r, (lam-p)/r
                response = response_interval(model, s, d)
                factor = ((T*(1-p)/40000).exp()+6*(T/40000).exp()*(3*T*p/500).cos())/lam
                approximate += w*factor*response
        reference = dict(nodes=reference_nodes, value=display(approximate),
                         difference_enclosure=display(enclosure-approximate),
                         scope='Independent finite quadrature; its owner error is not assumed zero')
    cap = 54 if face == 0 else 12
    omitted = count_allowance(s_hi, (lam-arb(1)/2)/r, cap+1)
    assert omitted == 0, 'Mean-face regression unexpectedly has omitted geometric counts'
    return dict(N=n, face=face, T=display(T), r=display(r), moving_ratio=display(lam),
                degree=degree, bits=bits, taylor_order=order, compression=compression,
                owner_orders=[lo, hi], conditional_trials=M, pieces=len(rows),
                independent_point_checks=checks, signed_integral=display(enclosure),
                explicit_truncation_and_density_budget=display(error),
                polynomial_roundoff_radius=display(total.rad()),
                omitted_model_count_allowance=display(omitted),
                owner_gauss_reference=reference, rows=rows, seconds=time.monotonic()-start,
                scope='Owner integration enclosed for a fixed radial point and exact mean beta '
                      'share in a synthetic finite-mode continuum. All count signs and '
                      'conditional factorial weights retained. Radial/beta integration, '
                      'arithmetic transport and the signed prime-sum bound remain open.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=65536)
    parser.add_argument('--face', type=int, choices=[0, 1], default=1)
    parser.add_argument('--degree', type=int, default=128)
    parser.add_argument('--bits', type=int, default=4096)
    parser.add_argument('--taylor-order', type=int, default=128)
    parser.add_argument('--compression', default='1e-60')
    parser.add_argument('--reference-nodes', type=int, default=0)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.order < 10000 or min(args.degree, args.taylor_order) < 32 or args.bits < 1024:
        parser.error('Insufficient order, degree, Taylor order or precision')
    names = [Path(__file__).name, 'riesz_response_spline.py', 'riesz_owner_moments.py',
             'probe_riesz_continuous_balls.py', 'riesz_continuous_projection.py',
             'riesz_owner_gauss.py']
    hashes = lambda: {p: hashlib.sha256(Path(__file__).with_name(p).read_bytes()).hexdigest()
                      for p in names}
    frozen = hashes()
    result = run(args.order, args.face, args.degree, args.bits, args.taylor_order,
                 args.compression, args.reference_nodes)
    assert hashes() == frozen, 'Sources changed during the computation'
    result['source_sha256'] = frozen
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'rows'}), flush=True)


if __name__ == '__main__':
    main()

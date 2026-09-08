"""Full signed product shells of the balanced gamma rectangle.

Finite floating-point exploration. Every cofactor, short sum, centering
term, and signed complex shell remains in the reconstruction.
"""

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy

from probe_eta_coprime_products import check_close
from probe_eta_gamma_balanced_outer import setup
from probe_eta_gamma_high import low_eta_coefficients, pair, survival


def probe(u, index, sigma, data):
    A, L, V, P, mu, inner, original_error, H, K, c, weights = data
    sm = mp.mpc(sigma, mp.zetazero(index).imag)
    s = complex(sm)
    alpha = 1-2*2**(-s)
    eta_s = complex((1-mp.power(2, 1-sm))*mp.zeta(sm))
    n = np.arange(1, P+1)
    x = n/A
    g = np.zeros(P, dtype=complex)
    g[:V] = np.polynomial.polynomial.polyval(x[:V], low_eta_coefficients(sm, 60))
    for q in range(1, P//(V+1)+1):
        length = P//q-V
        if length:
            g[V:V+length] += (1 if q%2 else -1)*q**(-s)*survival(q*x[V:V+length])
    f = np.r_[0j, np.exp(-s*np.log(n))*(g-eta_s*survival(x))/alpha]
    source = (survival(1/A)-2*2**(-s)*survival(2/A))/alpha
    source -= eta_s*np.dot(mu[1:], np.exp(-s*np.log(n))*survival(x))/alpha
    check_close(np.dot(mu, f), source, 'complete centered source')
    max_product = min(P, 2*L*V)
    product = np.arange(1, max_product+1)
    kernel = np.zeros(max_product+1, dtype=complex)
    # Compute the same complete zeta cofactor by two complementary loops.
    split = min(V, max_product)
    for m in range(1, split+1):
        kernel[m] = np.sum(f[m::m])
    for k in range(1, P//(split+1)+1):
        length = min(max_product, P//k)-split
        if length:
            kernel[split+1:split+length+1] += f[k*(split+1):k*(split+length)+1:k]
    conv = np.zeros(max_product+1)
    for a, value in enumerate(weights, 1):
        length = min(V, max_product//a)
        conv[a:a*length+1:a] += value*mu[1:length+1]
    # Independent exact divisor enumeration for selected product coefficients.
    coefficient_checks = []
    selected = {1, L+1, V, V+1, A//8, A//4, A, max_product}
    for m in sorted(n for n in selected if 1 <= n <= max_product):
        exact = sum((Fraction(int(mu[a])) if a <= L else c)*int(mu[m//a])
                    for a in sympy.divisors(m) if a <= 2*L and m//a <= V)
        check_close(conv[m], float(exact), 'independent exact product coefficient')
        coefficient_checks.append(dict(product=m, exact_coefficient=str(exact),
                                       float_error=float(abs(conv[m]-float(exact)))))
    # Independent complete divisor kernel, without the nested damped eta series.
    kernel_checks = []
    for m in sorted({max(1, A//64), max(1, A//16), A//4, A, 4*A}):
        if m > max_product:
            continue
        count = P//m
        tau = np.zeros(count+1, dtype=np.int64)
        for d in range(1, count+1):
            tau[d::d] += 1
        alternating = tau.copy()
        alternating[2::2] -= 2*tau[1:count//2+1]
        j = np.arange(1, count+1)
        direct = m**(-s)/alpha*np.dot((alternating[1:]-eta_s)*np.exp(-s*np.log(j)),
                                     survival(j*m/A))
        check_close(direct, kernel[m], 'independent complete alternating-divisor kernel')
        kernel_checks.append(dict(product=m, discrepancy=float(abs(direct-kernel[m]))))
    raw_terms = -conv[1:]*kernel[1:]
    actual = np.sum(raw_terms)
    rows = np.array([-np.dot(inner[1:P//a+1], f[a:a*(P//a)+1:a])
                     for a in range(1, 2*L+1)])
    check_close(actual, np.dot(weights, rows), 'product and inner-cofactor evaluations')
    original = np.dot(mu[1:L+1], rows[:L])
    left_low = np.dot(mu[1:L+1], f[1:L+1])
    right_low = np.dot(mu[1:V+1], f[1:V+1])
    tail = np.dot(original_error, f)
    source_correction = left_low+right_low+tail-(actual-original)
    check_close(actual+source_correction, source, 'all source corrections')
    # The eta zero at 1 cancels one zeta pole. There is one reciprocal mode.
    main_coefficient = complex(A**(1-sm)*mp.gamma(1-sm)*(2-sm)*(3-sm)/2
                               *(mp.log(2)-eta_s)/alpha)
    main = -main_coefficient*np.sum(conv[1:]/product)
    check_close(main, 0j, 'complete reciprocal-product cancellation')
    rem = -kernel[1:]+main_coefficient/product
    terms = conv[1:]*rem
    check_close(np.sum(terms)+main, actual, 'whole signed divisor remainder')
    shell_id = np.floor(np.log2(product/A)).astype(int)
    shells = []
    for j in np.unique(shell_id):
        mask = shell_id == j
        value = np.sum(terms[mask])
        shells.append(dict(log2_product_shell=int(j), lower_product=int(product[mask][0]),
            upper_product=int(product[mask][-1]), signed=pair(value),
            absolute_real=float(np.sum(np.abs(terms[mask].real))),
            absolute_complex=float(np.sum(np.abs(terms[mask])))))
    check_close(sum(complex(*r['signed']) for r in shells)+main,
                actual, 'all complex product shells')
    # Keep the full two-dimensional dyadic table, not only its marginals.
    aa = np.arange(1, 2*L+1)
    bb = np.arange(1, V+1)
    outer_shell = np.floor(np.log2(aa/u)).astype(int)
    inner_shell = np.floor(np.log2(bb/V)).astype(int)
    table = []
    for i in np.unique(outer_shell):
        avec = aa[outer_shell == i]
        for j in np.unique(inner_shell):
            bvec = bb[inner_shell == j]
            products = avec[:,None]*bvec[None,:]
            if np.any(products > max_product):
                raise ValueError('The chosen scales exceed the finite product shadow')
            block = weights[avec-1,None]*mu[bvec][None,:]*rem[products-1]
            table.append(dict(outer_log2_shell=int(i), inner_log2_shell=int(j),
                signed=pair(np.sum(block))))
    check_close(sum(complex(*r['signed']) for r in table)+main,
                actual, 'complete rectangular shell table')
    # Heat filters are diagnostics; the full signed removed part is retained.
    heats = []
    for t in [0., .125, .5, 2., 8.]:
        multiplier = np.exp(-t*np.log(product/A)**2)
        kept = np.dot(terms, multiplier)
        removed = np.dot(terms, 1-multiplier)
        check_close(kept+removed+main, actual, 'retained product-heat complement')
        heats.append(dict(heat_time=t, retained=pair(kept), removed=pair(removed),
                          absolute_removed=float(np.dot(np.abs(terms.real), 1-multiplier))))
    result = dict(u=u, index=index, sigma=sigma, sample_is_numerical_zero=(sigma==.5),
        A=A, L=L, V=V, P=P, actual=pair(actual), source=pair(source),
        source_correction=pair(source_correction), continuous_main=pair(main),
        product_real_envelope=float(np.sum(np.abs(terms.real))),
        dyadic_product_real_envelope=float(sum(abs(r['signed'][0]) for r in shells)),
        dyadic_rectangle_real_envelope=float(sum(abs(r['signed'][0]) for r in table)),
        outer_row_real_envelope=float(np.dot(np.abs(weights), np.abs(rows.real))),
        shells=shells, rectangle_shells=table, heat=heats,
        coefficient_checks=coefficient_checks, kernel_checks=kernel_checks,
        reconstruction_error=float(max(abs(actual+source_correction-source),
            abs(actual-np.dot(weights, rows)), abs(main))))
    print(json.dumps({k:result[k] for k in ['u','index','sigma','actual',
        'dyadic_product_real_envelope','dyadic_rectangle_real_envelope',
        'product_real_envelope','outer_row_real_envelope','heat','reconstruction_error']},
        allow_nan=False), flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scales', nargs='+', type=int, default=[3,4,6])
    parser.add_argument('--zeros', nargs='+', type=int, default=[1,2])
    parser.add_argument('--real-parts', nargs='+', type=float, default=[.5,.75])
    parser.add_argument('--output', type=Path, default=Path('/tmp/eta-gamma-product-shells.json'))
    args=parser.parse_args()
    if min(args.scales)<2 or max(args.scales)>40 or min(args.zeros)<1 or any(not 0<s<1 for s in args.real_parts):
        parser.error('Require 2<=scale<=40, positive zero indices, and real parts in (0,1)')
    mp.mp.dps=50
    records=[]
    for u in args.scales:
        data=setup(u)
        for index in args.zeros:
            for sigma in args.real_parts:
                records.append(probe(u,index,sigma,data))
                args.output.write_text(json.dumps(records, indent=2, allow_nan=False)+'\n')


if __name__=='__main__':
    main()

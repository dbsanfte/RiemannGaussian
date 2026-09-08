#!/usr/bin/env python3
"""An exact harmonic balancing rule, tested on the full signed rectangle.

Coefficients agree with Mobius through L. The added interval (L,2L]
has constant coefficient -H_mu(L)/sum_(L<n<=2L) 1/n. The exact rational
harmonic moment is zero. Floating-point kernel values are diagnostics.
"""

import argparse
import json
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import numpy as np

from probe_eta_coprime_products import arithmetic_arrays, check_close, positive_integer
from probe_eta_gamma_high import low_eta_coefficients, survival, pair


def setup(u):
    A, L, V, P = u**6, u**2, u**5, 80*u**6
    mu, _, _ = arithmetic_arrays(P)
    inner = np.zeros(P+1, dtype=np.int64)
    for b in range(1, V+1):
        if mu[b]:
            inner[b::b] += int(mu[b])
    if inner[1] != 1 or np.any(inner[2:V+1]):
        raise ArithmeticError('Inner inverse check failed')
    original_cofactor = np.zeros(P+1, dtype=np.int64)
    for a in range(1, L+1):
        if mu[a]:
            original_cofactor[a:a*(P//a)+1:a] += int(mu[a])*inner[1:P//a+1]
    original_error = mu.astype(np.int64)+original_cofactor
    original_error[1:L+1] -= mu[1:L+1]
    original_error[1:V+1] -= mu[1:V+1]
    if np.any(original_error[:min(P,L*V)+1]):
        raise ArithmeticError('Original complementary cofactor support failed')
    H = sum(Fraction(int(mu[a]), a) for a in range(1, L+1))
    K = sum(Fraction(1, a) for a in range(L+1, 2*L+1))
    c = -H/K
    weights = [Fraction(int(mu[a])) if a <= L else c for a in range(1, 2*L+1)]
    if sum(w/Fraction(a) for a, w in enumerate(weights, 1)) != 0:
        raise ArithmeticError('Exact harmonic balancing failed')
    assert K >= Fraction(1, 2) and abs(c) <= 4
    return A, L, V, P, mu, inner, original_error, H, K, c, np.array([float(w) for w in weights])


def probe(u, index, sigma, data):
    A, L, V, P, mu, inner, original_error_coefficients, H, K, c, weights = data
    sm = mp.mpc(sigma, mp.zetazero(index).imag)
    s = complex(sm)
    alpha = 1-2*2**(-s)
    eta_s = complex((1-mp.power(2, 1-sm))*mp.zeta(sm))
    n = np.arange(1, P+1)
    x = n/A
    g = np.zeros(P, dtype=complex)
    g[:V] = np.polynomial.polynomial.polyval(x[:V], low_eta_coefficients(sm, 60))
    for q in range(1, P//(V+1)+1):
        length = P//q - V
        if length:
            g[V:V+length] += (1 if q%2 else -1)*q**(-s)*survival(q*x[V:V+length])
    f = np.r_[0j, np.exp(-s*np.log(n))*(g-eta_s*survival(x))/alpha]
    rows = np.array([-np.dot(inner[1:P//a+1], f[a:a*(P//a)+1:a]) for a in range(1, 2*L+1)])
    original = np.dot(mu[1:L+1], rows[:L])
    source = (survival(1/A)-2*2**(-s)*survival(2/A))/alpha
    source -= eta_s*np.dot(mu[1:], np.exp(-s*np.log(n))*survival(x))/alpha
    full = np.dot(mu,f)
    check_close(full, source, 'original source including the complete centering correction')
    balanced = np.dot(weights, rows)
    correction = float(c)*np.sum(rows[L:])
    check_close(balanced, original+correction, 'full signed balancing correction')
    # Complete the actual inner Mobius sum in the added outer interval.
    low_band = float(c)*np.sum(f[L+1:2*L+1])
    complementary_inner = -inner.copy()
    complementary_inner[1] += 1
    omitted = sum(float(c)*np.dot(complementary_inner[1:P//a+1], f[a:a*(P//a)+1:a])
                  for a in range(L+1, 2*L+1))
    check_close(correction, -low_band+omitted, 'balancing low band and complete product tail')
    original_left = np.dot(mu[1:L+1],f[1:L+1])
    original_right = np.dot(mu[1:V+1],f[1:V+1])
    original_error = np.dot(original_error_coefficients,f)
    check_close(original_left+original_right+original+original_error, source,
                'independent original source and cofactor coefficients')
    check_close(original_left+low_band+original_right+balanced+original_error-omitted,
                source, 'balanced source with every cost')
    result = dict(status='exact coefficient rule; numerical kernel comparison only', u=u,
        index=index, sigma=sigma, sample_is_numerical_zero=(sigma==.5), A=A, L=L, V=V, P=P,
        harmonic_prefix=str(H), added_harmonic_mass=str(K), constant_added_weight=str(c),
        exact_balanced_harmonic_moment='0', original=pair(original), balanced=pair(balanced),
        correction=pair(correction), added_low_band=pair(low_band), added_cofactor_tail=pair(omitted),
        balanced_source=pair(source), left_short=pair(original_left+low_band),
        right_short=pair(original_right), complementary_cofactor=pair(original_error-omitted),
        original_row_envelope=float(np.dot(np.abs(mu[1:L+1]), np.abs(rows.real[:L]))),
        balanced_row_envelope=float(np.dot(np.abs(weights), np.abs(rows.real))),
        balanced_ordinary_abel_envelope=float(np.sum(np.abs(np.r_[np.cumsum(weights)[:-1]*
            (rows.real[:-1]-rows.real[1:]), np.sum(weights)*rows.real[-1]]))),
        reconstruction_error=float(max(abs(balanced-original-correction), abs(correction+low_band-omitted),
            abs(original_left+low_band+original_right+balanced+original_error-omitted-source), abs(full-source))))
    print(json.dumps({k:result[k] for k in ['u','index','sigma','balanced','correction',
        'original_row_envelope','balanced_row_envelope','reconstruction_error']}, allow_nan=False), flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scales',nargs='+',type=positive_integer,default=[3,4,6])
    parser.add_argument('--zeros',nargs='+',type=positive_integer,default=[1,2])
    parser.add_argument('--real-parts',nargs='+',type=float,default=[.5,.75])
    parser.add_argument('--output',type=Path,default=Path('/tmp/eta-gamma-balanced-outer.json'))
    args=parser.parse_args()
    if min(args.scales)<2 or any(not 0<s<1 for s in args.real_parts):
        parser.error('Scales must be at least 2 and real parts must lie strictly between 0 and 1')
    mp.mp.dps=50
    records=[]
    for u in sorted(set(args.scales)):
        data=setup(u)
        for index in args.zeros:
            for sigma in args.real_parts:
                records.append(probe(u,index,sigma,data))
        args.output.write_text(json.dumps(records,indent=2,allow_nan=False)+'\n')


if __name__=='__main__':
    main()

#!/usr/bin/env python3
"""Full signed gamma rectangle with exact small-prime orbit folding.

Numerical exploration, not a zero certificate. A centered kernel is used;
the complete nonzero centering correction remains in the source identity.
No prime-divisible rows or cross terms are deleted.
"""

import argparse
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy

from probe_eta_gamma_balanced_outer import setup
from probe_eta_coprime_products import check_close
from probe_eta_gamma_high import low_eta_coefficients, pair, survival


def partitions(V, mu):
    indices = np.flatnonzero(mu[1:V+1]) + 1
    primes = np.array(list(sympy.primerange(2, V+1)), dtype=np.int64)
    prime_mask = np.zeros(V+1, dtype=bool)
    prime_mask[primes] = True
    records = []
    for y in sorted({1, 2, 3, 5, 7, 11, 17, 29, math.isqrt(V)+1}):
        core = indices.copy()
        for p in primes[primes <= y]:
            divisible = core % p == 0
            core[divisible] //= p
        smooth = indices // core
        if not np.array_equal(mu[indices], mu[smooth]*mu[core]):
            raise ArithmeticError('Small-prime multiplicativity failed')
        if np.any(np.gcd(smooth, core) != 1):
            raise ArithmeticError('Prime parts were not coprime')
        active_cores = np.unique(core)
        known = (active_cores == 1) | prime_mask[active_cores]
        records.append((y, indices, core, smooth, active_cores, known))
    return records


def prime_abel(V, y, mu, right_rows, actual):
    """Retain prime powers and both Abel endpoints in the prime-only case."""
    primes = list(sympy.primerange(2, V+1))
    smooth_mask = mu[1:V+1] != 0
    smooth_mask = np.r_[False, smooth_mask]
    for p in primes:
        if p > y:
            smooth_mask[p::p] = False
    smooth = np.flatnonzero(smooth_mask)
    weights = np.zeros(V+1, dtype=complex)
    for d in smooth:
        weights[1:V//d+1] += int(mu[d])*right_rows[d-1:d*(V//d):d]
    large_primes = np.array([p for p in primes if p > y], dtype=int)
    check_close(weights[1]-np.sum(weights[large_primes]), actual,
                'complete smooth part and prime-only core')
    von_mangoldt = np.zeros(V+1)
    proper_powers = np.zeros(V+1)
    for p in primes:
        n = p
        exponent = 1
        while n <= V:
            von_mangoldt[n] = math.log(p)
            if exponent >= 2:
                proper_powers[n] = 1/exponent
            n *= p
            exponent += 1
    indices = np.arange(y+1, V+1)
    f = weights[indices]/np.log(indices)
    powers = np.dot(proper_powers[indices], weights[indices])
    baseline = weights[1]-np.sum(f)+powers
    error = -np.dot(von_mangoldt[indices]-1, f)
    check_close(baseline+error, actual, 'all proper prime powers in prime sum')
    E = np.cumsum(von_mangoldt)-np.arange(V+1)
    interior = np.arange(y+1, V)
    differences = f[:-1]-f[1:]
    upper_endpoint = -E[V]*f[-1]
    lower_endpoint = E[y]*f[0]
    abel_interior = -np.dot(E[interior], differences)
    check_close(error, upper_endpoint+lower_endpoint+abel_interior,
                'both prime discrepancy Abel endpoints')
    actual_discrepancy_envelope = (abs(E[V]*f[-1].real)+abs(E[y]*f[0].real)
        + np.dot(np.abs(E[interior]), np.abs(differences.real)))
    chebyshev_envelope = 5*(V*abs(f[-1].real)+y*abs(f[0].real)
        + np.dot(interior, np.abs(differences.real)))
    if error.real > actual_discrepancy_envelope+2e-8:
        raise ArithmeticError('Prime discrepancy absolute comparison failed')
    return dict(prime_cutoff=y, smooth_coefficient_count=len(smooth), prime_count=len(large_primes),
        smooth_part=pair(weights[1]), proper_prime_powers=pair(powers), baseline=pair(baseline),
        discrepancy=pair(error), upper_endpoint=pair(upper_endpoint), lower_endpoint=pair(lower_endpoint),
        signed_abel_interior=pair(abel_interior),
        actual_discrepancy_absolute_upper=float(baseline.real+actual_discrepancy_envelope),
        chebyshev_five_n_upper=float(baseline.real+chebyshev_envelope),
        reconstruction_error=float(max(abs(actual-baseline-error),
            abs(error-upper_endpoint-lower_endpoint-abel_interior))))


def probe(u, index, sigma, data, groups, prime_audit=prime_abel):
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
        size = P//q-V
        if size:
            g[V:V+size] += (1 if q%2 else -1)*q**(-s)*survival(q*x[V:V+size])
    f = np.r_[0j, np.exp(-s*np.log(n))*(g-eta_s*survival(x))/alpha]
    full = np.dot(mu, f)
    source = (survival(1/A)-2*2**(-s)*survival(2/A))/alpha
    source -= eta_s*np.dot(mu[1:], np.exp(-s*np.log(n))*survival(x))/alpha
    check_close(full, source, 'complete centered source')
    # Fold the actual balanced outer vector into the complete zeta cofactor.
    outer_cofactor = np.zeros(P+1, dtype=float)
    for a, value in enumerate(weights, 1):
        outer_cofactor[a::a] += value
    right_rows = np.array([-np.dot(outer_cofactor[1:P//b+1], f[b:b*(P//b)+1:b])
                           for b in range(1, V+1)])
    actual = np.dot(mu[1:V+1], right_rows)
    # Independent other-order evaluation through the integer inner inverse.
    left_rows = np.array([-np.dot(inner[1:P//a+1], f[a:a*(P//a)+1:a])
                          for a in range(1, 2*L+1)])
    other_order = np.dot(weights, left_rows)
    check_close(actual, other_order, 'both complete convolution orders')
    original = np.dot(mu[1:L+1], left_rows[:L])
    left_low = np.dot(mu[1:L+1], f[1:L+1])
    right_low = np.dot(mu[1:V+1], f[1:V+1])
    cofactor_tail = np.dot(original_error, f)
    balancing_change = actual-original
    check_close(left_low+right_low+actual+cofactor_tail-balancing_change,
                source, 'all short, cofactor, and balancing costs')
    bound = float(np.sum(np.abs(mu[1:V+1]*right_rows.real)))
    result = dict(u=u, index=index, sigma=sigma, A=A, L=L, V=V, P=P,
        sample_is_numerical_zero=(sigma == .5), source=pair(source), actual=pair(actual),
        signed_source_correction=pair(left_low+right_low+cofactor_tail-balancing_change),
        absolute_source_correction=float(abs(left_low)+abs(right_low)+abs(cofactor_tail)+abs(balancing_change)),
        right_coordinate_envelope=bound,
        left_coordinate_envelope=float(np.dot(np.abs(weights), np.abs(left_rows.real))),
        reconstruction_error=float(max(abs(actual-other_order), abs(full-source),
            abs(left_low+right_low+actual+cofactor_tail-balancing_change-source))),
        orbits=[])
    previous = bound
    for y, indices, core, smooth, active_cores, known in groups:
        folded = np.zeros(V+1, dtype=complex)
        np.add.at(folded, core, mu[smooth]*right_rows[indices-1])
        reconstructed = np.dot(mu[active_cores], folded[active_cores])
        check_close(reconstructed, actual, 'all signed prime orbits')
        unsigned = float(np.sum(np.abs(folded[active_cores].real)))
        if unsigned > previous+2e-8:
            raise ArithmeticError('Nested prime orbit envelope increased')
        previous = unsigned
        known_value = np.dot(mu[active_cores[known]], folded[active_cores[known]])
        unknown_value = np.dot(mu[active_cores[~known]], folded[active_cores[~known]])
        unknown_envelope = float(np.sum(np.abs(folded[active_cores[~known]].real)))
        known_signed_upper = float(known_value.real+unknown_envelope)
        if actual.real > known_signed_upper+2e-8:
            raise ArithmeticError('Prime-signed comparison failed')
        # Independent divisor enumeration for the first and last surviving cores.
        checks=[]
        for k in sorted(set(active_cores[:2].tolist()+active_cores[-2:].tolist())):
            direct = sum(int(mu[d])*right_rows[d*k-1] for d in range(1, V//k+1)
                         if mu[d] and all(p <= y for p in sympy.factorint(d))
                         and math.gcd(d, k) == 1)
            check_close(direct, folded[k], 'independent smooth divisor enumeration')
            checks.append(float(abs(direct-folded[k])))
        result['orbits'].append(dict(prime_cutoff=y, core_count=len(active_cores),
            unknown_core_count=int(np.count_nonzero(~known)), orbit_envelope=unsigned,
            known_core_signed_value=pair(known_value), unknown_core_signed_value=pair(unknown_value),
            unknown_core_envelope=unknown_envelope, known_signed_upper=known_signed_upper,
            full_signed_upper_with_source_correction=known_signed_upper+result['signed_source_correction'][0],
            full_upper_with_absolute_source_correction=known_signed_upper+result['absolute_source_correction'],
            reconstruction_error=float(max(abs(reconstructed-actual), *checks))))
    result['prime_abel'] = prime_audit(V, math.isqrt(V)+1, mu, right_rows, actual)
    print(json.dumps({k:result[k] for k in ['u','index','sigma','actual','right_coordinate_envelope',
        'left_coordinate_envelope','prime_abel','reconstruction_error']}, allow_nan=False), flush=True)
    return result


def main(prime_audit=prime_abel, default_output='/tmp/eta-gamma-prime-orbits.json'):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scales',nargs='+',type=int,default=[3,4,6])
    parser.add_argument('--zeros',nargs='+',type=int,default=[1,2])
    parser.add_argument('--real-parts',nargs='+',type=float,default=[.5,.75])
    parser.add_argument('--output',type=Path,default=Path(default_output))
    args=parser.parse_args()
    if min(args.scales)<2 or min(args.zeros)<1 or any(not 0<s<1 for s in args.real_parts):
        parser.error('Scales >=2, zero indices >=1, and real parts in (0,1) are required')
    mp.mp.dps=50
    records=[]
    for u in sorted(set(args.scales)):
        data=setup(u)
        groups=partitions(data[2],data[4])
        for index in args.zeros:
            for sigma in args.real_parts:
                records.append(probe(u,index,sigma,data,groups,prime_audit))
                args.output.write_text(json.dumps(records,indent=2,allow_nan=False)+'\n')


if __name__=='__main__':
    main()

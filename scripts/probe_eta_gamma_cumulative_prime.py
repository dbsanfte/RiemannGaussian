#!/usr/bin/env python3
"""Second Abel audit with the complete continuous/discrete correction.

Numerical exploration, not a zero certificate. Retain all the source,
centering, and prime-power terms from the prime-orbit probe. Compare signed
second Abel summation with absolute envelopes, and separate the first
difference into cutoff jumps and a common-divisor part. All CLI options
match probe_eta_gamma_prime_orbits.py.
"""

import math

import numpy as np
import sympy

import probe_eta_gamma_prime_orbits as base
from probe_eta_coprime_products import check_close
from probe_eta_gamma_high import pair


def cumulative_prime_abel(V, y, mu, rows, actual):
    result = base.prime_abel(V, y, mu, rows, actual)
    # Independently list squarefree smooth numbers using prime subsets.
    smooth = [1]
    primes = list(sympy.primerange(2, V+1))
    for p in primes:
        if p > y:
            break
        smooth += [d*p for d in smooth if d*p <= V]
    if len(set(smooth)) != len(smooth):
        raise ArithmeticError('Prime-subset enumeration is not unique')
    W = np.zeros(V+1, dtype=complex)
    for d in smooth:
        W[1:V//d+1] += int(mu[d])*rows[d-1:d*(V//d):d]
    check_close(W[1], complex(*result['smooth_part']),
                'independent smooth-prime-subset enumeration')
    indices = np.arange(y+1, V+1)
    f = W[indices]/np.log(indices)
    first = f[:-1]-f[1:]
    second = first[:-1]-first[1:]
    von_mangoldt = np.zeros(V+1)
    for p in primes:
        q = p
        while q <= V:
            von_mangoldt[q] = math.log(p)
            q *= p
    E = np.cumsum(von_mangoldt)-np.arange(V+1)
    D = np.cumsum(E)
    # Suzuki's continuous primitive at n+1 differs by n/2.
    n = np.arange(V+1)
    triangular = (n+1)*np.cumsum(von_mangoldt)-np.cumsum(n*von_mangoldt)
    continuous = triangular-((n+1)**2-1)/2
    check_close(D, continuous+n/2, 'continuous primitive and full lattice correction')
    outer = -E[V]*f[-1]+E[y]*f[0]
    second_upper = -D[V-1]*first[-1]
    second_lower = D[y]*first[0]
    interior_indices = np.arange(y+1, V-1)
    interior = -np.dot(D[interior_indices], second)
    discrepancy = outer+second_upper+second_lower+interior
    check_close(discrepancy, complex(*result['discrepancy']), 'complete second Abel identity')
    # Hold the original endpoints signed; compare only the remaining terms.
    actual_envelope = (abs(D[V-1]*first[-1].real)+abs(D[y]*first[0].real)
        + np.dot(np.abs(D[interior_indices]), np.abs(second.real)))
    continuous_envelope = 2.5*((n+1)**2-1)+n/2
    naive_envelope = 2.5*n*(n+1)
    analytic_cost = (naive_envelope[V-1]*abs(first[-1].real)
        + naive_envelope[y]*abs(first[0].real)
        + np.dot(naive_envelope[interior_indices], np.abs(second.real)))
    suzuki_cost = (continuous_envelope[V-1]*abs(first[-1].real)
        + continuous_envelope[y]*abs(first[0].real)
        + np.dot(continuous_envelope[interior_indices], np.abs(second.real)))
    # Separate first differences caused by removed smooth divisors at V/d.
    jump = np.zeros(V-y-1, dtype=complex)
    for i, k in enumerate(range(y+1, V)):
        jump[i] = sum(int(mu[d])*rows[d*k-1]/math.log(k) for d in smooth
                      if V//(k+1) < d <= V//k)
    bulk = first-jump
    check_close(-np.dot(E[np.arange(y+1,V)], jump+bulk),
                complex(*result['signed_abel_interior']), 'cutoff jumps and retained bulk')
    baseline = complex(*result['baseline'])
    result['cumulative'] = dict(
        second_upper_endpoint=pair(second_upper), second_lower_endpoint=pair(second_lower),
        second_signed_interior=pair(interior),
        second_actual_absolute_upper=float(baseline.real+outer.real+actual_envelope),
        second_pointwise_five_n_upper=float(baseline.real+outer.real+analytic_cost),
        second_continuous_suzuki_upper=float(baseline.real+outer.real+suzuki_cost),
        first_cutoff_jump_signed=pair(-np.dot(E[np.arange(y+1,V)], jump)),
        first_bulk_signed=pair(-np.dot(E[np.arange(y+1,V)], bulk)),
        first_cutoff_jump_five_n_cost=float(5*np.dot(np.arange(y+1,V),np.abs(jump.real))),
        first_bulk_five_n_cost=float(5*np.dot(np.arange(y+1,V),np.abs(bulk.real))),
        first_jump_absolute_variation=float(np.sum(np.abs(jump.real))),
        first_bulk_absolute_variation=float(np.sum(np.abs(bulk.real))),
        reconstruction_error=float(abs(discrepancy-complex(*result['discrepancy']))))
    return result


if __name__ == '__main__':
    base.main(cumulative_prime_abel, '/tmp/eta-gamma-cumulative-prime.json')

#!/usr/bin/env python3
"""Optional signed cofactor-main diagnostic, outside CI.

Actual squarefree integers and ordinary primes are enumerated in a literal
radial/physical window. The largest prime exceeds its whole cofactor.
The owner allocation and full product phase are retained. Nonowner allocation
is omitted here; its existing eventual theorem is NOT a finite error bound
for these sample orders. This is a few-column diagnostic, not the whole core,
not a certified bound, and not evidence for an eventual source-scale floor.
The squarefree density is evaluated by its classical Euler product formula;
this floating computation does not evaluate the Lean counting constant.
"""
import argparse
import json
import math
import time

import numpy as np
from probe_riesz_retained_factorial import unpaid_orders


def arithmetic(limit):
    prime = np.ones(limit + 1, dtype=bool)
    prime[:2] = False
    for p in range(2, math.isqrt(limit) + 1):
        if prime[p]:
            prime[p*p::p] = False
    ps = np.flatnonzero(prime)
    mu = np.ones(limit + 1, dtype=np.int8)
    mu[0] = 0
    for p in ps:
        mu[p::p] *= -1
        if p*p <= limit:
            mu[p*p::p*p] = 0
    return prime, mu


def next_prime(n):
    while n < 2 or any(n % d == 0 for d in range(2, math.isqrt(n) + 1)):
        n += 1
    return n


def density(d):
    out, rest = 6 / math.pi**2, d
    p = 2
    while p*p <= rest:
        if rest % p == 0:
            out /= p + 1
            while rest % p == 0:
                rest //= p
        p += 1
    if rest > 1:
        out /= rest + 1
    return out


def column(order, log_p, heights):
    started = time.monotonic()
    u = 10001/20000
    physical = (math.floor(u**(-order)/(order+1)) + 2)**2
    length = math.log(physical)
    p = next_prime(math.ceil(math.exp(log_p)))
    if p >= physical:
        raise ValueError('Marked prime lies beyond original physical cutoff')
    # Largest prime exceeds the cofactor. Both annulus endpoints retained.
    lower = max(math.floor(math.exp(1.971*order)/p), physical//p)
    upper = min(math.floor(math.exp(2.029*order)/p), p-1,
                (physical*physical-1)//p)
    if upper <= lower:
        raise ValueError('Empty literal radial/physical intersection')
    prime, mu = arithmetic(upper)
    ns = np.arange(lower+1, upper+1)
    total = math.log(p) + np.log(ns)
    B = length-math.log(p)
    cutoff = math.floor(math.exp(B))
    assert cutoff**2 <= lower
    assert total.min() > 1.971*order
    assert total.max() <= 2.029*order+1e-12
    assert (math.log(p) < .65*total).all()
    owner = sum(math.comb(order+1, k)
                *(np.log(ns)/total)**k*(math.log(p)/total)**(order+1-k)
                for k in unpaid_orders(order))
    amplitude = (-(1-owner)*u**(order+1)/(length*math.factorial(order)*p)
                 *np.exp(-total/2)*total**(order+1))
    response = np.zeros(len(ns))
    main_density = 0.
    for d in range(1, cutoff+1):
        v = int(mu[d])*max(0., B-math.log(d))
        response[ns % d == 0] += v
        main_density += v*density(d)
    sf = mu[ns] != 0
    comp = sf & ~prime[ns]
    rows = []
    for y in heights:
        w = amplitude*np.cos(y*total)/ns
        # Original two-hinge response equals minus R_B on these composites.
        actual = -float(np.dot(w[comp], response[comp]))
        density_term = -main_density*float(w.sum())
        prime_term = B*float(w[prime[ns]].sum())
        model = density_term + prime_term
        denominator = abs(density_term) + abs(prime_term)
        rows.append(dict(height=y, normalizedLiteralOwnerColumn=actual,
                         signedDensityMain=density_term,
                         signedPrimeSubtraction=prime_term,
                         signedMain=model, countingDiscrepancy=actual-model,
                         signedMainOverSeparatedAbs=(abs(model)/denominator
                                                    if denominator else 0.),
                         fullPhaseRetained=True))
    return dict(order=order, markedPrime=p, length=length, cofactorLower=lower,
                cofactorUpper=upper, shortDivisorCutoff=cutoff,
                squarefreeCompositeCount=int(comp.sum()),
                primeCofactorCount=int(prime[ns].sum()),
                nonemptyPhysicalAnnulus=True,
                allOriginalMasksVerified=False, nonownerAllocationIncluded=False,
                actualTwoHingesReducedBySaturation=True,
                sourceFloorCertified=False, rows=rows,
                elapsedSeconds=time.monotonic()-started)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=16)
    parser.add_argument('--log-primes', type=float, nargs='+', default=[15.79,16.,16.3])
    parser.add_argument('--heights', type=float, nargs='+', default=[0.,54.,108.])
    args = parser.parse_args()
    print(json.dumps(dict(scope=__doc__.strip(), columns=[
        column(args.order, t, args.heights) for t in args.log_primes]), indent=2))

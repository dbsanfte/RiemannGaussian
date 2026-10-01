#!/usr/bin/env python3
"""Optional literal finite-prime diagnostic; not a certificate or a floor.

Join every complete/clipped phase period in 1.95N < log(n) <= 2.03N.
The finite population has distinct prime factors in (N^2, (cutoff+2)^2),
unique largest-prime ownership and largest share < 13/20. All feasible
counts, factorial allocation orders, divisor signs and phases are retained.

This is a selected atom population, NOT the full coreBand. In particular,
at these small orders the original annulus may exclude every tested label.
The annulus-compatible count is reported explicitly. No large-order prime
density, asymptotic cancellation or source-scale estimate is inferred.
"""

import argparse
import json
import math
from itertools import combinations

import numpy as np
from scipy.stats import binom

from probe_riesz_fixed_count_period import riesz, unpaid_orders


def row(n, y):
    u = 10001 / 20000
    cutoff = 20000**n // (10001**n * (n + 1))
    physical_upper = (cutoff + 2)**2
    length = 2 * math.log(cutoff + 2)
    tlo, thi = 1.95*n, 2.03*n
    nmax = math.floor(math.exp(thi))
    nmin = math.exp(tlo)
    prime = np.ones(physical_upper, dtype=bool)
    prime[:2] = False
    for p in range(2, math.isqrt(physical_upper - 1) + 1):
        if prime[p]:
            prime[p*p::p] = False
    primes = np.flatnonzero(prime)
    primes = primes[primes > n*n]
    orders = unpaid_orders(n)
    totals = dict(signed=0., owner_signed=0., moment0=0., moment1=0.,
                  signed_crossing=0., unit_b=0., prime_b=0., composite_b=0.)
    periods = {}
    counts = {}
    labels = annulus_labels = 0
    error = 0.

    def visit(factors, a, start):
        nonlocal labels, annulus_labels, error
        if len(factors) >= 2:
            low = max(factors[-1], nmin/a)
            high = min(physical_upper-1, nmax//a)
            first = np.searchsorted(primes, low, side='right')
            last = np.searchsorted(primes, high, side='right')
            ps = primes[first:last]
            if len(ps):
                logs = np.log(factors)
                loga = math.log(a)
                total = np.log(ps) + loga
                good = np.log(ps) < .65*total
                ps, total = ps[good], total[good]
                if len(ps):
                    centers = (2*np.floor(y*total/(2*math.pi))+1)*math.pi/y
                    allocated = np.zeros_like(total)
                    owner_allocated = np.zeros_like(total)
                    for k in orders:
                        owner_allocated += binom.pmf(k, n+1, loga/total)
                    allocated += owner_allocated
                    for lp in logs:
                        for k in orders:
                            allocated += binom.pmf(k, n+1, 1-lp/total)
                    base = (np.exp(-total/2+(n+1)*np.log(total)-math.lgamma(n+1)) /
                            (length*ps*a)*np.cos(y*total))
                    weight = base*(1-allocated)
                    owner_weight = base*(1-owner_allocated)
                    parity = (-1)**len(factors)
                    response = (riesz(total-length, logs) -
                                riesz(np.full_like(total, loga-length), logs))
                    r0 = (riesz(centers-length, logs) -
                          riesz(np.full_like(total, loga-length), logs))
                    slope = np.zeros_like(total)
                    components = {0: np.zeros_like(total),
                                  1: np.zeros_like(total),
                                  2: np.zeros_like(total)}
                    for size in range(len(factors)+1):
                        for subset in combinations(range(len(factors)), size):
                            logd = sum(float(logs[i]) for i in subset)
                            slope += (-1)**size*(centers-length > logd)
                            logb = loga-logd
                            hinge = (np.maximum(np.log(ps)+logb-length, 0) -
                                     max(logb-length, 0))
                            bcount = len(factors)-size
                            kind = min(bcount, 2)
                            components[kind] += (-1)**bcount*hinge
                    joined = sum(components.values())
                    error = max(error, float(np.max(abs(joined-parity*response))))
                    m0 = weight*parity*r0
                    m1 = weight*parity*slope*(total-centers)
                    signed = weight*parity*response
                    crossing = signed-m0-m1
                    values = dict(signed=signed, owner_signed=owner_weight*joined,
                                  moment0=m0, moment1=m1, signed_crossing=crossing,
                                  unit_b=weight*components[0],
                                  prime_b=weight*components[1],
                                  composite_b=weight*components[2])
                    for key, vals in values.items():
                        totals[key] += float(vals.sum())
                    count = len(factors)+1
                    counts[count] = counts.get(count, 0)+len(ps)
                    period_ids = np.floor(y*total/(2*math.pi)).astype(int)
                    for period in np.unique(period_ids):
                        selected = period_ids == period
                        entry = periods.setdefault(int(period),
                            {key: 0. for key in totals})
                        for key, vals in values.items():
                            entry[key] += float(vals[selected].sum())
                    labels += len(ps)
                    annulus_labels += int(((total > length) & (total < 2*length)).sum())
        for i in range(start, len(primes)):
            q = int(primes[i])
            if a*q*q >= nmax:
                break
            visit([*factors, q], a*q, i+1)

    visit([], 1, 0)
    scale = u**(n+1)
    return dict(N=n, y=y, moving_length=length, labels=labels,
                annulus_compatible_labels=annulus_labels, counts=counts,
                signed_totals=totals,
                source_normalized={key: scale*val for key, val in totals.items()},
                periods={str(i): {key: scale*val for key, val in entry.items()}
                         for i, entry in sorted(periods.items())},
                divisor_complement_roundoff=error,
                moment_crossing_ledger_roundoff=abs(
                    totals['signed']-totals['moment0']-totals['moment1']-
                    totals['signed_crossing']),
                convolution_ledger_roundoff=abs(
                    totals['signed']-totals['unit_b']-totals['prime_b']-
                    totals['composite_b']))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[8, 10])
    parser.add_argument('--height', type=float, default=54.)
    args = parser.parse_args()
    if args.height <= 0:
        parser.error('--height must be positive')
    print(json.dumps({'scope': __doc__,
                      'rows': [row(n, args.height) for n in args.orders]}, indent=2))

#!/usr/bin/env python3
"""Optional floating-point probes for the global Riesz crossing bound.

Neither output is a certificate. The aggregate probe includes every integer
cofactor via exact divisor incidence (harmonic values use floating point).
--literal also enumerates finite uniquely owned prime labels, retaining the
actual damped length, unpaid factorial orders, allocation and cosine phase.
Its small orders and extra physical selection do not model the full endgame.
"""
import argparse
import json
import math
from itertools import combinations

import numpy as np
from scipy.special import digamma
from scipy.stats import binom
from probe_riesz_fixed_count_period import unpaid_orders, riesz


def aggregate_rows():
    h = math.pi / 54
    limit = int(math.exp(.307 * 50 + h)) + 1
    squarefree = np.ones(limit + 1, dtype=bool)
    squarefree[0] = False
    prime = np.ones(math.isqrt(limit) + 1, dtype=bool)
    prime[:2] = False
    for p in range(2, len(prime)):
        if prime[p]:
            prime[p*p::p] = False
            squarefree[p*p::p*p] = False
    rows = []
    for v in (12., 20., 30., 40., 50.):
        d, x = .307 * v, int(math.exp(.985 * v))
        ds = np.arange(max(1, math.ceil(math.exp(d-h))),
                       math.floor(math.exp(d+h)) + 1, dtype=np.int64)
        tent = np.maximum(0, h - abs(d - np.log(ds)))
        quot = np.array([x // int(j) for j in ds], dtype=np.float64)
        harmonic = digamma(quot + 1) + np.euler_gamma
        mass = float(np.sum(squarefree[ds] * tent / ds * harmonic))
        bound = (1 + math.log(x)) * h * (math.expm1(2*h) + math.exp(h-d))
        rows.append({
            'v': v, 'cutoff': d, 'half_period': h,
            'all_integer_crossing_majorant': mass,
            'proved_bound_evaluated_in_float': bound,
            'coarse_all_divisor_comparison': h * (1 + math.log(x))**2,
            'mass_over_v_h_squared': mass / (v*h*h),
        })
    return rows


def literal_row(n, y=54.):
    cut = pow(20000, n) // (pow(10001, n) * (n+1))
    upper = (cut+2)**2
    length = 2 * math.log(cut+2)
    h = math.pi / y
    v = (2 * math.ceil((2*n*y-math.pi)/(2*math.pi)) + 1) * math.pi/y
    lo_t, hi_t = max(v-h, 1.95*n), min(v+h, 2.03*n)
    prime = np.ones(upper, dtype=bool)
    prime[:2] = False
    for p in range(2, math.isqrt(upper-1)+1):
        if prime[p]:
            prime[p*p::p] = False
    primes = np.flatnonzero(prime)
    primes = primes[primes > n*n]
    orders = unpaid_orders(n)
    nmax = int(math.exp(hi_t))
    nmin = math.exp(lo_t)
    actual = affine = max_mass = 0.
    constant_moment = first_moment = profile_cost = 0.
    owner_only = nonowner_absolute = max_nonowner_ratio = 0.
    by_count = {}
    labels = cofactors = xmax = 0
    counts = {}
    identity_error = 0.

    def visit(factors, product, start):
        nonlocal actual, affine, max_mass, labels, cofactors, xmax, identity_error
        nonlocal constant_moment, first_moment, profile_cost
        nonlocal owner_only, nonowner_absolute, max_nonowner_ratio
        if len(factors) >= 2:
            lower = max(factors[-1], nmin/product)
            upper_p = min(upper-1, nmax//product)
            ps = primes[(primes > lower) & (primes <= upper_p)]
            if len(ps):
                logs = np.log(factors)
                b = math.log(product)
                total = np.log(ps) + b
                ps = ps[np.log(ps) <= (1189/2000)*total]
                if len(ps):
                    total = np.log(ps) + b
                    allocation = np.zeros_like(total)
                    owner_allocation = np.zeros_like(total)
                    for k in orders:
                        owner_allocation += binom.pmf(k, n+1, b/total)
                    for lp in [np.log(ps), *[np.full_like(total, z) for z in logs]]:
                        for k in orders:
                            allocation += binom.pmf(k, n+1, 1-lp/total)
                    weight = ((-1)**(len(factors)+2)/length * (1-allocation) *
                              np.exp(-total/2 + (n+1)*np.log(total) - math.lgamma(n+1)) /
                              ps * np.cos(y*total))
                    response = riesz(total-length, logs)-riesz(np.full_like(total, b-length), logs)
                    r0 = float(riesz(np.array([v-length]), logs)[0] -
                               riesz(np.array([b-length]), logs)[0])
                    slope = sum((-1)**len(subset)
                                for k in range(len(factors)+1)
                                for subset in combinations(logs, k)
                                if sum(subset) < v-length)
                    direct = float(np.dot(weight, response))/product
                    base_weight = ((-1)**(len(factors)+2)/length *
                                   np.exp(-total/2 + (n+1)*np.log(total) - math.lgamma(n+1)) /
                                   ps * np.cos(y*total))
                    owner_only += float(np.dot(base_weight*(1-owner_allocation), response))/product
                    nonowner_absolute += float(np.sum(abs(base_weight*response)*
                                                       (allocation-owner_allocation)))/product
                    max_nonowner_ratio = max(max_nonowner_ratio,
                        float(np.max(allocation-owner_allocation)) /
                        (len(factors)*math.exp(-n/64)))
                    m0 = r0*float(weight.sum())/product
                    m1 = slope*float(np.dot(weight, total-v))/product
                    actual += direct
                    affine += m0+m1
                    constant_moment += m0
                    first_moment += m1
                    local_tent = sum(max(0., h-abs(v-length-sum(subset)))
                                     for k in range(len(factors)+1)
                                     for subset in combinations(logs,k))
                    profile_cost += float(abs(weight).sum())*local_tent/product
                    c = by_count.setdefault(len(factors)+1, {'signed':0.,'constant':0.,'first':0.})
                    c['signed'] += direct
                    c['constant'] += m0
                    c['first'] += m1
                    max_mass = max(max_mass, float(abs(weight).sum()))
                    # Check the full-label response, rather than only its reflected form.
                    full = np.zeros_like(total)
                    for k in range(len(factors)+1):
                        for subset in combinations(logs, k):
                            full += (-1)**k * (np.maximum(length-sum(subset), 0) -
                                np.maximum(length-sum(subset)-np.log(ps), 0))
                    identity_error = max(identity_error,
                        float(abs(full-(-1)**(len(factors)+1)*response).max()))
                    labels += len(ps)
                    cofactors += 1
                    xmax = max(xmax, product)
                    counts[len(factors)+1] = counts.get(len(factors)+1, 0) + len(ps)
        for i in range(start, len(primes)):
            q = int(primes[i])
            if product*q*q >= nmax:
                break
            visit([*factors, q], product*q, i+1)

    visit([], 1, 0)
    bound = max_mass*(1+math.log(max(1, xmax)))*h*(math.expm1(2*h)+math.exp(h-(v-length)))
    return {'N': n, 'labels': labels, 'cofactors': cofactors, 'counts': counts,
            'moving_length': length, 'center': v, 'signed_literal_sum': actual,
            'retained_affine_moments': affine, 'signed_crossing_error': actual-affine,
            'constant_moment': constant_moment, 'first_moment': first_moment,
            'literal_profile_cost': profile_cost, 'signed_by_count': by_count,
            'signed_owner_only_sum': owner_only,
            'signed_nonowner_difference': actual-owner_only,
            'source_normalized_nonowner_difference': (10001/20000)**(n+1)*(actual-owner_only),
            'source_normalized_nonowner_absolute_mass': (10001/20000)**(n+1)*nonowner_absolute,
            'max_nonowner_share_over_proved_count_bound': max_nonowner_ratio,
            'proved_error_bound_evaluated_in_float': bound,
            'source_normalized_error': (10001/20000)**(n+1)*(actual-affine),
            'reflection_identity_roundoff': identity_error}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--literal', action='store_true')
    args = parser.parse_args()
    result = {'scope': __doc__, 'aggregate': aggregate_rows()}
    if args.literal:
        result['literal'] = [literal_row(n) for n in (6, 8, 10)]
    print(json.dumps(result, indent=2))

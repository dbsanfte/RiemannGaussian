#!/usr/bin/env python3
"""Optional joined smooth-tail diagnostics; never an ordinary CI certificate.

The small actual-prime blocks are below the proved, unevaluated arithmetic
threshold. Large-order budgets use a smooth saddle and binomial caps, not
the exact retained coefficients or a partition of the whole carrier. Mean
constants are omitted; no whole floor, ceiling or source decay is inferred.
"""
import json
import math

import numpy as np

from probe_riesz_prime_tail_energy import primes_to
from probe_riesz_retained_factorial import binomial_weights
from probe_riesz_retained_discrepancy import block
from probe_riesz_joint_period_energy import numerical_budget


def smooth_tail_check(j, periods, phase):
    a, y = 10., 54.
    h, b = 2*math.pi/y, a+periods*2*math.pi/y
    w = min(math.exp(-a/2)*b**j, math.exp(-j)*(2*j)**j)
    bound = 2*w/(a*y)
    nodes, weights = np.polynomial.legendre.leggauss(32)
    ratios = []
    for lower in np.linspace(a, b, 41):
        edges = np.linspace(lower, b, max(1, math.ceil((b-lower)/h))+1)
        parts = []
        for lo, hi in zip(edges[:-1], edges[1:]):
            t = lo+(nodes+1)*(hi-lo)/2
            parts.append(float((hi-lo)/2*np.dot(weights,
                np.exp(-t/2)*t**(j-1)*np.cos(y*(t+phase)))))
        ratios.append(abs(math.fsum(parts))/bound)
    assert max(ratios) <= 1+2e-10
    return dict(order=j, periods=periods, phase=phase,
                testedPartialTails=len(ratios), maximumTailOverBound=max(ratios))


def actual_block(primes, order, count, eligible):
    row = block(primes, order, count, eligible)
    a, y, length, shell = 10., 54., 12., 128
    b = a+count*2*math.pi/y
    terms = []
    for j in range(order+2):
        w = min(math.exp(-a/2)*b**j, math.exp(-j)*(2*j)**j)
        terms.append(math.comb(order+1, j)*math.log(2*shell)**(order+1-j)*2*w/(a*y))
    smooth_cost = (math.exp(-math.log(shell)/2)*math.sqrt(b)
                   /(length*math.factorial(order))*math.fsum(terms))
    row['smoothCostWithoutSqrtE'] = smooth_cost
    row['joinedCostWithoutSqrtE'] = smooth_cost+row['eventualCostWithoutSqrtE']
    return row


def order_comparison(n, count):
    row = numerical_budget(n, count)
    j, y = row['factorialOrder'], 54.
    a, b = row['lowestPrimeLog'], row['lowestPrimeLog']+count*2*math.pi/y
    peak = -j+j*math.log(2*j)
    w = math.exp(min(-a/2+j*math.log(b)-peak, 0.))
    score = abs(j/a-.5)+j*(b-a)/a**2
    cost = math.sqrt(b)*w*(2/(a*y)+5*(2+(score+y+2)*(b-a))/a**3)
    row['newJoinedCostOverFactorialPeak'] = cost
    row['newOverPreviousJoinedCost'] = cost/row['jointCostOverFactorialPeak']
    row['scope'] = 'Single saddle order, explicit costs only; different unevaluated E omitted.'
    return row


def all_order_budget(n, count):
    m, y, u, share = n+1, 54., 10001/20000, .55
    h, center, cofactor_log = 2*math.pi/y, 2*share*m, 2*(1-share)*m
    a, b = center-count*h/2, center+count*h/2
    orders = np.arange(m+1, dtype=float)
    probability = np.asarray(binomial_weights(m, share))
    log_peak = np.zeros(m+1)
    log_peak[1:] = -orders[1:]+orders[1:]*np.log(2*orders[1:])
    log_peak -= -center/2+orders*math.log(center)
    log_endpoint = -(a-center)/2+orders*math.log(b/center)
    w = np.exp(np.minimum(log_peak, log_endpoint))
    score = np.abs(orders/a-.5)+orders*(b-a)/a**2
    smooth = w*2/(a*y)
    discrepancy = 5*w*(2+(score+y+2)*(b-a))/a**3
    averaged = float(probability @ (smooth+discrepancy))*math.sqrt(b)
    length = -2*n*math.log(u)
    log_prefactor = (m*math.log(u)-(cofactor_log-math.log(2))/2-center/2
                    +m*math.log(2*m)-math.lgamma(n+1)-math.log(length))
    return dict(N=n, periodCount=count, includedOrders=m+1,
                sourceNormalizedJoinedBudgetWithoutSqrtE_log10=
                    (log_prefactor+math.log(averaged))/math.log(10),
                discrepancyOverSmooth=float(probability @ discrepancy)/float(probability @ smooth))


if __name__ == '__main__':
    primes = primes_to(math.ceil(math.exp(12.)))
    result = dict(scope=__doc__.strip(),
        smoothChecks=[smooth_tail_check(j, periods, phase)
                      for j in [0, 1, 5, 16, 32] for periods in [1, 16] for phase in [0., .37]],
        actualPrimeBlocks=[actual_block(primes, n, periods, eligible)
                           for n in [8, 16, 32, 64] for periods in [1, 16] for eligible in [False, True]],
        previousCostComparison=[order_comparison(n, count)
                                for n in [16384, 65536, 262144] for count in [16, 256, 4096]],
        sourceBudgets=[all_order_budget(n, count)
                       for n in [16384, 65536, 262144, 1048576] for count in [16, 4096]])
    print(json.dumps(result, indent=2))

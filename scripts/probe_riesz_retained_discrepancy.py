#!/usr/bin/env python3
"""Optional finite diagnostics for the literal retained discrepancy theorem.

Actual primes, squarefree cofactors, the full allocation polynomial, both
Riesz hinges and cos(y log(pn)) are retained. Floating arithmetic/quadrature
are not certificates. Log-prime endpoints near ten are below the proved
but unevaluated eventual threshold; no E value or source floor is inferred.
The common blocks below do not assert the whole carrier's ownership masks.
Never run this exploratory script in ordinary CI.
"""
import json
import math

import numpy as np

from probe_riesz_prime_tail_energy import primes_to
from probe_riesz_retained_factorial import unpaid_orders
from probe_riesz_discrepancy_energy import mu_divisors
from probe_riesz_joint_prime_error import all_order_error


def coefficients(n, logs, eligible):
    m, total = n+1, sum(logs)
    orders = unpaid_orders(n)
    out = []
    for j in range(m+1):
        fraction = float(m-j not in orders)
        for q in eligible:
            share = q/total
            fraction -= math.fsum(math.comb(m-j, k-j)*(1-share)**(k-j)*share**(m-k)
                                  for k in orders if k >= j)
        assert -2e-12 <= fraction <= 1+2e-12
        out.append(math.comb(m, j)*total**(m-j)*max(0., fraction))
    return np.asarray(out)


def block(primes, order, periods, include_cofactor_primes):
    a, y, length, shell = 10., 54., 12., 128
    b = a+periods*2*math.pi/y
    ps = primes[(primes > math.exp(a)) & (primes <= math.exp(b))]
    ts = np.log(ps)
    nodes, quadrature = np.polynomial.legendre.leggauss(32)
    rows = []
    for factors in [[11, 13], [3, 5, 11], [2, 3, 5, 7]]:
        n = math.prod(factors)
        assert shell < n <= 2*shell
        logs = [math.log(q) for q in factors]
        total = sum(logs)
        eligible = logs if include_cofactor_primes else []
        bs = coefficients(order, logs, eligible)
        m, orders = order+1, unpaid_orders(order)
        poly = np.polynomial.polynomial.polyval(ts, bs)
        theta = np.zeros_like(ts)
        for q in [ts, *eligible]:
            theta += sum(math.comb(m, k)*((ts+total-q)/(ts+total))**k
                         *(q/(ts+total))**(m-k) for k in orders)
        direct_polynomial = (1-theta)*(ts+total)**m
        relative_identity_error = float(np.max(np.abs(poly-direct_polynomial)
                                               /np.maximum(poly, 1e-100)))
        assert relative_identity_error < 2e-8
        divs = mu_divisors(factors)

        def response(t):
            return sum(sign*(max(0., length-math.log(d))
                             -np.maximum(0., length-t-math.log(d))) for d, sign in divs)

        prefactor = -math.exp(-total/2)/(length*math.factorial(order)*n)
        actual = float(prefactor*np.sum(np.exp(-ts/2)*direct_polynomial
                                       *np.cos(y*(ts+total))*response(ts)/ps))
        expanded = float(prefactor*np.sum(np.exp(-ts/2)*poly
                                         *np.cos(y*(ts+total))*response(ts)/ps))
        boundaries = {a, b}
        boundaries.update(length-math.log(d) for d, _ in divs
                          if a < length-math.log(d) < b)
        boundaries.update(a+i*2*math.pi/y for i in range(1, periods))
        edges = sorted(boundaries)
        smooth_parts = []
        for lo, hi in zip(edges[:-1], edges[1:]):
            t = lo+(nodes+1)*(hi-lo)/2
            val = (np.exp(-t/2)*np.polynomial.polynomial.polyval(t, bs)
                   *np.cos(y*(t+total))*response(t)/t)
            smooth_parts.append(float((hi-lo)/2*np.dot(quadrature, val)))
        smooth = prefactor*math.fsum(smooth_parts)
        rows.append(dict(n=n, totalPrimeCount=len(factors)+1,
                         allocationIdentityRelativeError=relative_identity_error,
                         retainedOrderZero=float(bs[0]), retainedOrderOne=float(bs[1]),
                         literalRetainedResponse=actual, expandedResponse=expanded,
                         signedSmoothResponse=smooth, arithmeticDiscrepancy=actual-smooth))
    errors = []
    for j in range(order+2):
        w = min(math.exp(-a/2)*b**j, math.exp(-j)*(2*j)**j)
        score = abs(j/a-.5)+j*(b-a)/a**2
        eps = 5*w*(2+(score+abs(y)+2)*(b-a))/a**3
        errors.append(math.comb(order+1, j)*math.log(2*shell)**(order+1-j)*eps)
    cost = (math.exp(-math.log(shell)/2)*math.sqrt(b)
            /(length*math.factorial(order))*math.fsum(errors))
    return dict(N=order, periods=periods, eligibleCofactorPrimes=include_cofactor_primes,
                primeCount=len(ps), cofactors=rows,
                jointRetainedResponse=math.fsum(r['literalRetainedResponse'] for r in rows),
                jointSignedSmoothResponse=math.fsum(r['signedSmoothResponse'] for r in rows),
                jointArithmeticDiscrepancy=math.fsum(r['arithmeticDiscrepancy'] for r in rows),
                eventualCostWithoutSqrtE=cost, inProvedEventualRange=False)


if __name__ == '__main__':
    primes = primes_to(math.ceil(math.exp(12.)))
    budgets = []
    for n in [16384, 65536, 262144, 1048576]:
        row = all_order_error(n, 16)
        upper = 2*.55*(n+1)+8*2*math.pi/54
        row['twoCutoffErrorWithoutSqrtE_log10'] = (
            row['normalizedNewErrorFormula_log10']+.5*math.log10(upper))
        budgets.append(row)
    result = dict(scope=__doc__.strip(),
                  finiteBlocks=[block(primes, n, periods, eligible)
                                for n in [8, 16, 32, 64]
                                for periods in [1, 16] for eligible in [False, True]],
                  sourceBudgetScope='Full all-order binomial CAP, not the exact retained B(n,j). '
                  'Smooth saddle parameters, omitted sqrt(E), no cofactor-family aggregation. '
                  'Growing positive budgets are not carrier lower bounds or an asymptotic no-go.',
                  sourceBudgets=budgets)
    print(json.dumps(result, indent=2))

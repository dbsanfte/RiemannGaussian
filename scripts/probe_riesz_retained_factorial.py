#!/usr/bin/env python3
"""Optional diagnostics for the literal retained-factorial period bound.

Integer coefficient checks are exact finite regressions. The large-order
binomial calculations use floating point, not a certificate. No actual
primes are enumerated at exponential endpoints, no value for the proved
mean constant E is inferred, and no source-scale floor/ceiling is claimed.
This script is deliberately outside routine CI.
"""
import json
import math


def unpaid_orders(n):
    m = n + 1
    return [k for k in range(n + 2)
            if m < 8*k < 7*m and 32*k <= 15*n + 64
            and not (13*n//32 + 1 <= k <= (15*n + 64)//32)
            and 5*(m-k) < 4*n]


def retained_coefficients(n, logs):
    """All eligible cofactor primes; integer logs test the exact polynomial."""
    m, b = n + 1, sum(logs)
    orders = unpaid_orders(n)
    rows = []
    for j in range(m + 1):
        cap = math.comb(m, j)*b**(m-j)
        retained = cap if m-j not in orders else 0
        for q in logs:
            retained -= sum(math.comb(m, k)*math.comb(k, j)
                            *(b-q)**(k-j)*q**(m-k)
                            for k in orders if k >= j)
        assert 0 <= retained <= cap
        rows.append(retained)
    return {"N": n, "cofactorLogs": logs, "orders": orders,
            "nonnegativeAndBelowBinomialCap": True,
            "zeroOrderRetained": rows[0] > 0,
            "nonzeroOrders": sum(value > 0 for value in rows)}


def binomial_weights(m, x):
    """Scale at the mode; visit every order, allowing floating underflow."""
    mode = min(m, math.floor((m+1)*x))
    weights = [0.]*(m+1)
    weights[mode] = 1.
    for j in range(mode, m):
        weights[j+1] = weights[j]*(m-j)/(j+1)*x/(1-x)
    for j in range(mode, 0, -1):
        weights[j-1] = weights[j]*j/(m-j+1)*(1-x)/x
    total = math.fsum(weights)
    return [weight/total for weight in weights]


def order_cost(n, share=.55, radial=2., y=54.):
    m = n + 1
    h = 2*math.pi/abs(y)
    total = radial*m
    t, b = share*total, (1-share)*total
    a = t-h
    assert a >= 5000
    x = t/total
    weights = binomial_weights(m, x)
    base_tail = 2/(abs(y)*a)+4/a**2
    base = math.sqrt(a)*4/a**2 + math.sqrt(h)*base_tail
    slope = (math.sqrt(a)+math.sqrt(h))*h*base_tail
    scores = [abs(j/a-.5)+j*h/a**2 for j in range(m+1)]
    average = math.fsum(w*s for w, s in zip(weights, scores))
    variance_bound = math.sqrt(m*x*(1-x))/a+abs(m*x/a-.5)+m*h/a**2
    exact_energy_average = math.fsum(
        w*math.sqrt(a*(4/a**2+s*h*base_tail)**2
                    + h*((1+s*h)*base_tail)**2)
        for w, s in zip(weights, scores))
    summed_bound = base+slope*variance_bound
    maximum_bound = base+slope*max(scores)
    assert average <= variance_bound*(1+1e-10)
    assert exact_energy_average <= summed_bound*(1+1e-10)
    # Smooth saddle diagnostic only: b represents log(2M), L=-2N log(u).
    # Keep the (2u)^N growth visible instead of calling polynomial savings o(1).
    u, length = 10001/20000, -2*n*math.log(10001/20000)
    log_normalized = (m*math.log(u)-(b-math.log(2))/2-a/2
                      +m*math.log(total)-math.lgamma(n+1)-math.log(length)
                      +math.log(summed_bound))
    return {"N": n, "share": share, "radialSlope": radial,
            "primeLogEndpoint": a, "averageScore": average,
            "provedVarianceScoreBound": variance_bound,
            "exactOrderEnergyAverage": exact_energy_average,
            "provedSummedBudgetFactor": summed_bound,
            "maximumScoreBudgetFactor": maximum_bound,
            "summedOverMaximumBudget": summed_bound/maximum_bound,
            "sourceNormalizedSaddleBudgetWithoutSqrtE_log10":
                log_normalized/math.log(10)}


def main():
    integers = [retained_coefficients(n, logs)
                for n in [8, 16, 32, 64, 128]
                for logs in [[1, 2], [1, 2, 3, 5], [1]*12]]
    rows = [order_cost(n, radial=radial)
            for n in [16384, 65536, 262144]
            for radial in [1.95, 2., 2.03]]
    print(json.dumps({"scope": __doc__.strip(),
                      "integerRegressions": integers, "orderCosts": rows}, indent=2))


if __name__ == "__main__":
    main()

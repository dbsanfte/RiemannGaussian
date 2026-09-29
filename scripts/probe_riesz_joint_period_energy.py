#!/usr/bin/env python3
"""Optional joint-period energy diagnostics, not a certificate.

The actual-prime tests use small log endpoints, below the quantitative
prime theorem's a>=5000 threshold, and check only the general tail identity
and joint inequality. The large-order examples evaluate explicit numerical
budgets at their valid log endpoints; they do not enumerate those primes,
estimate the unevaluated squarefree-mean constant, or prove source decay.
"""
import json
import math

import numpy as np

from probe_riesz_prime_tail_energy import primes_to
from probe_riesz_retained_factorial import binomial_weights


def tail_energy(primes, coefficients):
    if not len(primes):
        return 0., 0.
    tails = np.cumsum(coefficients[::-1])[::-1]
    widths = np.diff(np.r_[0., np.log(primes)])
    return float(widths @ tails**2), float(np.max(np.abs(tails)))


def actual_prime_probe(primes, count, phase):
    a, y, j = 10., 54., 5
    h = 2*math.pi/y
    moment, bound, energies, all_p, all_c = [], [], [], [], []
    for i in range(count):
        lo, hi = a+i*h, a+(i+1)*h
        ps = primes[(primes > math.floor(math.exp(lo)))
                    & (primes <= math.floor(math.exp(hi)))]
        logs = np.log(ps)
        cs = np.exp(-logs/2)*logs**j*np.cos(y*(logs+phase))/ps
        e, b = tail_energy(ps, cs)
        moment.append(float(cs.sum()))
        bound.append(b)
        energies.append(e)
        all_p.append(ps)
        all_c.append(cs)
    joint, _ = tail_energy(np.concatenate(all_p), np.concatenate(all_c))
    separate = math.fsum(math.sqrt(e) for e in energies)**2
    proved_bound = (a*math.fsum(moment)**2
                    + count*h*(math.fsum(abs(m) for m in moment)+max(bound))**2)
    assert joint <= proved_bound*(1+1e-10)+1e-12
    return {"periodCount": count, "phase": phase,
            "primeCount": sum(len(p) for p in all_p),
            "actualJointEnergy": joint, "separateNormSquared": separate,
            "jointOverSeparateSquared": joint/separate,
            "jointTailBound": proved_bound,
            "jointOverTailBound": joint/proved_bound}


def numerical_budget(n, count):
    j, y = round(.55*(n+1)), 54.
    h = 2*math.pi/y
    a = 2*j-count*h/2
    assert a >= 5000
    moments, tails, individual = [], [], []
    for i in range(count):
        ai = a+i*h
        # Normalize by the global factorial peak to avoid overflow.
        w = math.exp(-ai/2+j*math.log(ai+h)-(-j+j*math.log(2*j)))
        score = abs(j/ai-.5)+j*h/ai**2
        base = 2/(y*ai)+4/ai**2
        moment = 4*w/ai**2+w*score*h*base
        tail = (w+w*score*h)*base
        moments.append(moment)
        tails.append(tail)
        individual.append(ai*moment**2+h*tail**2)
    separate = math.fsum(math.sqrt(e) for e in individual)
    joint = math.sqrt(a*math.fsum(moments)**2
                      + count*h*(math.fsum(moments)+max(tails))**2)
    return {"N": n, "factorialOrder": j, "periodCount": count,
            "lowestPrimeLog": a, "jointOverSeparate": joint/separate,
            "jointCostOverFactorialPeak": joint,
            "separateCostOverFactorialPeak": separate}


def all_order_budget(n, count):
    """Evaluate the literal bound's full binomial sum at a smooth saddle.

    Every order is present in the arrays; tiny binomial probabilities may
    underflow in this floating diagnostic. Here b=log(2M) is treated as a
    real parameter and L=-2N log(u), so this is not an integer-cutoff bound.
    The unknown sqrt(E) and aggregation over other cofactor shells are omitted.
    """
    m, y, u = n+1, 54., 10001/20000
    h, share = 2*math.pi/y, .55
    center, b = share*2*m, (1-share)*2*m
    lo = center-count*h/2
    assert lo >= 5000
    orders = np.arange(m+1, dtype=float)
    probabilities = np.asarray(binomial_weights(m, share))
    moments, tails, separate = (np.zeros(m+1) for _ in range(3))
    for i in range(count):
        ai = lo+i*h
        # Divide each j-th amplitude by exp(-center/2)*center^j.
        weight = np.exp(-(ai-center)/2
                        + orders*np.log1p((ai+h-center)/center))
        score = np.abs(orders/ai-.5)+orders*h/ai**2
        base = 2/(y*ai)+4/ai**2
        moment = weight*(4/ai**2+score*h*base)
        tail = weight*(1+score*h)*base
        moments += moment
        tails = np.maximum(tails, tail)
        separate += np.sqrt(ai*moment**2+h*tail**2)
    joint = np.sqrt(lo*moments**2+count*h*(moments+tails)**2)
    joint_average = float(probabilities @ joint)
    separate_average = float(probabilities @ separate)
    length = -2*n*math.log(u)
    log_source_prefactor = (m*math.log(u)-(b-math.log(2))/2-center/2
                           + m*math.log(2*m)-math.lgamma(n+1)
                           - math.log(length))
    return {"N": n, "periodCount": count, "includedOrders": m+1,
            "lowestPrimeLog": lo, "largestShare": share,
            "jointOverSeparateAllOrders": joint_average/separate_average,
            "jointAllOrderBudgetWithoutSqrtE_log10":
                (log_source_prefactor+math.log(joint_average))/math.log(10),
            "separateAllOrderBudgetWithoutSqrtE_log10":
                (log_source_prefactor+math.log(separate_average))/math.log(10)}


def main():
    primes = primes_to(math.ceil(math.exp(12.)))
    actual = [actual_prime_probe(primes, count, phase)
              for count in [1, 4, 16] for phase in [0., .37]]
    numerical = [numerical_budget(n, count)
                 for n in [16384, 65536, 262144]
                 for count in [4, 16, 64, 256, 1024]]
    all_orders = [all_order_budget(n, count)
                  for n in [16384, 65536, 262144] for count in [16, 256]]
    all_orders.append(all_order_budget(1048576, 16))
    print(json.dumps({"scope": __doc__.strip(), "actualPrimes": actual,
                      "numericalBudgets": numerical,
                      "allOrderSmoothSaddleScope": all_order_budget.__doc__.strip(),
                      "allOrderSmoothSaddleBudgets": all_orders}, indent=2))


if __name__ == "__main__":
    main()

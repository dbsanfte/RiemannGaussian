#!/usr/bin/env python3
"""Optional diagnostics for the joined prime-discrepancy inequality.

The new theorem has a proved but unevaluated starting point. Evaluating its
formula at a finite log endpoint does not certify that the endpoint is in
that eventual range. The old/new budgets below both concern arithmetic
discrepancy from the SAME signed smooth integral, not the whole prime moment.
No cofactor-mask transfer, source-scale smallness or zero exclusion is inferred.
This experiment is not part of CI.
"""
import json
import math

import numpy as np

from probe_riesz_prime_tail_energy import primes_to
from probe_riesz_retained_factorial import binomial_weights


def actual_probe(primes, count, phase):
    a, y, j = 10., 54., 5
    h, b = 2*math.pi/y, 10.+count*2*math.pi/y
    ps = primes[(primes > math.floor(math.exp(a)))
                & (primes <= math.floor(math.exp(b)))]
    logs = np.log(ps)
    actual = float(np.sum(np.exp(-logs/2)*logs**j
                          * np.cos(y*(logs+phase))/ps))
    nodes, weights = np.polynomial.legendre.leggauss(32)
    smooth_parts = []
    prime_parts = []
    for i in range(count):
        ai = a+i*h
        ts = ai+(nodes+1)*h/2
        smooth_parts.append(float(h/2*np.dot(weights,
            np.exp(-ts/2)*ts**(j-1)*np.cos(y*(ts+phase)))))
        mask = (logs > ai) & (logs <= ai+h)
        prime_parts.append(float(np.sum(np.exp(-logs[mask]/2)*logs[mask]**j
            * np.cos(y*(logs[mask]+phase))/ps[mask])))
    smooth = math.fsum(smooth_parts)
    errors = [p-s for p, s in zip(prime_parts, smooth_parts)]
    assert math.isclose(actual, math.fsum(prime_parts), rel_tol=1e-10, abs_tol=1e-10)
    w = min(math.exp(-a/2)*b**j, math.exp(-j)*(2*j)**j)
    score = abs(j/a-.5)+j*(b-a)/a**2
    budget = 5*w*(2+(score+abs(y)+2)*(b-a))/a**3
    return {"periodCount": count, "phase": phase, "primeCount": len(ps),
            "signedPrimeMoment": actual, "signedSmoothMoment": smooth,
            "actualSignedDiscrepancy": actual-smooth,
            "sumAbsolutePeriodDiscrepancies": math.fsum(abs(e) for e in errors),
            "eventualBudgetFormula": budget,
            "inProvedEventualRange": "Not established"}


def all_order_error(n, count):
    m, y, u, share = n+1, 54., 10001/20000, .55
    h, center, cofactor_log = 2*math.pi/y, 2*share*m, 2*(1-share)*m
    lo, hi = center-count*h/2, center+count*h/2
    orders = np.arange(m+1, dtype=float)
    probabilities = np.asarray(binomial_weights(m, share))
    log_peak = np.zeros(m+1)
    log_peak[1:] = -orders[1:]+orders[1:]*np.log(2*orders[1:])
    log_peak -= -center/2+orders*math.log(center)
    log_endpoint = -(lo-center)/2+orders*math.log(hi/center)
    w = np.exp(np.minimum(log_endpoint, log_peak))
    score = np.abs(orders/lo-.5)+orders*(hi-lo)/lo**2
    joined = 5*w*(2+(score+y+2)*(hi-lo))/lo**3
    old = np.zeros(m+1)
    for i in range(count):
        ai = lo+i*h
        wi = np.exp(-(ai-center)/2+orders*np.log1p((ai+h-center)/center))
        si = np.abs(orders/ai-.5)+orders*h/ai**2
        old += .41*wi*(2+(si+y+2)*h)/ai**2
    joined_average = float(probabilities @ joined)
    old_average = float(probabilities @ old)
    length = -2*n*math.log(u)
    # Same smooth saddle prefactor as the preceding carrier-budget probe.
    log_prefactor = (m*math.log(u)-(cofactor_log-math.log(2))/2-center/2
                    +m*math.log(2*m)-math.lgamma(n+1)-math.log(length))
    return {"N": n, "periodCount": count, "includedOrders": m+1,
            "lowestPrimeLog": lo,
            "newOverOldArithmeticError": joined_average/old_average,
            "normalizedNewErrorFormula_log10":
                (log_prefactor+math.log(joined_average))/math.log(10),
            "normalizedOldErrorFormula_log10":
                (log_prefactor+math.log(old_average))/math.log(10)}


def main():
    primes = primes_to(math.ceil(math.exp(12.)))
    result = {"scope": __doc__.strip(),
              "actualPrimes": [actual_probe(primes, count, phase)
                               for count in [1, 4, 16] for phase in [0., .37]],
              "allOrderScope": "Every order is included, with floating underflow possible. "
              "Smooth L=-2N log u and real log(2M) parameters; the unevaluated mean "
              "constant and aggregation over cofactor shells are omitted. The signed "
              "smooth term is not part of this error budget.",
              "allOrderErrors": [all_order_error(n, count)
                                  for n in [16384, 65536, 262144]
                                  for count in [16, 256]]}
    result["allOrderErrors"].append(all_order_error(1048576, 16))
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Optional actual-prime diagnostic for the signed tail-energy inequality.

Floating-point probes are below the theorem's a>=5000 logarithmic threshold.
They test the exact identities/energy mechanism, not that theorem's numerical
constant, the unevaluated squarefree-mean constant, or any RH conclusion.
No prime-density approximation or CI/exhaustive verification is used.
"""
import json
import math

import numpy as np

from probe_riesz_sieve_mean import arithmetic


def primes_to(upper):
    prime = np.ones(upper + 1, dtype=bool)
    prime[:2] = False
    for p in range(2, math.isqrt(upper) + 1):
        if prime[p]:
            prime[p*p::p] = False
    return np.flatnonzero(prime)


def combined_profile(logs, weights, length, indices):
    hinge = np.maximum(0, length - np.log(indices))
    mass = np.r_[0, np.cumsum(weights)]
    moment = np.r_[0, np.cumsum(weights * logs)]
    cut = np.searchsorted(logs, hinge, side="right")
    return moment[cut] + hinge * (mass[-1] - mass[cut])


def probe(a, y, phase, primes):
    b = a + 2 * math.pi / abs(y)
    ps = primes[(primes > math.floor(math.exp(a)))
                & (primes <= math.floor(math.exp(b)))]
    logs = np.log(ps)
    cs = np.cos(y * (logs + phase)) / ps
    tails = np.cumsum(cs[::-1])[::-1]
    unsigned = np.cumsum(np.abs(cs)[::-1])[::-1]
    widths = np.diff(np.r_[0, logs])
    energy = float(widths @ tails**2)
    unsigned_energy = float(widths @ unsigned**2)
    full_moment = float(cs.sum())
    transition = energy - a * full_moment**2
    clipped = float(np.max(np.abs(tails), initial=0))
    rows = []
    for length in [6., 10., 14.]:
        end = math.floor(math.exp(length))
        indices = np.arange(1, end+2)
        f = combined_profile(logs, cs, length, indices)
        discrete = float(np.arange(1, end+1) @ np.diff(f)**2)
        assert discrete <= energy * (1 + 1e-8) + 1e-15
        rows.append({"length": length, "cutoff": end,
                     "discreteEnergy": discrete,
                     "discreteOverIntegrated": discrete / energy})
    # Direct signed cofactor sums with their actual product phases.
    population, length = 4096, 10.
    mu, _ = arithmetic(population)
    indices = np.arange(1, population+1)
    fc = combined_profile(logs, np.cos(y*logs)/ps, length, indices)
    fs = combined_profile(logs, -np.sin(y*logs)/ps, length, indices)
    rc, rs = np.zeros(population+1), np.zeros(population+1)
    for d in range(1, population+1):
        if mu[d]:
            rc[d::d] += int(mu[d])*fc[d-1]
            rs[d::d] += int(mu[d])*fs[d-1]
    ns = np.flatnonzero(mu)
    ns = ns[ns > 1]
    responses = np.cos(y*np.log(ns))*rc[ns] + np.sin(y*np.log(ns))*rs[ns]
    regression = []
    for n, response in zip(ns[:32], responses[:32]):
        divisors = np.array([d for d in range(1, n+1) if n % d == 0])
        hinge = np.maximum(0, length-np.log(divisors))
        riesz = np.minimum(logs[:, None], hinge[None, :]) @ mu[divisors]
        direct = float((np.cos(y*(logs+math.log(n)))/ps) @ riesz)
        regression.append(abs(direct-response))
    assert max(regression, default=0) < 1e-11
    return {"a": a, "b": b, "height": y, "phase": phase,
            "primeCount": len(ps), "fullSignedMoment": full_moment,
            "transitionEnergy": transition, "integratedTailEnergy": energy,
            "signedOverUnsignedTailEnergy": energy / unsigned_energy,
            "exactTailBound": a*full_moment**2 + (b-a)*clipped**2,
            "lengthChecks": rows,
            "squarefreePopulation": len(ns),
            "correlatedMeanSquare": float(responses @ responses),
            "cofactorRotationRegression": max(regression, default=0),
            "regressionAtoms": len(regression)}


def main():
    primes = primes_to(math.ceil(math.exp(14.2)))
    rows = [probe(a, 54., .37, primes) for a in [8., 10., 12., 14.]]
    print(json.dumps({"scope": __doc__.strip(), "rows": rows}, indent=2))


if __name__ == "__main__":
    main()

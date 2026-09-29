#!/usr/bin/env python3
"""Optional exact-moment energy diagnostic; never a CI or RH certificate.

Retains actual primes, squarefree cofactors, the full allocation polynomial,
all factorial orders, both cutoff hinges, moving length, largest-prime owner,
nondominant .65 mask and 1.95N..2.03N core. The finite population is truncated.
Costs omit the UNEVALUATED sqrt(E). Increasing finite costs do not prove an
asymptotic obstruction; decreases do not prove an eventual bound.
"""
import argparse
import json
import math

import numpy as np

from probe_riesz_sieve_mean import arithmetic
from probe_riesz_retained_discrepancy import coefficients


def probe(order, population, physical, height, radius):
    upper = (math.floor(radius**(-order)/(order+1))+2)**2
    length = math.log(upper)
    mu, phi = arithmetic(max(population, upper))
    integers = np.arange(len(phi))
    primes = np.flatnonzero((phi == integers-1) & (integers >= 2))
    ps = primes[(primes > order**2) & (primes < upper)]
    lp = np.log(ps)
    factors = [[] for _ in range(population+1)]
    for p in primes[primes <= population]:
        for n in range(int(p), population+1, int(p)):
            factors[n].append(int(p))
    totals, rows, labels, regressions = np.zeros(3), [], 0, []
    for b in range(population.bit_length()):
        lower = 2**b
        if lower >= population:
            break
        end = min(2*lower, population)
        P = ps[(lp+math.log(2*lower) > 1.95*order)
               & (lp+math.log(lower) <= 2.03*order)]
        if not len(P):
            continue
        logp, S, weights = np.log(P), [], []
        for n in range(max(2, lower+1), end+1):
            fs = factors[n]
            if mu[n] == 0 or len(fs) < 2 or (physical and min(fs) <= order**2):
                continue
            total = logp+math.log(n)
            selected = ((total > 1.95*order) & (total <= 2.03*order)
                        & (logp < .65*total) & (P > max(fs)))
            inds = np.flatnonzero(selected)
            if not len(inds):
                continue
            assert np.all(np.diff(inds) == 1)
            S.append(n)
            labels += len(inds)
            B = coefficients(order, [math.log(p) for p in fs],
                             [math.log(p) for p in fs if order**2 < p < upper])
            weights.append(math.exp(-math.log(n)/2)/n*B)
            if len(regressions) < 256:
                divisors = [1]
                for p in fs:
                    divisors += [p*d for d in divisors]
                ds = np.asarray(divisors)
                signs, logs = mu[ds], np.log(ds)
                assert int(signs.sum()) == 0
                moment = float(signs@logs)
                assert abs(moment) < 1e-11
                # Test the actual signed prime profile before and after an
                # arbitrary complex null correction, without a phase norm.
                t = logp[inds]
                c = np.exp(-t/2)*t**(order//2)/P[inds]*np.exp(1j*height*t)
                c /= max(1., float(np.abs(c).max()))
                profile = c@np.minimum(t[:, None], np.maximum(0., length-logs)[None, :])
                endpoint = np.sum(c*np.minimum(t, max(0., length-math.log(end))))
                centered = profile-endpoint+(.07+.13j)*(logs-math.log(end))
                diff = abs(signs@profile-signs@centered)
                scale = max(1., float(np.abs(profile).sum()))
                regressions.append(float(diff/scale))
        if not S:
            continue
        weight_energy = np.sum(np.asarray(weights)**2, axis=0)
        depth = math.ceil(math.log2(len(P)))
        k = np.arange(1, upper+1)
        hinge = np.maximum(0., length-np.log(np.arange(1, upper+2)))
        profile = np.minimum(logp[:, None], hinge[None, :])
        delta = profile[:, :-1]-profile[:, 1:]
        stop = min(upper, end-1)
        kv = np.arange(1, end)
        g = np.log1p(1/kv)
        norm = float(np.sum(kv*g*g))
        energy = np.zeros((3, order+2))
        for j in range(order+2):
            coef = np.exp(-logp/2)*logp**j/P*np.exp(1j*height*logp)
            cells = np.zeros((2**depth, upper), dtype=complex)
            cells[:len(P)] = coef[:, None]*delta
            while True:
                full = np.sum(np.abs(cells)**2*k, axis=1)
                truncated = np.sum(np.abs(cells[:, :stop])**2*k[:stop], axis=1)
                cross = cells[:, :stop]@(k[:stop]*g[:stop])
                centered = truncated-np.abs(cross)**2/norm
                assert np.min(centered) >= -1e-10*max(1., float(np.max(truncated)))
                energy[:, j] += np.array([sum(full), sum(truncated), sum(np.maximum(centered, 0.))])
                if len(cells) == 1:
                    break
                cells = cells[::2]+cells[1::2]
        costs = (2*math.sqrt(end*(depth+1))*np.sqrt(weight_energy*energy).sum(axis=1)
                 /(length*math.factorial(order))*radius**(order+1))
        totals += costs
        rows.append(dict(lower=lower, upper=end, cofactors=len(S), binaryDepth=depth,
                         sourceCostsWithoutSqrtE=costs.tolist()))
    assert max(regressions, default=0.) < 1e-10
    assert totals[2] <= totals[1]+1e-12 <= totals[0]+2e-12
    return dict(order=order, population=population, allCofactorPrimesAboveNSquared=physical,
                radius=radius, height=height, length=length, physicalUpper=upper,
                selectedLabels=labels, originalMovingCost=float(totals[0]),
                populationTruncatedCost=float(totals[1]), centeredCost=float(totals[2]),
                centeredOverPrevious=float(totals[2]/totals[0]),
                sourceCostsOmitSqrtE=True, constantEvaluated=False, wholeCarrierCovered=False,
                regressionRows=len(regressions), maximumNullCorrectionRelativeError=max(regressions, default=0.),
                shells=rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--height', type=float, default=54.)
    parser.add_argument('--radius', type=float, default=10001/20000)
    args = parser.parse_args()
    rows = [probe(N, X, physical, args.height, args.radius)
            for N, X in [(6, 4096), (8, 65536), (10, 1048576)] for physical in [False, True]]
    print(json.dumps(dict(scope=__doc__.strip(), rows=rows), indent=2))


if __name__ == '__main__':
    main()

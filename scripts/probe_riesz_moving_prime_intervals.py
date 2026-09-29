#!/usr/bin/env python3
"""Optional moving-interval diagnostic; never a CI or RH certificate.

Actual primes, squarefree cofactors, unique largest-prime ownership, the
1.95N..2.03N window, nondominant .65 mask, moving physical length, both Riesz
cutoffs, every factorial order and the exact original allocation are kept.
The population is finite and truncated. The reported source cost omits the
UNEVALUATED common sqrt(E); small-N evidence is not an eventual bound.
No smooth prime density, phase freezing or completed prime row is used.
"""
import argparse
import json
import math

import numpy as np

from probe_riesz_sieve_mean import arithmetic
from probe_riesz_retained_discrepancy import coefficients
from probe_riesz_retained_factorial import unpaid_orders


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
    costs, shell_rows, direct, expanded, regressions = [], [], [], [], []
    labels, orders = set(), unpaid_orders(order)
    for b in range(population.bit_length()):
        lower = 2**b
        if lower >= population:
            break
        end = min(2*lower, population)
        P = ps[(lp+math.log(2*lower) > 1.95*order)
               & (lp+math.log(lower) <= 2.03*order)]
        if not len(P):
            continue
        logp, S, weights, row_endpoints = np.log(P), [], [], []
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
            assert np.all(np.diff(inds) == 1), 'A selected row has an unpaid internal hole'
            for p in P[inds]:
                label = int(p)*n
                assert label not in labels, 'Duplicate ownership'
                labels.add(label)
            S.append(n)
            row_endpoints.append((int(inds[0]), int(inds[-1])+1))
            logs = [math.log(p) for p in fs]
            eligible = [math.log(p) for p in fs if order**2 < p < upper]
            B = coefficients(order, logs, eligible)
            weights.append(math.exp(-math.log(n)/2)/n*B)
            # Compare the original allocation to the exact cofactor polynomial.
            t, selected_logs, selected_primes = total[inds], logp[inds], P[inds]
            theta = np.zeros_like(t)
            for marked in [selected_logs, *eligible]:
                theta += sum(math.comb(order+1, k)*((t-marked)/t)**k
                             *(marked/t)**(order+1-k) for k in orders)
            raw = (1-theta)*t**(order+1)
            poly = np.polynomial.polynomial.polyval(selected_logs, B)
            regressions.append(float(np.max(np.abs(raw-poly)/np.maximum(1., np.abs(raw)))))
            divisors = [1]
            for p in fs:
                divisors += [p*d for d in divisors]
            response = sum(int(mu[d])*np.minimum(selected_logs,
                           max(0., length-math.log(d))) for d in divisors)
            atom = (-np.exp(-t/2)*np.cos(height*t)*response
                    /(length*math.factorial(order)*n*selected_primes))
            direct.append(float(atom@raw))
            expanded.append(float(atom@poly))
        if not S:
            continue
        weight_energy = np.sum(np.asarray(weights)**2, axis=0)
        depth = math.ceil(math.log2(len(P)))
        indices = np.arange(1, upper+2)
        hinge = np.maximum(0., length-np.log(indices))
        profiles = np.minimum(logp[:, None], hinge[None, :])
        delta = profiles[:, :-1]-profiles[:, 1:]
        energy = np.zeros(order+2)
        for j in range(order+2):
            coef = np.exp(-logp/2)*logp**j/P*np.exp(1j*height*logp)
            cells = np.zeros((2**depth, upper), dtype=complex)
            cells[:len(P)] = coef[:, None]*delta
            while True:
                # Both phase components, with cross terms inside every block.
                energy[j] += float(np.sum(np.abs(cells)**2*np.arange(1, upper+1)))
                if len(cells) == 1:
                    break
                cells = cells[::2]+cells[1::2]
        cost = (2*math.sqrt(end*(depth+1))*float(np.sqrt(weight_energy*energy).sum())
                /(length*math.factorial(order)))
        costs.append(cost)
        shell_rows.append(dict(lower=lower, upper=end, cofactors=len(S),
                               primeCells=len(P), binaryDepth=depth,
                               distinctMovingIntervals=len(set(row_endpoints)),
                               sourceCostWithoutSqrtE=radius**(order+1)*cost))
    regression_error = max(regressions, default=0.)
    assert regression_error < 2e-10
    direct_total, expanded_total = math.fsum(direct), math.fsum(expanded)
    assert abs(direct_total-expanded_total) < 1e-10*max(1., abs(direct_total))
    return dict(order=order, population=population, allCofactorPrimesAboveNSquared=physical,
                radius=radius, height=height, length=length, physicalUpper=upper,
                atoms=len(labels), shells=shell_rows, factorialOrders=list(range(order+2)),
                maximumRelativeAllocationError=regression_error,
                actualJoint=direct_total, expandedJoint=expanded_total,
                sourceNormalizedJoint=radius**(order+1)*direct_total,
                sourceCostWithoutSqrtE=radius**(order+1)*math.fsum(costs),
                wholeCarrierCovered=False, constantEvaluated=False, numericalCertificate=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--height', type=float, default=54.)
    parser.add_argument('--radius', type=float, default=10001/20000)
    args = parser.parse_args()
    print(json.dumps(dict(scope=__doc__.strip(), rows=[
        probe(N, X, physical, args.height, args.radius)
        for N, X in [(6, 4096), (8, 65536)] for physical in [False, True]]), indent=2))


if __name__ == '__main__':
    main()

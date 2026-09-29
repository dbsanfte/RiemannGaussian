#!/usr/bin/env python3
"""Optional joint-coordinate diagnostic, never a CI or numerical certificate.

Uses actual primes/cofactors, all factorial orders, original allocation,
both Riesz hinges and the full product phase. Finite populations are truncated;
the reported costs omit the UNEVALUATED sqrt(E). A complete orthogonal basis
is used, including every near-zero energy direction. No asymptotic claim.
"""
import argparse
import json
import math

import numpy as np

from probe_riesz_retained_discrepancy import coefficients
from probe_riesz_retained_factorial import unpaid_orders
from probe_riesz_sieve_mean import arithmetic


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
    totals, shells, labels, regressions = np.zeros(2), [], 0, []
    orders = unpaid_orders(order)
    for b in range(population.bit_length()):
        lower = 2**b
        if lower >= population:
            break
        end = min(2*lower, population)
        P = ps[(lp+math.log(2*lower) > 1.95*order)
               & (lp+math.log(lower) <= 2.03*order)]
        if not len(P):
            continue
        t, rows = np.log(P), []
        powers = t[None, :]**np.arange(order+2)[:, None]
        for n in range(max(2, lower+1), end+1):
            fs = factors[n]
            if mu[n] == 0 or len(fs) < 2 or (physical and min(fs) <= order**2):
                continue
            logs, v = [math.log(p) for p in fs], math.log(n)
            total = t+v
            selected = ((total > 1.95*order) & (total <= 2.03*order)
                        & (t < .65*total) & (P > max(fs)))
            if not selected.any():
                continue
            eligible = [math.log(p) for p in fs if order**2 < p < upper]
            poly = coefficients(order, logs, eligible)@powers
            weight = (-poly*np.exp(-total/2)/(n*P)*np.cos(height*total)
                      *radius**(order+1)/(length*math.factorial(order)))
            rows.append(weight*selected)
            labels += int(selected.sum())
            if len(regressions) < 256:
                inds = np.flatnonzero(selected)
                theta = np.zeros_like(t)
                for q in [t, *eligible]:
                    theta += sum(math.comb(order+1, k)
                                 *((total-q)/total)**k*(q/total)**(order+1-k)
                                 for k in orders)
                direct_poly = (1-theta)*total**(order+1)
                error = float(np.max(np.abs(poly[inds]-direct_poly[inds])
                                     /np.maximum(np.abs(poly[inds]), 1e-100)))
                ds = [1]
                for p in fs:
                    ds += [p*d for d in ds]
                ds = np.asarray(ds)
                # The actual original residual coefficient uses the divisor
                # sum of pn; splitting its divisors gives this same hinge.
                hinge = np.minimum(t[inds, None], np.maximum(0., length-np.log(ds))[None, :])
                response = hinge@mu[ds]
                atom = weight[inds]*response
                direct = (-(1-theta[inds])*total[inds]*response/length
                          *total[inds]**order/math.factorial(order)
                          *np.exp(-1.5*total[inds])*np.cos(height*total[inds])
                          *radius**(order+1))
                atom_error = float(np.max(np.abs(atom-direct))
                                   /max(1e-100, float(np.max(np.abs(atom)))))
                regressions.append(max(error, atom_error))
        if not rows:
            continue
        A = np.asarray(rows)
        stop = min(upper, end-1)
        k = np.arange(1, stop+1, dtype=float)
        hinge = np.maximum(0., length-np.log(np.arange(1, stop+2, dtype=float)))
        profile = np.minimum(t[:, None], hinge[None, :])
        D = (profile[:, :-1]-profile[:, 1:])*np.sqrt(k)
        logdir = np.sqrt(k)*np.log1p(1/k)
        cross = D@logdir
        kv = np.arange(1, end, dtype=float)
        lognorm = float(np.sum(kv*np.log1p(1/kv)**2))
        tailnorm = float(np.sum(kv[stop:]*np.log1p(1/kv[stop:])**2))
        gram = D@D.T-np.outer(cross, cross)/lognorm
        vals, Q = np.linalg.eigh((gram+gram.T)/2)
        # DO NOT discard small eigenvalues or their coordinate columns.
        assert vals.min() >= -1e-9*max(1., float(vals.max()))
        orthogonality = float(np.max(np.abs(Q.T@Q-np.eye(len(P)))))
        assert orthogonality < 1e-10
        rotated = Q.T@D
        slope = (Q.T@cross)/lognorm
        centered = rotated-slope[:, None]*logdir[None, :]
        energies = np.sum(centered**2, axis=1)+slope**2*tailnorm
        weight_energies = np.zeros(len(P))
        for start in range(0, len(A), 2048):
            weight_energies += np.sum((A[start:start+2048]@Q)**2, axis=0)
        joint = float(np.sqrt(weight_energies*energies).sum())*math.sqrt(end)
        slope0 = cross/lognorm
        centered0 = D-slope0[:, None]*logdir[None, :]
        energy0 = np.sum(centered0**2, axis=1)+slope0**2*tailnorm
        separate = float(np.sqrt(np.sum(A*A, axis=0)*energy0).sum())*math.sqrt(end)
        totals += [joint, separate]
        shells.append(dict(lower=lower, upper=end, cofactors=len(A), primes=len(P),
                           coordinateColumns=Q.shape[1], allCoordinateColumnsRetained=True,
                           maximumOrthogonalityError=orthogonality,
                           smallestComputedGramEigenvalue=float(vals.min()),
                           jointCostWithoutSqrtE=joint, separatePrimeCostWithoutSqrtE=separate))
    assert max(regressions, default=0.) < 2e-8
    return dict(order=order, population=population, radius=radius, height=height,
                allCofactorPrimesAboveNSquared=physical, length=length, physicalUpper=upper,
                selectedLabels=labels, jointCost=float(totals[0]), separatePrimeCost=float(totals[1]),
                sourceCostsOmitSqrtE=True, constantEvaluated=False, wholeCarrierCovered=False,
                allCoordinateColumnsRetained=True, regressionRows=len(regressions),
                maximumAtomRelativeError=max(regressions, default=0.), shells=shells)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--height', type=float, default=54.)
    parser.add_argument('--radius', type=float, default=10001/20000)
    parser.add_argument('--max-order', type=int, default=10, choices=[6, 8, 10])
    parser.add_argument('--expand-population', action='store_true',
                        help='Use exp(2.03N)/(N^2+1) as the cofactor cap; still not a full-core certificate.')
    args = parser.parse_args()
    rows = []
    for order, population in [(6, 4096), (8, 65536), (10, 1048576)]:
        if order > args.max_order:
            continue
        if args.expand_population:
            population = math.floor(math.exp(2.03*order)/(order**2+1))
        for physical in [False, True]:
            rows.append(probe(order, population, physical, args.height, args.radius))
    print(json.dumps(dict(scope=__doc__.strip(), expandedPopulation=args.expand_population,
                          rows=rows), indent=2))


if __name__ == '__main__':
    main()

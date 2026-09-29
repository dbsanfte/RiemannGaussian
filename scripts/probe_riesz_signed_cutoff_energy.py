#!/usr/bin/env python3
"""Optional signed cutoff-energy diagnostic, never a CI or RH certificate.

Uses actual finite primes, integer squarefreeness and divisor signs, floating
logs, the exact factorial allocation formula, moving Riesz length, original
phase, owner and nondominant masks, and the 1.95N..2.03N core. Reports both
all squarefree composite cofactors and the subpopulation with every prime
above N^2. Constants in Lean remain unevaluated. Small finite orders cannot
certify an eventual source bound.
"""
import argparse
import json
import math

import numpy as np

from probe_riesz_sieve_mean import arithmetic


def probe(order, population, height, radius):
    upper = (math.floor(radius**(-order) / (order + 1)) + 2)**2
    length = math.log(upper)
    mu, phi = arithmetic(max(upper, population))
    prime = np.flatnonzero((phi == np.arange(len(phi)) - 1)
                           & (np.arange(len(phi)) >= 2))
    primes = prime[(prime > order**2) & (prime < upper)]
    prime_logs = np.log(primes)
    factors = [[] for _ in range(population + 1)]
    for p in prime[prime <= population]:
        for a in range(int(p), population + 1, int(p)):
            factors[a].append(int(p))
    unpaid = [k for k in range(order + 2)
              if order + 1 < 8*k < 7*(order + 1)
              and 32*k <= 15*order + 64
              and not 13*order//32 + 1 <= k <= (15*order + 64)//32
              and 5*(order + 1 - k) < 4*order]
    indices = np.arange(1, upper + 2)
    hinge = np.maximum(0, length - np.log(indices))
    energy_weight = np.arange(1, upper + 1)
    previous = np.zeros(upper)
    variation = total = physical_total = absolute = 0.0
    profile_energy = unsigned_energy = 0.0
    atom_count = physical_count = crossing_count = 0
    regression = []

    for a in range(1, population + 2):
        if a <= population:
            logs = prime_logs + math.log(a)
            selected = ((logs > 1.95*order) & (logs <= 2.03*order)
                        & (prime_logs < .65*logs)
                        & (primes > (factors[a][-1] if factors[a] else 1)))
            ps, lp, ts = primes[selected], prime_logs[selected], logs[selected]
        else:
            ps, lp, ts = np.array([]), np.array([]), np.array([])
        if len(ps):
            assigned = np.zeros(len(ps))
            if mu[a] != 0 and len(factors[a]) >= 2:
                for marked_log, eligible in [(lp, True)] + [
                        (math.log(q), order**2 < q < upper) for q in factors[a]]:
                    if not eligible:
                        continue
                    share = marked_log / ts
                    for k in unpaid:
                        assigned += (math.comb(order + 1, k)
                                     * (1-share)**k * share**(order + 1-k))
            weight = (-(1-assigned) / (length*a) * np.exp(-ts/2)
                      * ts**(order+1) / math.factorial(order) / ps
                      * np.cos(height*ts))

            def combined(ws):
                # Sum the original signed primes before taking differences.
                mass = np.r_[0, np.cumsum(ws)]
                moment = np.r_[0, np.cumsum(ws*lp)]
                cut = np.searchsorted(lp, hinge, side="right")
                return moment[cut] + hinge*(mass[-1]-mass[cut])

            f = combined(weight)
            b = f[:-1]-f[1:]
            b_abs = np.diff(combined(np.abs(weight)))
            profile_energy += float(energy_weight @ b**2)
            unsigned_energy += float(energy_weight @ b_abs**2)
            if mu[a] != 0 and len(factors[a]) >= 2:
                divisors = [1]
                for q in factors[a]:
                    divisors += [q*d for d in divisors]
                ds = np.array([d for d in divisors if d <= upper])
                contribution = float(mu[ds] @ f[ds-1])
                total += contribution
                atom_count += len(ps)
                physical = factors[a][0] > order**2
                if physical:
                    physical_total += contribution
                    physical_count += len(ps)
                # Direct atom evaluation is a separate small regression sample.
                if len(regression) < 256:
                    for j in range(min(len(ps), 256-len(regression))):
                        all_divisors = divisors + [int(ps[j])*d for d in divisors]
                        signs = [int(mu[d]) for d in divisors]
                        signs += [-v for v in signs]
                        riesz = sum(sign*max(0, length-math.log(d))
                                    for sign, d in zip(signs, all_divisors))
                        direct = (-ts[j]/length*riesz*(1-assigned[j])
                                  * math.exp(-1.5*ts[j])*ts[j]**order
                                  / math.factorial(order)*math.cos(height*ts[j]))
                        reflected = weight[j]*sum(
                            int(mu[d])*min(lp[j], max(0, length-math.log(d)))
                            for d in divisors)
                        regression.append(abs(direct-reflected))
                # This keeps the exact divisor sum before taking atom size.
                response = sum(int(mu[d])*np.minimum(lp, max(0, length-math.log(d)))
                               for d in divisors)
                absolute += float(np.abs(weight*response).sum())
                centre = (1.95+2.03)/2*order
                crossing_count += sum(int(np.count_nonzero(
                    (centre-length-math.log(d))*(ts-length-math.log(d)) < 0))
                    for d in divisors)
        else:
            b = np.zeros(upper)
        if a >= 2:
            variation += (a-1)*math.sqrt(float(energy_weight @ (previous-b)**2))
        previous = b
    return {
        "order": order, "population": population, "radius": radius,
        "height": height, "length": length, "cutoff": upper,
        "unpaidOrders": unpaid, "atomCount": atom_count,
        "physicalAtomCount": physical_count, "crossingIncidences": crossing_count,
        "jointRealSum": total, "sourceNormalizedJoint": radius**(order+1)*total,
        "physicalSourceNormalizedJoint": radius**(order+1)*physical_total,
        "absoluteAtomMass": absolute,
        "profileEnergyOverUnsignedProfileEnergy": profile_energy/unsigned_energy,
        "variationBudgetWithoutUnknownSqrtE": variation,
        "sourceNormalizedVariationWithoutUnknownSqrtE": radius**(order+1)*variation,
        "directAtomRegressionMaxError": max(regression, default=0.0),
        "regressionAtoms": len(regression),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--height", type=float, default=54.0)
    parser.add_argument("--radius", type=float, default=10001/20000)
    args = parser.parse_args()
    print(json.dumps({"scope": __doc__.strip(), "rows": [
        probe(6, 4096, args.height, args.radius),
        probe(8, 65536, args.height, args.radius),
    ]}, indent=2))


if __name__ == "__main__":
    main()

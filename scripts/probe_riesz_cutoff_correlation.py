#!/usr/bin/env python3
"""Optional finite sharp-Mobius cross-cutoff probe.

The integer Mobius/totient arrays are exact; reciprocal sums are floating
point. This is not a certificate, a literal masked-carrier estimate, or a
source-scale bound. It is not run by ordinary CI.
"""
import argparse
import json
import math

import numpy as np

from probe_riesz_sieve_mean import arithmetic


def probe(upper, cutoffs):
    mu, phi = arithmetic(upper)
    reciprocal = mu.astype(float)
    reciprocal[1:] /= np.arange(1, upper + 1)
    full_rows = np.array([float(reciprocal[g::g].sum())
                          for g in range(1, upper + 1)])
    rows = []
    for lower in cutoffs:
        lower_rows = np.array([float(reciprocal[g:lower+1:g].sum())
                               for g in range(1, lower + 1)])
        cross = float(np.dot(phi[1:lower+1] * full_rows[:lower], lower_rows))
        gap = math.log(upper / lower)
        rows.append({
            "largerCutoff": upper,
            "smallerCutoff": lower,
            "logGap": gap,
            "signedCrossQuadratic": cross,
            "absoluteTimesOnePlusGapSquared": abs(cross) * (1 + gap)**2,
        })
    return {"scope": __doc__.strip(), "rows": rows}


def family_probe(first, step, counts, population):
    """Retain signed cross-cutoff terms in both lcm and actual-population Grams."""
    cutoffs = [round(first * math.exp(step * j)) for j in range(max(counts))]
    if len(set(cutoffs)) != len(cutoffs):
        raise ValueError("The selected cutoffs must be distinct")
    upper = max(cutoffs)
    mu, phi = arithmetic(upper)
    reciprocal = mu.astype(float)
    reciprocal[1:] /= np.arange(1, upper + 1)
    harmonic_rows = np.zeros((len(cutoffs), upper))
    responses = np.zeros((len(cutoffs), population))
    current = np.zeros(population + 1, dtype=np.int32)
    previous = 0
    for i, cutoff in enumerate(cutoffs):
        harmonic_rows[i, :cutoff] = [float(reciprocal[g:cutoff+1:g].sum())
                                     for g in range(1, cutoff + 1)]
        for d in range(previous + 1, min(cutoff, population) + 1):
            current[d::d] += int(mu[d])
        responses[i] = current[1:]
        previous = cutoff
    weighted = harmonic_rows * np.sqrt(phi[1:])
    quadratic = weighted @ weighted.T
    actual = (responses @ responses.T) / population
    rows = []
    for count in counts:
        q = quadratic[:count, :count]
        m = actual[:count, :count]
        alternating = (-1.)**np.arange(count)
        # The proved sharper floor cost sums the cutoff coefficients with
        # their signs before taking an absolute value at each divisor.
        combined = np.zeros(cutoffs[count - 1] + 1)
        for sign, cutoff in zip(alternating, cutoffs[:count]):
            combined[1:cutoff + 1] += sign * mu[1:cutoff + 1]
        combined_mass = float(np.abs(combined).sum())
        # Smooth the two exterior endpoints without changing the interior
        # alternating signs. This is a diagnostic, not a campaign mask.
        tapered = alternating * np.sin(np.pi * (np.arange(count) + 1) / (count + 1))**2
        tapered_energy = float(tapered @ tapered)
        rows.append({
            "count": count,
            "cutoffs": cutoffs[:count],
            "minimumLogSpacing": float(np.diff(np.log(cutoffs[:count])).min()),
            "sharpQuadraticLargestEigenvalue": float(np.linalg.eigvalsh(q)[-1]),
            "sharpQuadraticLargestAbsoluteRow": float(np.abs(q).sum(axis=1).max()),
            "literalMeanLargestEigenvalueOverX": float(np.linalg.eigvalsh(m)[-1]),
            "sameSignJointQuadraticOverCoefficientEnergy": float(q.sum() / count),
            "alternatingJointQuadraticOverCoefficientEnergy": float(alternating @ q @ alternating / count),
            "alternatingLiteralMeanOverXCoefficientEnergy": float(alternating @ m @ alternating / count),
            "populationLength": population,
            "combinedFiniteErrorOverXCoefficientEnergy": sum(cutoffs[:count])**2 / (population * count),
            "signedCombinedCoefficientMass": combined_mass,
            "signedFiniteErrorOverXCoefficientEnergy": combined_mass**2 / (population * count),
            "taperedAlternatingQuadraticOverCoefficientEnergy": float(tapered @ q @ tapered / tapered_energy),
            "taperedAlternatingLiteralMeanOverXCoefficientEnergy": float(tapered @ m @ tapered / tapered_energy),
        })
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upper", type=int, default=100000)
    parser.add_argument("--cutoffs", nargs="+", type=int,
                        default=[100, 320, 1000, 3200, 10000, 32000, 100000])
    parser.add_argument("--families", action="store_true",
                        help="Also compare complete signed cutoff-family Grams")
    parser.add_argument("--population", type=int, default=200000)
    parser.add_argument("--family-first", type=int, default=32)
    parser.add_argument("--family-step", type=float, default=.5)
    parser.add_argument("--family-counts", nargs="+", type=int, default=[4, 8, 12, 16])
    args = parser.parse_args()
    if args.upper < 1 or not all(1 <= x <= args.upper for x in args.cutoffs):
        parser.error("Every cutoff must lie between one and the upper cutoff")
    if args.population < 1:
        parser.error("Population must be positive")
    if args.family_first < 1 or args.family_step <= 0 or min(args.family_counts) < 2:
        parser.error("Family first cutoff and spacing must be positive, and counts at least two")
    result = probe(args.upper, args.cutoffs)
    if args.families:
        result["families"] = family_probe(args.family_first, args.family_step,
                                           args.family_counts, args.population)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

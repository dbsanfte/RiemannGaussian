#!/usr/bin/env python3
"""Optional finite actual-label test of the near-pair energy partition.

All test counts, actual divisor columns, phases and factorial weights are
joined BEFORE the adverse cutoff selection. This is not the native
dyadic/physical/funding/many-bin support. Test L=11N/8; allocation is exactly
empty at the supported tiny orders. The exponential cutoff is very wide
here, so a separate rational 1/1000 cutoff is tested as a diagnostic only.
No floats in this script constitute interval or asymptotic certificates.
"""

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path

import numpy as np

from probe_riesz_post_hinge_correlations import divisors
from probe_riesz_signed_density import prime_table


def experiment(order, heights):
    radius, length = 10001 / 20000, 11 * order / 8
    assert not any(32 * k <= 13 * order and 5 * (order + 1 - k) < 4 * order
                   for k in range(order + 2))
    first = math.floor(math.exp(39 * order / 20)) + 1
    last = math.floor(math.exp(203 * order / 100))
    spf = prime_table(last)
    mu = np.ones(last + 1, dtype=np.int8)
    counts = np.zeros(last + 1, dtype=np.int16)
    largest = np.ones(last + 1, dtype=np.int64)
    for n in range(2, last + 1):
        p, a = spf[n], n // spf[n]
        mu[n] = 0 if a % p == 0 else -mu[a]
        counts[n] = counts[a] + int(a % p != 0)
        largest[n] = max(largest[a], p)
    labels = np.arange(first, last + 1)
    selected = labels[(mu[labels] != 0) & (counts[labels] >= 3) &
                      (np.log(largest[labels]) < (60069 / 100000) * np.log(labels))]
    endpoint = int(selected.max())
    increments = np.zeros((endpoint + 1, selected.size), dtype=np.int16)
    divisor_counts = np.zeros(selected.size)
    for i, n in enumerate(selected):
        ds = divisors(int(n), spf)
        divisor_counts[i] = len(ds)
        for d in ds:
            increments[d, i] = mu[d]
    cutoffs = np.arange(math.floor(math.exp(length)), endpoint)
    columns = np.cumsum(increments, axis=0, dtype=np.int16)[cutoffs].astype(float)
    steps = (np.maximum(length, np.log(cutoffs)) -
             np.maximum(length, np.log(cutoffs + 1)))
    profile = cutoffs * steps ** 2
    off_diagonal = ~np.eye(selected.size, dtype=bool)
    gcds = np.gcd.outer(selected, selected)
    large = (np.log(gcds) > order / 1000) & off_diagonal
    small = ~large & off_diagonal
    differences = np.abs(selected[:, None] - selected[None, :])
    minima = np.minimum(selected[:, None], selected[None, :])
    native_epsilon = math.exp(-order / 1000)
    masks = [
        ("literal-exponential-threshold", native_epsilon,
         (differences <= native_epsilon * minima) & off_diagonal),
        ("rational-threshold-diagnostic-only", 1 / 1000,
         (1000 * differences <= minima) & off_diagonal),
    ]
    rows = []
    for name, epsilon, close in masks:
        degrees = close.sum(axis=1)
        assert np.all(degrees <= 2 * epsilon * selected + 1e-10)
        a = divisor_counts / selected
        pair_mass = float(np.sum(close * a[:, None] * a[None, :]))
        degree_mass = float(np.sum(degrees * a ** 2))
        capacity_mass = float(2 * epsilon * np.sum(divisor_counts ** 2 / selected))
        assert pair_mass <= degree_mass + 1e-12
        assert degree_mass <= capacity_mass + 1e-12
        rows.append({"threshold": name, "epsilon": epsilon,
                     "orderedClosePairs": int(close.sum()),
                     "actualReciprocalPairMass": pair_mass,
                     "degreeSquareMass": degree_mass,
                     "capacitySquareMass": capacity_mass})
    logs = np.log(selected)
    common = (-radius ** (order + 1) / (length * math.factorial(order)) *
              np.exp(-1.5 * logs) * logs ** (order + 1))
    cases = []
    for height in heights:
        weights = common * np.cos(height * logs)
        prefix = columns @ weights
        adverse = prefix * steps < 0
        active_columns = columns[adverse]
        gram = active_columns.T @ (active_columns / cutoffs[adverse, None])
        pairs = weights[:, None] * weights[None, :] * gram
        diagonal = float(np.trace(pairs))
        np.fill_diagonal(pairs, 0)
        large_cross = float(pairs[large].sum())
        small_cross = float(pairs[small].sum())
        whole_cross = float(pairs.sum())
        energy = float(np.sum(prefix[adverse] ** 2 / cutoffs[adverse]))
        scale = max(abs(whole_cross), diagonal, energy, 1e-15)
        assert abs(large_cross + small_cross - whole_cross) <= 1e-10 * scale
        assert abs(energy - diagonal - whole_cross) <= 1e-10 * scale
        profile_energy = float(profile[adverse].sum())
        signed_sum = float(np.sum(prefix * steps))
        assert -math.sqrt(energy * profile_energy) <= signed_sum + 1e-12
        for name, epsilon, close in masks:
            near = small & close
            separated = small & ~close
            near_cross = float(pairs[near].sum())
            separated_cross = float(pairs[separated].sum())
            assert abs(near_cross + separated_cross - small_cross) <= 1e-10 * scale
            before = math.sqrt(max(small_cross, 0) * profile_energy)
            after = math.sqrt(max(separated_cross, 0) * profile_energy)
            price = math.sqrt(abs(near_cross) * profile_energy)
            assert before <= after + price + 1e-12
            cases.append({"order": order, "height": height, "threshold": name,
                          "epsilon": epsilon, "labelCount": int(selected.size),
                          "sourceScaledSignedLiteralSum": signed_sum,
                          "smallSharedCross": small_cross, "nearCross": near_cross,
                          "separatedCross": separated_cross,
                          "orderedSmallerGcdNearPairs": int(near.sum()),
                          "orderedSeparatedSmallerGcdPairs": int(separated.sum()),
                          "costBefore": before, "remainingCost": after,
                          "finiteNearPrice": price,
                          "adverseCutoffsReselectedAfterPartition": False,
                          "nativeMovingLengthUsed": False,
                          "nativeFundingWitnessUsed": False,
                          "nativePhysicalPrimeMasksCertified": False,
                          "nativeCount56PlusManyBinPopulationCertified": False})
    return cases, {"order": order, "labelCount": int(selected.size), "rows": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="+", default=[4])
    parser.add_argument("--heights", type=float, nargs="+", default=[54, 65, 100])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if any(n not in (4, 5) for n in args.orders):
        parser.error("the complete finite diagnostic supports orders 4..5")
    if any(not math.isfinite(y) or y < 54 for y in args.heights):
        parser.error("heights must be finite and >=54")
    rate = Fraction(1, 1000) - Fraction(1, 5000) - Fraction(3, 262144)
    assert rate > Fraction(1, 2000)
    results = [experiment(n, args.heights) for n in args.orders]
    cases = [case for result, _ in results for case in result]
    report = {"scope": "Actual finite Gram pairs, original joined adverse selection.",
              "nearThreshold": "|n-m| <= exp(-N/1000)*min(n,m)",
              "diagnosticThresholdHasNoCofinalUse": True,
              "conservativeRateMargin": str(rate), "requestedRate": "1/2000",
              "capacityChecks": [result for _, result in results], "cases": cases,
              "rigorousIntervalArithmetic": False, "nativeDyadicSupportUsed": False,
              "nativeFundingWitnessUsed": False, "cofinalSeparatedBudgetProved": False,
              "automaticManyBinOrthogonalityProved": False, "floorCertified": False}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    diagnostic = [c for c in cases if c["threshold"] == "rational-threshold-diagnostic-only"]
    print(json.dumps({"cases": len(cases),
                      "positiveDiagnosticSeparatedCases": sum(c["separatedCross"] > 0 for c in diagnostic),
                      "negativeDiagnosticSeparatedCases": sum(c["separatedCross"] < 0 for c in diagnostic),
                      "cofinalSeparatedBudgetProved": False, "floorCertified": False}, indent=2))


if __name__ == "__main__":
    main()

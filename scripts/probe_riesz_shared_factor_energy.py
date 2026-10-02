#!/usr/bin/env python3
"""Optional actual-integer shared/coprime cross-energy diagnostic.

All test labels and counts, divisor columns, total-label phases and
factorial weights are joined before the ORIGINAL adverse cutoff selection.
No funding witness, native dyadic/physical/count56+ support or cofinal
bound is certified. Orders 4..5 have exactly empty allocation support;
the test length 11N/8 is not the native moving length. Outside normal CI.
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
    for i, n in enumerate(selected):
        for d in divisors(int(n), spf):
            increments[d, i] = mu[d]
    cutoffs = np.arange(math.floor(math.exp(length)), endpoint)
    columns = np.cumsum(increments, axis=0, dtype=np.int16)[cutoffs].astype(float)
    steps = (np.maximum(length, np.log(cutoffs)) -
             np.maximum(length, np.log(cutoffs + 1)))
    profile = cutoffs * steps ** 2
    gcds = np.gcd.outer(selected, selected)
    large = np.log(gcds) > order / 1000
    off_diagonal = ~np.eye(selected.size, dtype=bool)
    large &= off_diagonal
    small = ~large & off_diagonal
    cofactor_ids = selected // largest[selected]
    same_cofactor = (cofactor_ids[:, None] == cofactor_ids[None, :]) & off_diagonal
    assert np.all(large[same_cofactor])
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
        far, near, cross = (float(pairs[large].sum()), float(pairs[small].sum()),
                            float(pairs.sum()))
        energy = float(np.sum(prefix[adverse] ** 2 / cutoffs[adverse]))
        scale = max(abs(cross), diagonal, energy, 1e-15)
        assert abs(far + near - cross) <= 1e-10 * scale
        assert abs(energy - diagonal - cross) <= 1e-10 * scale
        profile_energy = float(profile[adverse].sum())
        before = math.sqrt(max(cross, 0) * profile_energy)
        after = math.sqrt(max(near, 0) * profile_energy)
        shared_price = math.sqrt(abs(far) * profile_energy)
        assert before <= after + shared_price + 1e-12
        actual_period_cost = math.sqrt(energy * profile_energy)
        literal_signed = float(np.sum(prefix * steps))
        assert -actual_period_cost <= literal_signed + 1e-12
        count_pairs = []
        for c in np.unique(counts[selected]):
            for d in np.unique(counts[selected]):
                mask = ((counts[selected, None] == c) &
                        (counts[selected][None, :] == d) & small)
                count_pairs.append({"left": int(c), "right": int(d),
                                    "signedSmallSharedCross": float(pairs[mask].sum())})
        cases.append({
            "order": order, "height": height, "labelCount": int(selected.size),
            "sourceScaledSignedLiteralSum": literal_signed,
            "wholeFundedAdverseCutoffsReselectedAfterPartition": False,
            "diagonal": diagonal, "wholeSignedCross": cross,
            "largeSharedCross": far, "smallSharedCross": near,
            "coprimeCross": float(pairs[(gcds == 1) & off_diagonal].sum()),
            "sameCofactorCross": float(pairs[same_cofactor].sum()),
            "absoluteLargeSharedCross": float(np.abs(pairs[large]).sum()),
            "smallSharedCountPairs": count_pairs,
            "crossCostBefore": before, "crossCostAfter": after,
            "actualSharedPrice": shared_price,
            "nativeManyBinPopulationCertified": False,
            "nativeMovingLengthUsed": False,
            "nativePhysicalPrimeMasksCertified": False,
            "nativeFundingWitnessIncluded": False,
        })
    return cases


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
    rate = Fraction(1, 2000) - Fraction(1, 5000) - Fraction(6, 262144)
    assert rate > Fraction(1, 4000)
    cases = [case for n in args.orders for case in experiment(n, args.heights)]
    report = {"scope": "Complete finite actual-integer cross pairs with original adverse cutoff selection.",
              "largeSharedThreshold": "log(gcd(n,m)) > N/1000",
              "conservativeRateMargin": str(rate), "requestedRate": "1/4000",
              "nativeFundingWitnessUsed": False, "nativeDyadicSupportUsed": False,
              "nativeManyBinPopulationCertified": False, "rigorousIntervalArithmetic": False,
              "cofinalSmallSharedBoundProved": False, "floorCertified": False,
              "cases": cases}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": len(cases),
                      "positiveSmallSharedCases": sum(c["smallSharedCross"] > 0 for c in cases),
                      "negativeSmallSharedCases": sum(c["smallSharedCross"] < 0 for c in cases),
                      "cofinalSmallSharedBoundProved": False, "floorCertified": False}, indent=2))


if __name__ == "__main__":
    main()

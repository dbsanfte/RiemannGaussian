#!/usr/bin/env python3
"""Optional whole signed prefix/cross-energy diagnostic on actual integers.

Retains the total-label phase, squarefree/count/owner crop, full factorial
radial weight, every actual divisor and the exact corrected-profile steps.
Counts and labels are joined before selecting adverse COMPLETE increments.
Orders 4..7 have empty original allocation support. The length 11N/8 and
these small-order supports are NOT the native count56+ many-bin population,
dyadic schedule, physical prime masks or funding witness. Floating outputs
are not interval certificates or asymptotic evidence. Outside ordinary CI.
"""

import argparse
import json
import math
from pathlib import Path

import numpy as np

from probe_riesz_post_hinge_correlations import divisors
from probe_riesz_signed_density import prime_table


def experiment(order, heights):
    length, radius = 11 * order / 8, 10001 / 20000
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
    labels = np.arange(1, last + 1)
    logs = np.log(labels)
    support = ((labels >= first) & (mu[1:] != 0) & (counts[1:] >= 3) &
               (np.log(largest[1:]) < (60069 / 100000) * logs))
    selected = labels[support]
    endpoint = int(selected.max())
    cutoffs = np.arange(math.floor(math.exp(length)), endpoint)
    steps = (np.maximum(length, np.log(cutoffs)) -
             np.maximum(length, np.log(cutoffs + 1)))
    assert np.all(steps < 0)
    profile = cutoffs * steps ** 2
    results = []
    for height in heights:
        weights = np.zeros(last + 1)
        weights[1:] = (support * (-radius ** (order + 1) /
                                  (length * math.factorial(order))) *
                       np.exp(-1.5 * logs) * logs ** (order + 1) *
                       np.cos(height * logs))
        increments = np.zeros(endpoint + 1)
        diagonal_increments = np.zeros(endpoint + 1)
        direct_sum = 0.0
        for n in selected:
            prefix = 0
            riesz = 0.0
            weight = weights[n]
            for d in divisors(int(n), spf):
                sign = int(mu[d])
                increments[d] += sign * weight
                next_prefix = prefix + sign
                diagonal_increments[d] += weight ** 2 * (next_prefix ** 2 - prefix ** 2)
                prefix = next_prefix
                riesz += sign * max(0.0, length - math.log(d))
            direct_sum += weight * riesz
        prefixes = np.cumsum(increments)[cutoffs]
        diagonal_prefixes = np.cumsum(diagonal_increments)[cutoffs]
        scale = max(float(np.max(diagonal_prefixes)), np.finfo(float).tiny)
        assert float(np.min(diagonal_prefixes)) >= -1e-10 * scale
        energy_terms = prefixes ** 2 / cutoffs
        diagonal_terms = diagonal_prefixes / cutoffs
        cross_terms = energy_terms - diagonal_terms
        adverse = prefixes * steps < 0
        signed_sum = float(np.sum(prefixes * steps))
        cancellation_roundoff_scale = float(np.sum(np.abs(prefixes * steps)))
        assert abs(signed_sum - direct_sum) <= 1e-9 * max(cancellation_roundoff_scale, 1e-15)
        ea = float(np.sum(energy_terms[adverse]))
        da = float(np.sum(diagonal_terms[adverse]))
        ca = float(np.sum(cross_terms[adverse]))
        pa = float(np.sum(profile[adverse]))
        cost = math.sqrt(ea * pa)
        cross_cost = math.sqrt(max(ca, 0.0) * pa)
        diagonal_cost = math.sqrt(max(da, 0.0) * pa)
        assert cross_cost <= cost + 1e-12
        assert cost <= cross_cost + diagonal_cost + 1e-12
        assert -cost <= signed_sum + 1e-12
        period_ids = np.floor(height * np.log(cutoffs) / (2 * math.pi)).astype(np.int64)
        period_cross = [float(np.sum(cross_terms[adverse & (period_ids == period)]))
                        for period in np.unique(period_ids)]
        results.append({
            "order": order, "height": height, "labelCount": int(selected.size),
            "countsPresent": [int(x) for x in np.unique(counts[selected])],
            "testLength": length, "exactAllocationSupportEmpty": True,
            "sourceScaledSignedLiteralSum": signed_sum,
            "sumThenSelectAdverseCutoffs": True,
            "adversePhaseEnergy": ea, "adverseDiagonal": da,
            "adverseSignedCross": ca, "adverseProfileEnergy": pa,
            "formerAdverseCost": cost, "crossOnlyCost": cross_cost,
            "actualDiagonalPrice": diagonal_cost,
            "adverseCrossEnergyByCutoffPeriod": period_cross,
            "crossProfileProduct": max(ca, 0.0) * pa,
            "finiteDiagnosticThreshold": (79 / 1000) ** 2,
            "positiveCrossPeriods": sum(x > 0 for x in period_cross),
            "negativeCrossPeriods": sum(x < 0 for x in period_cross),
            "nativeManyBinSupportCertified": False,
            "nativePhysicalPrimeMasksCertified": False,
            "nativeFundingWitnessIncluded": False,
        })
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="+", default=[4, 5, 6, 7])
    parser.add_argument("--heights", type=float, nargs="+", default=[54, 65, 100])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if any(n not in (4, 5, 6, 7) for n in args.orders):
        parser.error("the exact empty-allocation diagnostic supports orders 4..7")
    if any(not math.isfinite(y) or y < 54 for y in args.heights):
        parser.error("heights must be finite and >=54")
    cases = [case for n in args.orders for case in experiment(n, args.heights)]
    report = {
        "scope": "Actual-integer signed adverse cross energy, all selected counts joined.",
        "nativeDyadicSupportUsed": False, "nativeMovingLengthUsed": False,
        "nativeManyBinPopulationCertified": False, "nativeFundingWitnessUsed": False,
        "rigorousIntervalArithmetic": False, "cofinalCrossEnergyBoundProved": False,
        "floorCertified": False, "cases": cases,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": len(cases),
                      "casesWithPositiveAdverseCross": sum(c["adverseSignedCross"] > 0 for c in cases),
                      "crossCostRange": [min(c["crossOnlyCost"] for c in cases),
                                         max(c["crossOnlyCost"] for c in cases)],
                      "cofinalCrossEnergyBoundProved": False,
                      "floorCertified": False}, indent=2))


if __name__ == "__main__":
    main()

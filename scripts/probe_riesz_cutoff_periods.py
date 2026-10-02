#!/usr/bin/env python3
"""Optional finite actual-integer probe of joined signed cutoff periods.

The total-log window, squarefree labels, original phases and empty exact
allocation are retained. L=11N/8 is a test length. These orders are NOT the
native unpaid count-56+ population, and no funding witness is supplied.
The LP fits exact logarithmic null directions, not new carrier coefficients.
Floating results are diagnostics, not interval or source-scale certificates.
Requires numpy and scipy; this script is deliberately outside ordinary CI.
"""

import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

from probe_riesz_signed_density import prime_table


def experiment(order, heights):
    radius, length = 10001 / 20000, 11 * order / 8
    first = math.floor(math.exp(39 * order / 20)) + 1
    last = math.floor(math.exp(203 * order / 100))
    assert not any(32 * k <= 13 * order and 5 * (order + 1 - k) < 4 * order
                   for k in range(order + 2))
    spf = prime_table(last)
    mu = np.ones(last + 1)
    count = np.zeros(last + 1, dtype=np.int64)
    largest = np.ones(last + 1, dtype=np.int64)
    for n in range(2, last + 1):
        p, a = spf[n], n // spf[n]
        count[n] = count[a] + int(a % p != 0)
        mu[n] = 0 if a % p == 0 else -mu[a]
        largest[n] = max(largest[a], p)
    labels = np.arange(1, last + 1)
    logs = np.log(labels)
    support = ((labels >= first) & (mu[1:] != 0) & (count[1:] >= 3) &
               (np.log(largest[1:]) < (60069 / 100000) * logs))
    endpoint = int(labels[support].max())
    cutoffs = np.arange(1, endpoint)
    log_step = np.log((cutoffs + 1) / cutoffs)
    log_squared_step = np.diff(logs[:endpoint] ** 2)
    hinge_step = -np.diff(np.maximum(0.0, length - logs[:endpoint]))
    slope = float(np.sum(cutoffs * hinge_step * log_step) /
                  np.sum(cutoffs * log_step ** 2))
    delta = hinge_step - slope * log_step
    riesz = np.zeros(last + 1)
    for d in range(1, min(last, math.floor(math.exp(length))) + 1):
        if mu[d]:
            riesz[d::d] += mu[d] * max(0.0, length - math.log(d))
    cases = []
    for height in heights:
        weights = np.zeros(last + 1)
        weights[1:] = (support * (-radius ** (order + 1) /
                                  (length * math.factorial(order))) *
                       np.exp(-1.5 * logs) * logs ** (order + 1) *
                       np.cos(height * logs))
        increments = np.zeros(last + 1)
        for d in range(1, last + 1):
            if mu[d]:
                increments[d] = mu[d] * np.sum(weights[d::d])
        prefix = np.cumsum(increments)[1:endpoint]
        terms = prefix * delta
        actual = float(np.sum(weights * riesz))
        pairing_error = abs(actual - float(np.sum(terms)))
        assert pairing_error < 1e-12
        adverse = terms < 0
        atomic_cost = float(-np.sum(terms[adverse]))
        previous_cost = math.sqrt(
            float(np.sum(prefix[adverse] ** 2 / cutoffs[adverse])) *
            float(np.sum(cutoffs[adverse] * delta[adverse] ** 2)))
        variants = []
        for periods in [1, 2, 4, 8]:
            for offset in [0.0, 0.25, 0.5, 0.75]:
                group_keys = np.floor(height * np.log(cutoffs) /
                                      (2 * math.pi * periods) + offset).astype(int)
                grouped = np.bincount(group_keys, weights=terms)
                grouped_cost = float(-np.sum(grouped[grouped < 0]))
                variation_saving = (float(np.sum(np.abs(terms))) -
                                    float(np.sum(np.abs(grouped)))) / 2
                assert abs(atomic_cost - grouped_cost - variation_saving) < 1e-12
                assert grouped_cost <= atomic_cost + 1e-12
                assert actual >= -grouped_cost - 1e-12

                raw = np.bincount(group_keys, weights=prefix * hinge_step)
                log_moment = np.bincount(group_keys, weights=prefix * log_step)
                square_moment = np.bincount(group_keys, weights=prefix * log_squared_step)
                assert abs(float(np.sum(log_moment))) < 1e-10
                assert abs(float(np.sum(square_moment))) < 1e-10
                magnitude = max(float(np.max(np.abs(raw))),
                                float(np.max(np.abs(log_moment))),
                                float(np.max(np.abs(square_moment))), 1e-300)
                matrix = np.column_stack((log_moment / magnitude,
                                          square_moment / magnitude,
                                          -np.eye(len(grouped))))
                solution = linprog(np.concatenate((np.zeros(2), np.ones(len(grouped)))),
                                   A_ub=matrix, b_ub=raw / magnitude,
                                   bounds=[(None, None), (None, None)] +
                                          [(0, None)] * len(grouped), method="highs")
                assert solution.success, solution.message
                corrected = (raw - solution.x[0] * log_moment -
                             solution.x[1] * square_moment)
                optimized_cost = float(-np.sum(corrected[corrected < 0]))
                assert optimized_cost <= grouped_cost + 1e-10
                assert actual >= -optimized_cost - 1e-10
                variants.append({
                    "periodsPerBlock": periods, "offset": offset,
                    "blockCount": len(grouped), "groupedCost": grouped_cost,
                    "groupedToFormerCost": grouped_cost / previous_cost,
                    "groupedToAtomicCost": grouped_cost / atomic_cost,
                    "signedVariationSaving": variation_saving,
                    "optimizedLogSlope": float(solution.x[0]),
                    "optimizedLogSquaredSlope": float(solution.x[1]),
                    "optimizedCost": optimized_cost,
                    "optimizedToFormerCost": optimized_cost / previous_cost,
                    "negativeOptimizedBlockCount": int((corrected < 0).sum()),
                    "nullLogMomentFloatingError": abs(float(np.sum(log_moment))),
                    "nullSquaredLogMomentFloatingError": abs(float(np.sum(square_moment))),
                    "partitionFloatingError": abs(float(np.sum(grouped)) - actual)
                })
        cases.append({"order": order, "height": height, "labelCount": int(support.sum()),
                      "endpoint": endpoint, "testLength": length,
                      "originalCenteringSlope": slope, "exactAllocationSupportEmpty": True,
                      "actualSignedCarrier": actual, "previousOneSidedCost": previous_cost,
                      "atomicAdverseCost": atomic_cost, "prefixPairingFloatingError": pairing_error,
                      "variants": variants})
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="+", default=[4, 5, 6])
    parser.add_argument("--heights", type=float, nargs="+", default=[54, 65, 100])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if any(n < 4 or n > 6 for n in args.orders):
        parser.error("the exact empty-allocation probe supports only orders 4..6")
    if any(not math.isfinite(y) or y < 54 for y in args.heights):
        parser.error("this phase-period probe requires finite heights >=54")
    cases = [r for n in args.orders for r in experiment(n, args.heights)]
    report = {"scope": "Generic small-order actual-integer signed cutoff-period diagnostics.",
              "nativeMovingLengthUsed": False, "literalUnpaidCount56SupportUsed": False,
              "nativePhysicalPrimeMasksUsed": False, "fundingWitnessIncluded": False,
              "rigorousIntervalArithmetic": False, "sourceScaleSavingCertified": False,
              "numericalFloorCertified": False, "cases": cases}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    fixed = [next(v for v in r["variants"] if v["periodsPerBlock"] == 1 and v["offset"] == 0)
             for r in cases]
    print(json.dumps({"cases": len(cases), "fixedOnePeriodGroupedCostRatioRange": [
        min(v["groupedToFormerCost"] for v in fixed), max(v["groupedToFormerCost"] for v in fixed)],
        "fixedOnePeriodOptimizedCostRatioRange": [min(v["optimizedToFormerCost"] for v in fixed),
                                                 max(v["optimizedToFormerCost"] for v in fixed)],
        "sourceScaleSavingCertified": False, "numericalFloorCertified": False}, indent=2))


if __name__ == "__main__":
    main()

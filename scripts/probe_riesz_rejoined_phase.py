#!/usr/bin/env python3
"""Optional actual-integer regression for the rejoined signed prefix cost.

All squarefree labels, divisor signs, total-log phases and factorial weights
in each finite test support are literal. This is a GENERIC finite regression:
L=11N/8 is a test parameter, not the repo's rounded moving length, and these
small-order/count samples are NOT the growing unpaid core population.
No fixed-height asymptotic saving or -79/1000 floor is certified.
"""

import argparse
import json
import math
from pathlib import Path

import numpy as np

from probe_riesz_signed_density import prime_table


def experiment(order, heights):
    radius = 10001 / 20000
    length = 11 * order / 8
    first = math.floor(math.exp(39 * order / 20)) + 1
    last = math.floor(math.exp(203 * order / 100))
    # The necessary integer order conditions in unpaidOrders_support have
    # no solution here, so assignedAmplitude is zero for every prime set.
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
               (np.log(largest[1:]) < (751 / 1250) * logs))
    classes = sorted(int(k) for k in set(count[1:][support]))
    profile_endpoint = int(labels[support].max())
    positions = np.arange(1, profile_endpoint)
    log_step = np.log((positions + 1) / positions)
    hinge = np.maximum(0.0, length - logs[:profile_endpoint])
    increment = -np.diff(hinge)
    slope = np.sum(positions * increment * log_step) / np.sum(positions * log_step**2)
    delta = increment - slope * log_step
    profile_energy = float(np.sum(positions * delta**2))
    # Compute the actual divisor convolution independently for the signed
    # carrier, rather than reconstructing it from its energy inequality.
    riesz = np.zeros(last + 1)
    for d in range(1, min(last, math.floor(math.exp(length))) + 1):
        if mu[d]:
            riesz[d::d] += mu[d] * max(0.0, length - math.log(d))
    rows = []
    for height in heights:
        weights = np.zeros(last + 1)
        weights[1:] = (support * (-radius**(order + 1) / (length * math.factorial(order))) *
                       np.exp(-1.5 * logs) * logs**(order + 1) * np.cos(height * logs))
        correlations, separate_costs, class_energies = [], [], []
        for k in classes:
            selected = weights * (count == k)
            increments = np.zeros(last + 1)
            for d in range(1, last + 1):
                if mu[d]:
                    increments[d] = mu[d] * np.sum(selected[d::d])
            correlation = np.cumsum(increments)[1:profile_endpoint]
            energy = float(np.sum(correlation**2 / positions))
            correlations.append(correlation)
            class_energies.append(energy)
            separate_costs.append(math.sqrt(energy * profile_energy))
        joined = np.sum(correlations, axis=0)
        energy = float(np.sum(joined**2 / positions))
        joint_cost = math.sqrt(energy * profile_energy)
        old_cost = sum(separate_costs)
        actual_signed = float(np.sum(weights * riesz))
        joined_increments = joined * delta
        adverse = joined_increments < 0
        adverse_energy = float(np.sum(joined[adverse]**2 / positions[adverse]))
        adverse_profile_energy = float(np.sum(positions[adverse] * delta[adverse]**2))
        one_sided_cost = math.sqrt(adverse_energy * adverse_profile_energy)
        pairing_error = abs(actual_signed - float(np.sum(joined_increments)))
        assert joint_cost <= old_cost + 1e-12
        assert abs(actual_signed) <= joint_cost + 1e-12
        assert one_sided_cost <= joint_cost + 1e-12
        assert actual_signed >= -one_sided_cost - 1e-12
        assert pairing_error < 1e-12
        cross = []
        for i, k in enumerate(classes):
            for j in range(i + 1, len(classes)):
                cross.append({"leftCount": k, "rightCount": classes[j],
                              "signedCrossEnergy": float(np.sum(
                                  correlations[i] * correlations[j] / positions))})
        assert abs(energy - sum(class_energies) - 2 * sum(
            p["signedCrossEnergy"] for p in cross)) < 1e-12
        rows.append({"order": order, "height": height, "testLength": length,
                     "physicalFirst": first, "physicalLast": last,
                     "commonProfileEndpoint": profile_endpoint,
                     "labelCount": int(support.sum()), "primeCounts": classes,
                     "exactAllocationSupportEmpty": True,
                     "centeringSlope": float(slope), "profileEnergy": profile_energy,
                     "actualSignedCarrier": actual_signed,
                     "phaseEnergy": energy, "separateCountPhaseEnergies": class_energies,
                     "signedCrossCountEnergies": cross,
                     "jointCost": joint_cost, "separateCountCost": old_cost,
                     "jointToSeparateRatio": joint_cost / old_cost,
                     "oneSidedCost": one_sided_cost,
                     "oneSidedToTwoSidedRatio": one_sided_cost / joint_cost,
                     "adverseJoinedPrefixEnergy": adverse_energy,
                     "adverseProfileEnergy": adverse_profile_energy,
                     "favorablePrefixContribution": float(np.sum(joined_increments[~adverse])),
                     "adversePrefixContribution": float(np.sum(joined_increments[adverse])),
                     "prefixPairingFloatingError": pairing_error,
                     "savedSquaredCost": old_cost**2 - joint_cost**2,
                     "certifiesUnpaidPopulationSaving": False})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="+", default=[4, 5, 6])
    parser.add_argument("--heights", type=float, nargs="+", default=[0, 54, 65, 100])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if any(n < 4 or n > 6 for n in args.orders):
        parser.error("this optional finite regression supports orders 4 through 6")
    if any(not math.isfinite(y) or y < 0 for y in args.heights):
        parser.error("heights must be finite and nonnegative")
    cases = [case for n in args.orders for case in experiment(n, args.heights)]
    report = {"scope": "Generic finite actual-integer signed correlation regression.",
              "roundedMovingLengthUsed": False, "exactLiteralUnpaidSupportUsed": False,
              "countBinMaskCompletionUsed": False, "separateLegPhaseApproximationUsed": False,
              "actualCarrierMomentsMeasured": True, "prescribedOwnerAmplitudesUsed": False,
              "rigorousIntervalArithmetic": False, "cases": cases,
              "sourceScaleSavingCertified": False, "numericalFloorCertified": False}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    positive = [r for r in cases if r["height"] >= 54]
    print(json.dumps({"testCases": len(cases), "positiveHeightCases": len(positive),
                      "positiveHeightJointToSeparateRange": [
                          min(r["jointToSeparateRatio"] for r in positive),
                          max(r["jointToSeparateRatio"] for r in positive)],
                      "positiveHeightOneSidedToTwoSidedRange": [
                          min(r["oneSidedToTwoSidedRatio"] for r in positive),
                          max(r["oneSidedToTwoSidedRatio"] for r in positive)],
                      "maximumActualLabelCount": max(r["labelCount"] for r in cases),
                      "sourceScaleSavingCertified": False,
                      "numericalFloorCertified": False}, indent=2))


if __name__ == "__main__":
    main()

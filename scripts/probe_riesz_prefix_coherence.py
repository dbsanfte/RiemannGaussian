#!/usr/bin/env python3
"""Optional actual-integer probe of the existing prefix-energy channel.

This tests endpoint centering and exact subtraction of the constant prefix
component. It is not the unpaid count-56+ population, not the repo's rounded
moving length, and not a source-scale/floor certificate. No result runs in CI.
"""

import argparse
import json
import math
from pathlib import Path

import numpy as np

from probe_riesz_signed_density import prime_table


def experiment(order, heights):
    radius, length = 10001 / 20000, 11 * order / 8
    first = math.floor(math.exp(39 * order / 20)) + 1
    last = math.floor(math.exp(203 * order / 100))
    assert not any(32 * k <= 13 * order and 5 * (order + 1 - k) < 4 * order
                   for k in range(order + 2))
    spf = prime_table(last)
    mu = np.ones(last + 1)
    counts = np.zeros(last + 1, dtype=np.int64)
    largest = np.ones(last + 1, dtype=np.int64)
    for n in range(2, last + 1):
        p, a = spf[n], n // spf[n]
        counts[n] = counts[a] + int(a % p != 0)
        mu[n] = 0 if a % p == 0 else -mu[a]
        largest[n] = max(largest[a], p)
    labels = np.arange(1, last + 1)
    logs = np.log(labels)
    support = ((labels >= first) & (mu[1:] != 0) & (counts[1:] >= 3) &
               (np.log(largest[1:]) < (751 / 1250) * logs))
    endpoint = int(labels[support].max())
    cutoffs = np.arange(1, endpoint)
    hinge = np.maximum(0.0, length - logs[:endpoint])
    log_step = np.log((cutoffs + 1) / cutoffs)
    # This slope forces both endpoint values to be zero. Thus the exact
    # prefix pairing is unchanged on subtracting ANY constant from Phi.
    slope = (hinge[0] - hinge[-1]) / math.log(endpoint)
    delta = -np.diff(hinge) - slope * log_step
    profile_energy = float(np.sum(cutoffs * delta**2))
    harmonic_mass = float(np.sum(1 / cutoffs))
    riesz = np.zeros(last + 1)
    for d in range(1, min(last, math.floor(math.exp(length))) + 1):
        if mu[d]:
            riesz[d::d] += mu[d] * max(0.0, length - math.log(d))
    rows = []
    for height in heights:
        weights = np.zeros(last + 1)
        weights[1:] = (support * (-radius**(order + 1) / (length * math.factorial(order))) *
                       np.exp(-1.5 * logs) * logs**(order + 1) * np.cos(height * logs))
        increments = np.zeros(last + 1)
        for d in range(1, last + 1):
            if mu[d]:
                increments[d] = mu[d] * np.sum(weights[d::d])
        prefix = np.cumsum(increments)[1:endpoint]
        common_moment = float(np.sum(weights))
        assert abs(prefix[0] - common_moment) < 1e-12
        anchor = float(np.sum(prefix / cutoffs) / harmonic_mass)
        centered = prefix - anchor

        def costs(phi):
            energy = float(np.sum(phi**2 / cutoffs))
            adverse = phi * delta < 0
            one_sided = math.sqrt(float(np.sum(phi[adverse]**2 / cutoffs[adverse])) *
                                  float(np.sum(cutoffs[adverse] * delta[adverse]**2)))
            return energy, math.sqrt(energy * profile_energy), one_sided

        energy, full_cost, one_sided_cost = costs(prefix)
        centered_energy, centered_cost, centered_one_sided = costs(centered)
        value = float(np.sum(prefix * delta))
        direct_error = abs(value - float(np.sum(weights * riesz)))
        pairing_error = abs(value - float(np.sum(centered * delta)))
        variance_error = abs(energy - centered_energy - anchor**2 * harmonic_mass)
        assert pairing_error < 1e-12
        assert direct_error < 1e-12
        assert variance_error < 1e-12
        assert value >= -one_sided_cost - 1e-12
        assert value >= -centered_one_sided - 1e-12
        assert centered_cost <= full_cost + 1e-12
        rows.append({"order": order, "height": height, "testLength": length,
                     "labelCount": int(support.sum()), "endpoint": endpoint,
                     "phaseEnergy": energy, "commonSignedMoment": common_moment,
                     "firstCutoffEnergyFraction": common_moment**2 / energy,
                     "endpointCenteringSlope": slope, "optimalPrefixAnchor": anchor,
                     "actualSignedCarrier": value,
                     "fullCostRatio": centered_cost / full_cost,
                     "oneSidedCostRatio": centered_one_sided / one_sided_cost,
                     "constantProjectionSquaredSaving": anchor**2 * harmonic_mass,
                     "originalRieszCarrierFloatingError": direct_error,
                     "exactPairingFloatingError": pairing_error,
                     "varianceIdentityFloatingError": variance_error,
                     "sourceScaleSavingCertified": False})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="+", default=[4, 5, 6])
    parser.add_argument("--heights", type=float, nargs="+", default=[54, 65, 100])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if any(n < 4 or n > 6 for n in args.orders):
        parser.error("the exact empty-allocation regression supports orders 4..6")
    if any(not math.isfinite(y) or y < 0 for y in args.heights):
        parser.error("heights must be finite and nonnegative")
    cases = [r for n in args.orders for r in experiment(n, args.heights)]
    report = {"scope": "Generic small-order actual-integer prefix projection test.",
              "nativeMovingLengthUsed": False, "literalUnpaidSupportUsed": False,
              "fundingPopulationIncluded": False, "primeBinAntiConcentrationAssumed": False,
              "rigorousIntervalArithmetic": False, "sourceScaleSavingCertified": False,
              "floorCertified": False, "cases": cases}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": len(cases), "fullCostRatioRange": [
        min(r["fullCostRatio"] for r in cases), max(r["fullCostRatio"] for r in cases)],
        "oneSidedCostRatioRange": [min(r["oneSidedCostRatio"] for r in cases),
                                  max(r["oneSidedCostRatio"] for r in cases)],
        "firstCutoffEnergyFractionRange": [min(r["firstCutoffEnergyFraction"] for r in cases),
                                          max(r["firstCutoffEnergyFraction"] for r in cases)],
        "floorCertified": False}, indent=2))


if __name__ == "__main__":
    main()

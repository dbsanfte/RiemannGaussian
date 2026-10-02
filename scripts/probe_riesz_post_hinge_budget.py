#!/usr/bin/env python3
"""Optional joined-prefix energy and profile-price diagnostic.

The native rational radius, exact integer moving cutoff, full phases and
finite divisor columns are retained. Test orders4/5 have exactly empty
allocation support. Native count56+, physical, dyadic and funded supply
hypotheses are NOT certified. These floating finite results do not prove
the remaining energy budget or any eventual floor. Outside ordinary CI.
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
    radius = Fraction(10001, 20000)
    cutoff = radius.denominator ** order // (radius.numerator ** order * (order + 1))
    length = 2 * math.log(cutoff + 2)
    assert not any(32 * k <= 13 * order and 5 * (order + 1 - k) < 4 * order
                   for k in range(order + 2))
    first = math.floor(math.exp(39 * order / 20)) + 1
    last = math.floor(math.exp(203 * order / 100))
    spf = prime_table(last)
    mu = np.ones(last + 1, dtype=np.int8)
    counts = np.zeros(last + 1, dtype=np.int16)
    largest = np.ones(last + 1, dtype=np.int64)
    for n in range(2, last + 1):
        p, a = int(spf[n]), n // int(spf[n])
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
    cutoffs = np.arange(1, endpoint)
    columns = np.cumsum(increments, axis=0, dtype=np.int16)[cutoffs].astype(float)
    logk, lognext = np.log(cutoffs), np.log(cutoffs + 1)
    logstep = lognext - logk
    delta = np.maximum(length, logk) - np.maximum(length, lognext)
    full_profile = float(np.sum(cutoffs * delta ** 2))
    width = max(0, math.log(endpoint) - length)
    assert np.all(delta <= 0)
    assert full_profile <= width + 1e-12
    assert np.all(cutoffs * delta ** 2 <= -delta + 1e-12)
    # A free null-profile correction gives zero endpoint sum. Test the
    # common-prefix projection before building any new proof mechanism.
    slope = length / math.log(endpoint)
    corrected_delta = (np.maximum(0, length - logk) -
                       np.maximum(0, length - lognext) - slope * logstep)
    harmonic = float(np.sum(1 / cutoffs))
    logs = np.log(selected)
    common = (-float(radius) ** (order + 1) / (length * math.factorial(order)) *
              np.exp(-1.5 * logs) * logs ** (order + 1))
    cases = []
    for height in heights:
        weights = common * np.cos(height * logs)
        correlation = columns @ weights
        adverse = correlation * delta < 0
        energy = float(np.sum(correlation[adverse] ** 2 / cutoffs[adverse]))
        profile = float(np.sum(cutoffs[adverse] * delta[adverse] ** 2))
        signed = float(np.sum(correlation * delta))
        assert profile <= full_profile + 1e-12
        assert -math.sqrt(energy * profile) <= signed + 1e-12
        assert abs(float(np.sum(correlation * logstep))) < 1e-12
        assert abs(float(np.sum(correlation * corrected_delta)) - signed) < 1e-12
        mean = float(np.sum(correlation / cutoffs)) / harmonic
        raw = float(np.sum(correlation ** 2 / cutoffs))
        variance = float(np.sum((correlation - mean) ** 2 / cutoffs))
        projection_price = float(np.sum(cutoffs * corrected_delta ** 2))
        cases.append({
            "order": order, "height": height, "labels": int(selected.size),
            "nativeIntegerCutoff": cutoff, "nativeLength": length,
            "fullProfileEnergy": full_profile, "postHingeWidth": width,
            "adverseProfileEnergy": profile, "joinedAdverseEnergy": energy,
            "joinedSignedValue": signed, "originalAdverseCost": math.sqrt(energy * profile),
            "calibratedSmallOrderWidthCost": math.sqrt(energy * width),
            "commonMeanVarianceRatio": variance / raw,
            "commonMeanProjectedCost": math.sqrt(variance * projection_price),
            "explicit65536ThresholdApplicable": False,
        })
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="+", default=[4, 5])
    parser.add_argument("--heights", type=float, nargs="+", default=[54, 65, 100])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if any(n not in (4, 5) for n in args.orders):
        parser.error("the complete finite empty-allocation diagnostic supports orders4/5")
    if any(not math.isfinite(y) or y < 54 for y in args.heights):
        parser.error("heights must be finite and >=54")
    cases = [c for n in args.orders for c in experiment(n, args.heights)]
    report = {
        "scope": "Finite joined-prefix profile and common-mean projection diagnostics.",
        "nativeMovingLengthUsed": True, "exactRationalIntegerFloorUsed": True,
        "allocationSupportExactlyEmpty": True, "nativeCount56PlusManyBinPopulationCertified": False,
        "nativePhysicalMasksCertified": False, "nativeDyadicScheduleCertified": False,
        "nativeFundingWitnessCertified": False, "floatingResultsIntervalCertified": False,
        "remainingEnergyBoundProved": False, "floorProved": False, "cases": cases,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": len(cases), "profileWidthChecksPassed": True,
                      "commonMeanVarianceRatioRange": [
                          min(c["commonMeanVarianceRatio"] for c in cases),
                          max(c["commonMeanVarianceRatio"] for c in cases)],
                      "remainingEnergyBoundProved": False, "floorProved": False}, indent=2))


if __name__ == "__main__":
    main()

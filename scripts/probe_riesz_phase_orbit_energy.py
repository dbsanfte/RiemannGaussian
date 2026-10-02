#!/usr/bin/env python3
"""Optional actual-integer phase-period cross-energy diagnostic.

The rational radius, integer moving cutoff, full total-label phase and
actual divisor Gram columns are retained. Allocation is exactly empty at
orders4/5. These orders do not certify native physical/many-bin/dyadic or
funded-supply conditions. The native near-label strip includes all tested
pairs; a separate 1/1000 distance strip is explicitly diagnostic only.
No finite floating result proves an eventual energy budget or floor.
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
    cutoff = radius.denominator**order // (radius.numerator**order * (order + 1))
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
        prime, rest = int(spf[n]), n // int(spf[n])
        mu[n] = 0 if rest % prime == 0 else -mu[rest]
        counts[n] = counts[rest] + int(rest % prime != 0)
        largest[n] = max(largest[rest], prime)
    labels = np.arange(first, last + 1)
    selected = labels[(mu[labels] != 0) & (counts[labels] >= 3) &
                      (np.log(largest[labels]) < (60069 / 100000) * np.log(labels))]
    endpoint = int(selected.max())
    increments = np.zeros((endpoint + 1, selected.size), dtype=np.int16)
    tau = np.zeros(selected.size)
    for i, n in enumerate(selected):
        ds = divisors(int(n), spf)
        tau[i] = len(ds)
        for d in ds:
            increments[d, i] = mu[d]
    cutoffs = np.arange(1, endpoint)
    columns = np.cumsum(increments, axis=0, dtype=np.int16)[cutoffs].astype(float)
    steps = np.maximum(length, np.log(cutoffs)) - np.maximum(length, np.log(cutoffs + 1))
    logs = np.log(selected)
    log_gap = logs[:, None] - logs[None, :]
    gcd = np.gcd(selected[:, None], selected[None, :])
    distinct = ~np.eye(selected.size, dtype=bool)
    small_gcd = np.log(gcd) <= order / 1000
    relative_distance = np.abs(selected[:, None] - selected[None, :]) / np.minimum(
        selected[:, None], selected[None, :])
    native_separated = distinct & small_gcd & (relative_distance > math.exp(-order / 1000))
    diagnostic_separated = distinct & small_gcd & (relative_distance > 1 / 1000)
    source_amplitude = (-float(radius)**(order + 1) /
                        (length * math.factorial(order)) *
                        np.exp(-1.5 * logs) * logs**(order + 1))
    pair_mass = (tau / selected)[:, None] * (tau / selected)[None, :]
    divisor_harmonic = float(np.sum(tau**2 / selected))
    cases = []
    for height in heights:
        weights = source_amplitude * np.cos(height * logs)
        prefix = columns @ weights
        adverse = prefix * steps < 0
        gram = columns[adverse].T @ (columns[adverse] / cutoffs[adverse, None])
        cross = gram * weights[:, None] * weights[None, :]
        width = math.exp(-order / 1000) / (1 + abs(height))
        periods = np.rint(height * log_gap / (2 * math.pi)).astype(np.int64)
        maximum_period = 4 * (math.ceil(abs(height)) + 1) * (order + 1)
        orbit = np.abs(log_gap - 2 * math.pi * periods / height) <= width
        assert np.all(np.abs(periods) <= maximum_period)
        # Test the proved reciprocal-capacity mechanism on literal integers.
        capacity = (2 * maximum_period + 1) * (4 * width + math.exp(-7 * order / 4))
        row_mass = orbit @ (1 / selected)
        assert float(np.max(row_mass)) <= capacity + 1e-12
        mass = float(np.sum(pair_mass[orbit]))
        assert mass <= capacity * divisor_harmonic + 1e-12
        total = float(np.sum(cross[distinct]))
        paid = float(np.sum(cross[distinct & orbit]))
        remaining = float(np.sum(cross[distinct & ~orbit]))
        assert abs(total - paid - remaining) < 1e-12
        native = float(np.sum(cross[native_separated]))
        native_orbit = float(np.sum(cross[native_separated & orbit]))
        native_rest = float(np.sum(cross[native_separated & ~orbit]))
        diagnostic = float(np.sum(cross[diagnostic_separated]))
        diagnostic_orbit = float(np.sum(cross[diagnostic_separated & orbit]))
        diagnostic_rest = float(np.sum(cross[diagnostic_separated & ~orbit]))
        assert abs(diagnostic - diagnostic_orbit - diagnostic_rest) < 1e-12
        profile = float(np.sum(cutoffs[adverse] * steps[adverse]**2))
        cases.append({
            "order": order, "height": height, "labels": int(selected.size),
            "countsPresent": [int(x) for x in np.unique(counts[selected])],
            "movingIntegerCutoff": cutoff, "movingLength": length,
            "allocationSupportExactlyEmpty": True,
            "actualJoinedSignedValue": float(np.sum(prefix * steps)),
            "originalAdverseProfile": profile,
            "phaseWidthLog": width, "finitePhaseIndexRadius": maximum_period,
            "actualPhaseBandPairMass": mass,
            "reciprocalCapacityUpperBound": capacity * divisor_harmonic,
            "allCrossEnergy": total, "allPhaseBandCrossEnergy": paid,
            "allOutsideBandCrossEnergy": remaining,
            "nativeSeparatedEnergy": native,
            "nativeSeparatedPhaseBandEnergy": native_orbit,
            "nativeSeparatedOutsideBandEnergy": native_rest,
            "nativeNearStripIncludesAllTestPairs": not bool(np.any(native_separated)),
            "diagnosticRelativeDistanceThreshold": 1 / 1000,
            "diagnosticSeparatedEnergy": diagnostic,
            "diagnosticPhaseBandEnergy": diagnostic_orbit,
            "diagnosticOutsideBandEnergy": diagnostic_rest,
            "diagnosticFormerCost": math.sqrt(max(diagnostic, 0) * profile),
            "diagnosticRemainingCost": math.sqrt(max(diagnostic_rest, 0) * profile),
        })
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="+", default=[4, 5])
    parser.add_argument("--heights", type=float, nargs="+", default=[54, 65, 100])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if any(n not in (4, 5) for n in args.orders):
        parser.error("this complete empty-allocation diagnostic supports orders4/5")
    if any(not math.isfinite(y) or y < 54 for y in args.heights):
        parser.error("heights must be finite and >=54")
    cases = [case for n in args.orders for case in experiment(n, args.heights)]
    report = {
        "scope": "Finite actual-integer all-count phase-band correlation diagnostic.",
        "nativeMovingLengthUsed": True, "exactRationalIntegerFloorUsed": True,
        "originalPhaseAndDivisorColumnsRetained": True,
        "nativePhysicalMasksCertified": False, "nativeFundingWitnessCertified": False,
        "nativeCount56PlusManyBinPopulationCertified": False,
        "nativeDyadicScheduleCertified": False, "intervalArithmeticCertified": False,
        "unpaidOutsideBandEnergyBoundProved": False, "floorProved": False,
        "cases": cases,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "cases": len(cases), "reciprocalCapacityChecksPassed": True,
        "exactSignedPartitionsChecked": True,
        "negativeDiagnosticPhaseBandCases": sum(c["diagnosticPhaseBandEnergy"] < 0 for c in cases),
        "diagnosticCostIncreasedCases": sum(c["diagnosticRemainingCost"] >
                                             c["diagnosticFormerCost"] for c in cases),
        "floorProved": False,
    }, indent=2))


if __name__ == "__main__":
    main()

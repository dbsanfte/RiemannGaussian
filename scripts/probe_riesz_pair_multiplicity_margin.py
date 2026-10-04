#!/usr/bin/env python3
"""Source-side multiplicity regression, not an arithmetic floor estimate.

Retain the original factorial slots, exact integer cutoff and stated
moving-length floor error. No prime/zeta data or unknown source mass is
sampled. The Lean endpoint retains the arithmetic bound as an open premise.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp

from probe_riesz_selberg_renewal import moving_length


def number(value):
    return mp.nstr(value, 35)


def retained(u):
    return mp.log(mp.mpf(32) / 13) / (-2 * u * mp.log(u)) - mp.log(mp.mpf(19) / 13)


def selected_evaluation(order, multiplicity, u, length):
    cutoff = 13 * order // 32
    harmonic = lambda k: mp.digamma(k + 1) + mp.euler
    return multiplicity**2 * (
        1 + harmonic(order - cutoff) - harmonic(cutoff)
        - (order + 1) / (u * length) * (harmonic(order + 1) - harmonic(cutoff)))


def original_slots(order, multiplicity, u, length):
    cutoff = 13 * order // 32
    m = order + 1
    return {
        "central": m * multiplicity**2 / 2 * mp.fsum(
            1 / (mp.mpf(k) * (m - k)) for k in range(cutoff + 1, m - cutoff)),
        "successor": -m * (m + 1) * multiplicity**2 / (2 * u * length) * mp.fsum(
            1 / (mp.mpf(k) * (m + 1 - k)) for k in range(cutoff + 1, m + 1 - cutoff)),
        "loggedPrefix": -m * multiplicity**2 / (u * length) * mp.fsum(
            1 / mp.mpf(m + 1 - k) for k in range(1, cutoff + 1)),
        "fullTrace": mp.mpf(multiplicity**2),
    }


def probe():
    mp.mp.dps = 100
    target = mp.mpf(399) / 5000
    ceiling = mp.mpf(10001) / 20000
    limit_rows = []
    for u in [mp.mpf("0.5"), mp.mpf("0.500001"), ceiling]:
        cost = retained(u)
        for multiplicity in range(1, 9):
            pair_source = multiplicity**2 * (1 - cost)
            joint_source = -multiplicity + multiplicity**2 * cost
            identity_error = abs(pair_source + joint_source - (multiplicity**2 - multiplicity))
            assert identity_error < mp.mpf("1e-90")
            assert pair_source > target
            assert pair_source >= 1 - cost
            limit_rows.append({
                "u": number(u), "multiplicity": multiplicity,
                "selectedPairSource": number(pair_source),
                "olderJointSource": number(joint_source),
                "pairSourceAboveUnchangedTarget": number(pair_source - target),
                "sourceLedgerIdentityError": number(identity_error),
            })
    regression_rows = []
    for order in [32, 96, 256]:
        length, _, method = moving_length(order, ceiling)
        for multiplicity in [1, 2, 3, 8]:
            slots = original_slots(order, multiplicity, ceiling, length)
            value = selected_evaluation(order, multiplicity, ceiling, length)
            regression_error = abs(mp.fsum(slots.values()) - value)
            assert regression_error < mp.mpf("1e-90")
            regression_rows.append({
                "N": order, "multiplicity": multiplicity,
                "originalSlots": {key: number(term) for key, term in slots.items()},
                "collectedSelectedEvaluation": number(value),
                "slotCollectionError": number(regression_error),
                "movingLengthMethod": method,
            })
    finite_rows = []
    for order in [65536, 131072, 425984, 1048576]:
        length, floor_error, method = moving_length(order, ceiling)
        cutoff = 13 * order // 32
        prefix_mass = mp.digamma(order + 2) - mp.digamma(cutoff + 1)
        for multiplicity in [1, 2, 3, 8]:
            value = selected_evaluation(order, multiplicity, ceiling, length)
            length_change = multiplicity**2 * (order + 1) / ceiling * prefix_mass * floor_error / length**2
            finite_rows.append({
                "N": order, "multiplicity": multiplicity,
                "pureSelectedEvaluationOnly": number(value),
                "aboveTargetInThisPureSourceSample": value > target,
                "movingLengthMethod": method,
                "lengthFloorErrorBound": number(floor_error),
                "evaluationFloorErrorBoundExcludingRoundoff": number(length_change),
                "literalPrimeCarrierSampled": False,
            })
    return {
        "classification": "source-side scalar and factorial-index regression",
        "precisionDigits": 100, "primeOrZetaSamples": 0,
        "arithmeticUpperBoundProved": False, "newZeroExclusion": False,
        "firstCrossingOrEntryOrderCertified": False,
        "targetUnchanged": "399/5000", "limitRows": limit_rows,
        "originalSlotRegressions": regression_rows, "finitePureSourceRows": finite_rows,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = probe()
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"sourceLimitRows": len(result["limitRows"]),
                      "originalSlotChecks": len(result["originalSlotRegressions"]),
                      "primeOrZetaSamples": 0, "arithmeticBoundProved": False}))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Optional algebraic regression of the joined source-error price.

Finite synthetic errors, not prime data. Match exact factorial indices
BEFORE joining signed slots; include swapped trace incidences. No unknown
height-dependent source mass is assigned a numerical value for arithmetic.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp

from probe_riesz_selberg_renewal import moving_length


def number(value):
    return mp.nstr(value, 35)


def complex_number(value):
    return {"re": number(mp.re(value)), "im": number(mp.im(value))}


def direct_difference(errors, multiplicity, order, length, u):
    """Four original slots, including the two swapped trace endpoints."""
    cutoff = 13 * order // 32
    m = order + 1

    def value(k):
        return -multiplicity + (errors[k] if k < len(errors) else 0)

    def product_error(i, j):
        return value(i) * value(j) - multiplicity**2

    return {
        "central": m / 2 * mp.fsum(
            product_error(k - 1, m - k - 1) / (k * (m - k))
            for k in range(cutoff + 1, m - cutoff)),
        "successor": -m * (m + 1) / (2 * u * length) * mp.fsum(
            product_error(k - 1, m - k) / (k * (m + 1 - k))
            for k in range(cutoff + 1, m + 1 - cutoff)),
        "loggedPrefix": -m / (u * length) * mp.fsum(
            product_error(k - 1, m - k) / (m + 1 - k)
            for k in range(1, cutoff + 1)),
        "fullTrace": mp.fsum(
            product_error(k, order - 1 - k) for k in range(order)) / order,
    }


def probe():
    mp.mp.dps = 100
    u = mp.mpf(10001) / 20000
    head = 64
    specifications = [
        ("real-positive", 1, mp.mpc("0.25"), mp.mpc("0.75")),
        ("real-negative", 1, mp.mpc("-0.25"), mp.mpc("0.75")),
        ("complex-common-phase", 1, mp.mpc("0.2", "0.1"),
         mp.mpf("0.9") * mp.exp(mp.j / 7)),
        ("multiple-source", 3, mp.mpc("0.25"), mp.mpc("0.75")),
    ]
    rows = []
    for name, multiplicity, coefficient, ratio in specifications:
        errors = [coefficient * ratio**k for k in range(head)]
        error_mass = mp.fsum(abs(value) for value in errors)
        for order in [256, 640, 65536, 131072, 1048576]:
            cutoff = 13 * order // 32
            assert head < cutoff and 2 * head < order
            length, floor_error, method = moving_length(order, u)
            factor = (order + 1) / (u * length)
            # Sum the matching products first. The correlated high leg
            # is exactly constant here, and the central errors are zero.
            trace = -2 * multiplicity * mp.fsum(errors) / order
            prefix = multiplicity * factor * mp.fsum(
                errors[k] / (order + 1 - k) for k in range(head))
            difference = trace + prefix
            price = 22 * (multiplicity + error_mass) * error_mass / order
            assert abs(difference) <= price
            direct_error = None
            slots = None
            if order <= 640:
                slots = direct_difference(errors, multiplicity, order, length, u)
                direct_error = abs(mp.fsum(slots.values()) - difference)
                assert direct_error < mp.mpf("1e-90")
            # The only large-N approximation is the already-stated
            # moving-length floor error, not an allocation/phase limit.
            length_error_cost = (multiplicity * (order + 1) / u
                                 * mp.fsum(abs(errors[k]) / (order + 1 - k)
                                           for k in range(head))
                                 * floor_error / length**2)
            asymptotic_linear = multiplicity * (
                1 / (-2 * u * mp.log(u)) - 2) * mp.fsum(errors)
            rows.append({
                "syntheticArray": name, "multiplicity": multiplicity,
                "N": order, "formalOrderRange": order >= 65536,
                "exactSyntheticErrorMass": number(error_mass),
                "signedTraceError": complex_number(trace),
                "signedPrefixError": complex_number(prefix),
                "joinedError": complex_number(difference),
                "wholeSourceErrorPrice": number(price),
                "observedErrorOverPrice": number(abs(difference) / price),
                "NtimesJoinedError": complex_number(order * difference),
                "predictedSignedInverseOrderCoefficient": complex_number(asymptotic_linear),
                "originalSlots": None if slots is None else
                    {key: complex_number(value) for key, value in slots.items()},
                "exactIndexCollectionError": None if direct_error is None else number(direct_error),
                "movingLengthMethod": method,
                "lengthFloorErrorBound": number(floor_error),
                "joinedErrorLengthChangeBoundExcludingRoundoff": number(length_error_cost),
            })
    return {
        "classification": "synthetic finite-error algebra regression",
        "precisionDigits": 100, "primeOrZetaSamples": 0,
        "lowOrdersZeroAndOneRetained": True,
        "swappedTraceIncidencesRetained": True,
        "quadraticLowLowTermsOmittedByIndexEquality": True,
        "sourcePoleNormPaid": False,
        "actualSourceErrorMassNumericallyCertified": False,
        "independentFloorSaving": False,
        "floorTarget": "399/5000", "rows": rows,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = probe()
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"rows": len(result["rows"]), "primeOrZetaSamples": 0,
                      "exactIndexRegressions": 8, "floorSaving": False}))


if __name__ == "__main__":
    main()

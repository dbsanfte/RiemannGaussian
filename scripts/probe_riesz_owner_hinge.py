#!/usr/bin/env python3
"""Optional actual-integer regression for the complete owner-hinge scalar.

Checks the exact scalar's recurrence, its common-reference error, and its
joint owner-prefix price. The signed owner amplitudes in that last check
are diagnostic inputs, NOT moments measured from the masked carrier.
It evaluates no cofactor mask/phase carrier and certifies no floor or decay.
The finite Euler density and omitted-tail enclosure are diagnostics only.
"""

import argparse
import json
import math
from pathlib import Path

from probe_riesz_signed_density import coefficients, prime_table


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=50000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.limit < 2048:
        parser.error("limit must be at least 2048")
    spf = prime_table(args.limit)
    primes = [n for n in range(2, args.limit + 1) if spf[n] == n]
    density_upper = math.prod(1 - 1 / (p * p) for p in primes)
    density_lower = density_upper * (1 - 1 / args.limit)
    assert 0 < density_lower <= density_upper < 1
    unexcluded = coefficients(args.limit, set(), spf)

    def riesz(values, cutoff):
        if cutoff <= 0:
            return 0.0
        last = min(args.limit, int(math.floor(math.exp(cutoff) + 1e-8)))
        return sum(values[n] * max(0.0, cutoff - math.log(n))
                   for n in range(1, last + 1))

    rows = []
    for p in (2, 3, 23, 101, 1009):
        excluded = coefficients(args.limit, {p}, spf)
        for cut in (128, 2048, args.limit):
            c = math.log(cut)
            full = riesz(unexcluded, c)
            owner = riesz(excluded, c)
            shifted = riesz(excluded, c - math.log(p))
            recurrence_error = abs(owner - full - shifted / (p + 1))
            assert recurrence_error < 1e-10
            source_scalar_abs_upper = density_upper * abs(owner)
            constant = 7 * (p + 1) / p
            assert source_scalar_abs_upper <= constant
            old_height_bound = density_upper * c
            rows.append({"ownerPrime": p, "physicalCutoff": cut,
                         "hingeHeight": c, "normalizedSignedScalar": owner,
                         "scalarAbsoluteUpper": source_scalar_abs_upper,
                         "provedConstantAllowance": constant,
                         "previousLinearAllowance": old_height_bound,
                         "recurrenceFloatingError": recurrence_error})

    joint_rows = []
    configurations = [([101, 103], [1.0, -1.0]),
                      ([1009, 1013, 1019, 1021], [1.0, -1.0, 1.0, -1.0]),
                      ([1009, 1013, 1019, 1021], [1.0, -1.0, 1.0, -0.99]),
                      ([101, 103], [1.0, 1.0])]
    if args.limit >= 10009:
        configurations.append(([10007, 10009], [1.0, -1.0]))
    for owners, values in configurations:
        assert all(p <= args.limit and spf[p] == p for p in owners)
        L = math.log(args.limit) + math.log(owners[0])
        signed_value, common_errors = 0.0, []
        for p, value in zip(owners, values):
            c = L - math.log(p)
            owner = density_upper * riesz(coefficients(args.limit, {p}, spf), c)
            common = density_upper * riesz(unexcluded, c)
            common_error = abs(owner - common)
            assert common_error <= 7 / p + 1e-10
            common_errors.append(common_error)
            signed_value += owner * value
        prefix, prefix_cost = 0.0, 0.0
        for index in range(len(owners) - 1):
            prefix += values[index]
            prefix_cost += math.log(owners[index + 1] / owners[index]) * abs(prefix)
        joint_allowance = (7 * abs(sum(values)) + density_upper * prefix_cost +
                           7 * sum(abs(v) / p for p, v in zip(owners, values)))
        common_endpoint = density_upper * riesz(unexcluded, L - math.log(owners[-1]))
        centered_allowance = joint_allowance - 7 * abs(sum(values))
        centered_error = abs(signed_value - common_endpoint * sum(values))
        assert centered_error <= centered_allowance + 1e-10
        former_allowance = 7 * sum((p + 1) / p * abs(v)
                                   for p, v in zip(owners, values))
        assert abs(signed_value) <= joint_allowance + 1e-10
        joint_rows.append({"ownerPrimes": owners, "chosenSignedOwnerAmplitudes": values,
                           "actualCarrierMomentsMeasured": False,
                           "signedScalarAggregate": signed_value,
                           "commonReferenceErrors": common_errors,
                           "jointOwnerPrefixAllowance": joint_allowance,
                           "commonEndpointMomentRetainedSigned": common_endpoint * sum(values),
                           "centeredOwnerError": centered_error,
                           "centeredOwnerAllowance": centered_allowance,
                           "formerSeparateOwnerAllowance": former_allowance,
                           "jointToFormerAllowanceRatio": joint_allowance / former_allowance})
    report = {"scope": "Actual-integer complete owner-reference scalar only.",
              "limit": args.limit,
              "densityEnclosure": {"lower": density_lower, "upper": density_upper,
                                   "rigorousIntervalArithmetic": False},
              "cases": rows, "jointOwnerPrefixCases": joint_rows,
              "maskedCarrierBoundCertified": False,
              "sourceScaleDecayCertified": False, "floorCertified": False}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": len(rows), "cutoff": args.limit,
                      "largestRecurrenceFloatingError": max(
                          r["recurrenceFloatingError"] for r in rows),
                      "jointOwnerPrefixCases": len(joint_rows),
                      "leastJointToFormerAllowanceRatio": min(
                          r["jointToFormerAllowanceRatio"] for r in joint_rows),
                      "scalarAbsoluteUpperMaximum": max(
                          r["scalarAbsoluteUpper"] for r in rows),
                      "floorCertified": False}, indent=2))


if __name__ == "__main__":
    main()

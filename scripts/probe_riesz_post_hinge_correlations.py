#!/usr/bin/env python3
"""Optional actual-integer audit of post-hinge sharp-prefix correlations.

This uses the SAME total-label phase and finite divisor prefixes, summing
labels before squaring. Orders 4..6 and L=11N/8 are diagnostics, not the
native unpaid count-56+ support, physical prime masks or funding witness.
Neither the covariance ratios nor the small common-cofactor example are
a source-scale cancellation certificate. Deliberately outside ordinary CI.
"""

import argparse
import json
import math
from pathlib import Path

import numpy as np

from probe_riesz_signed_density import prime_table


def divisors(n, spf):
    result = [1]
    while n > 1:
        p = int(spf[n])
        power = 1
        old = list(result)
        while n % p == 0:
            n //= p
            power *= p
            result.extend(d * power for d in old)
    return sorted(result)


def experiment(order, heights):
    length, radius = 11 * order / 8, 10001 / 20000
    assert not any(32 * k <= 13 * order and 5 * (order + 1 - k) < 4 * order
                   for k in range(order + 2))
    first = math.floor(math.exp(39 * order / 20)) + 1
    last = math.floor(math.exp(203 * order / 100))
    spf = prime_table(last)
    mu = np.ones(last + 1)
    count = np.zeros(last + 1, dtype=np.int64)
    largest = np.ones(last + 1, dtype=np.int64)
    for n in range(2, last + 1):
        p, a = int(spf[n]), n // int(spf[n])
        mu[n] = 0 if a % p == 0 else -mu[a]
        count[n] = count[a] + int(a % p != 0)
        largest[n] = max(largest[a], p)
    labels = np.arange(1, last + 1)
    logs = np.log(labels)
    support = ((labels >= first) & (mu[1:] != 0) & (count[1:] >= 3) &
               (np.log(largest[1:]) < (60069 / 100000) * logs))
    selected = labels[support]
    endpoint = int(selected.max())
    cutoffs = np.arange(math.floor(math.exp(length)), endpoint)
    harmonic = np.concatenate(([0.0], np.cumsum(1 / np.arange(1, endpoint + 1))))

    # A column is constant between successive ACTUAL integer divisors.
    # This computes its diagonal energy exactly up to floating summation,
    # including the moving partial first interval of the corrected profile.
    column_energies = []
    for n in selected:
        ds = divisors(int(n), spf)
        value, energy = 0, 0.0
        for d, following in zip(ds, ds[1:] + [endpoint + 1]):
            value += int(mu[d])
            start = max(d, int(cutoffs[0]))
            stop = min(following - 1, endpoint - 1)
            if start <= stop:
                energy += value ** 2 * (harmonic[stop] - harmonic[start - 1])
        column_energies.append(energy)
    column_energies = np.asarray(column_energies)

    results = []
    for height in heights:
        weights = np.zeros(last + 1)
        weights[1:] = (support * (-radius ** (order + 1) /
                                  (length * math.factorial(order))) *
                       np.exp(-1.5 * logs) * logs ** (order + 1) *
                       np.cos(height * logs))
        increments = np.zeros(last + 1)
        for d in range(1, last + 1):
            if mu[d]:
                increments[d] = mu[d] * float(np.sum(weights[d::d]))
        prefix = np.cumsum(increments)[cutoffs]
        joint = float(np.sum(prefix ** 2 / cutoffs))
        diagonal = float(np.sum(weights[selected] ** 2 * column_energies))
        signed_cross = joint - diagonal
        assert diagonal > 0 and joint >= 0
        results.append({
            "order": order, "height": height, "labelCount": len(selected),
            "exactAllocationSupportEmpty": True,
            "testLength": length, "firstPostHingeCutoff": int(cutoffs[0]),
            "jointPhaseEnergy": joint, "diagonalLabelEnergy": diagonal,
            "signedOffDiagonalEnergy": signed_cross,
            "jointToDiagonal": joint / diagonal,
            "weightedCrossCancellationPresent": signed_cross < 0,
        })
    return results


def owner_cell():
    a, cutoff, height, order = 210, 5500, 54, 6
    owners = (907, 911)
    spf = prime_table(max(a, *owners))
    assert all(int(spf[p]) == p and a % p != 0 for p in owners)
    ds = divisors(a, spf)
    mu = {d: (-1) ** sum(1 for p in (2, 3, 5, 7) if d % p == 0) for d in ds}

    def sharp(k):
        return sum(mu[d] for d in ds if d <= k)

    length = 11 * order / 8
    rows = []
    for p in owners:
        n = p * a
        response = sum(mu[d] * (max(0, length - math.log(d)) -
                               max(0, length - math.log(p * d))) for d in ds)
        rows.append({
            "owner": p, "label": n, "cofactor": a,
            "quotientCutoff": cutoff // p,
            "literalSharpPrefix": sharp(cutoff) - sharp(cutoff // p),
            "ownerShare": math.log(p) / math.log(n),
            "totalLogOverOrder": math.log(n) / order,
            "originalRiesz": response, "phaseCosine": math.cos(height * math.log(n)),
        })
    assert all(row["literalSharpPrefix"] == 1 for row in rows)
    assert all(1.95 < row["totalLogOverOrder"] <= 2.03 for row in rows)
    assert all(row["ownerShare"] < 60069 / 100000 for row in rows)
    assert all(row["phaseCosine"] < 0 for row in rows)
    return {
        "rows": rows, "testLength": length, "cutoff": cutoff,
        "postHinge": length < math.log(cutoff),
        "fullPhaseSeparation": height * math.log(owners[1] / owners[0]),
        "rawSharpJointToDiagonal": 2,
        "manyBinHypothesisVerified": False,
        "nativePhysicalMasksVerified": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="+", default=[4, 5, 6])
    parser.add_argument("--heights", type=float, nargs="+", default=[54, 65, 100])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if any(n not in (4, 5, 6) for n in args.orders):
        parser.error("the empty-allocation regression supports orders 4..6")
    if any(not math.isfinite(y) or y < 54 for y in args.heights):
        parser.error("heights must be finite and >=54")
    cases = [case for n in args.orders for case in experiment(n, args.heights)]
    report = {
        "scope": "Actual-integer post-hinge cross-label correlation diagnostics.",
        "literalUnpaidCount56SupportUsed": False, "nativeMovingLengthUsed": False,
        "nativePhysicalPrimeMasksUsed": False, "fundingWitnessIncluded": False,
        "rigorousIntervalArithmetic": False, "sourceScaleSavingCertified": False,
        "floorCertified": False, "ownerCell": owner_cell(), "cases": cases,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": len(cases), "jointToDiagonalRange": [
        min(c["jointToDiagonal"] for c in cases),
        max(c["jointToDiagonal"] for c in cases)],
        "casesWithNegativeCrossTerms": sum(c["weightedCrossCancellationPresent"] for c in cases),
        "sourceScaleSavingCertified": False, "floorCertified": False}, indent=2))


if __name__ == "__main__":
    main()

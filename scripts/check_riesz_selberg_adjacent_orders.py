#!/usr/bin/env python3
"""Independent 420-bit replay of the fixed-mask adjacent-order controls.

Recomputes the divisor response and factorial prefixes via binomial
weights, rather than importing the producer's prime-leg convolution.
Ball overlap and relative enclosure widths are both required. These
controls do not enumerate the native core or sample hypothetical zeros.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path

from flint import acb, arb, ctx, fmpz


def load_ball(row: dict) -> arb:
    mid, rad = row["mid"], row["rad"]
    return (arb(int(mid[0]))*arb(2)**int(mid[1])
            + arb(0, int(rad[0]))*arb(2)**int(rad[1]))


def compare_real(row: dict, expected: arb, scale: arb | None = None) -> None:
    stored = load_ball(row)
    assert stored.overlaps(expected), (stored, expected)
    if scale is None:
        scale = abs(expected)
    if scale == 0:
        assert stored == expected == 0
        return
    assert scale > 0
    assert stored.rad() < scale*arb(2)**(-280)
    assert expected.rad() < scale*arb(2)**(-330)


def compare_complex(row: dict, expected: acb) -> None:
    scale = abs(expected)
    compare_real(row["re"], expected.real, scale)
    compare_real(row["im"], expected.imag, scale)


def moving_length(u: Fraction, n: int) -> tuple[arb, int]:
    # Exact rational floor, including the successor correction in L_N.
    inverse = (1/u)**n/(n+1)
    cutoff = inverse.numerator//inverse.denominator
    return 2*arb(cutoff+2).log(), cutoff.bit_length()


def lower_binomial(n: int, cutoff: int, q: arb) -> arb:
    return sum((arb(math.comb(n, k))*q**k*(1-q)**(n-k)
                for k in range(cutoff+1)), arb(0))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/riesz-selberg-adjacent-order/numeric-replay.json"))
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    ctx.prec = 420
    assert data["schemaVersion"] == 1 and data["precisionBits"] == 360
    assert len(data["rows"]) == data["actualPrimeAtomRows"] == 216
    assert len(data["scalars"]) == data["scalarGeometryRows"] == 4
    assert data["nativeCoreEnumerated"] is False and data["actualZeroSamples"] == 0
    assert data["nativeEntryOrderCertified"] is False and data["newGlobalCeilingCredit"] == 0
    comparisons = 0
    for row in data["rows"]:
        n, p, q, y = row["N"], int(row["p"]), int(row["q"]), row["height"]
        uf = Fraction(row["u"])
        u = arb(uf.numerator)/uf.denominator
        assert fmpz(p).is_prime() and fmpz(q).is_prime() and p < q
        x, z = arb(p).log(), arb(q).log()
        total = x+z
        assert n < x < n+1 < z < n+2
        assert row["balancedMaskAtN"] is True and row["balancedMaskAtNPlusOne"] is False
        assert not (n+1 < x <= n+2)
        assert row["nativeTheoremThresholdMet"] is False and n < 65536
        length, bits = moving_length(uf, n)
        assert bits == row["cutoffBits"] and max(x, z) < length < total

        # Independently enumerate all four squarefree divisors, preserving signs.
        response = arb(0)
        for d, mu in ((1, 1), (p, -1), (q, -1), (p*q, 1)):
            hinge = length-arb(d).log()
            response += mu*(hinge if hinge > 0 else arb(0))
        defect = -total*response/length+2*x*z/total
        # Separate prime phases, rather than the producer's total-log exponential.
        phase = acb(-arb(3)*x/2, -y*x).exp()*acb(-arb(3)*z/2, -y*z).exp()
        kernels = {k: phase*total**k/arb(math.factorial(k))
                   for k in (n-1, n, n+1, n+2)}
        first = arb(3)*(n+1)/2*kernels[n+1]
        second = -(n+1)*(n+2)/length*kernels[n+2]
        imbalance = -(x-z)**2/(2*n)*kernels[n-1]
        joined = first+second+imbalance
        raw = defect*kernels[n]
        assert (raw-joined).contains(0)
        cutoff = 13*n//32
        qx = lower_binomial(n+1, cutoff, x/total)
        qz = lower_binomial(n+1, cutoff, z/total)
        prefix_coefficient = total/length*((length-x)*qz+(length-z)*qx)
        prefix = prefix_coefficient*kernels[n]
        literal = (defect-prefix_coefficient)*kernels[n]
        assert (literal-(joined-prefix)).contains(0)
        swapped_defect = -total*response/length+2*z*x/total
        assert (raw-swapped_defect*kernels[n]).contains(0)
        values = {"rawDefect": raw, "orderPlusOne": first,
                  "orderPlusTwo": second, "imbalanceOrderMinusOne": imbalance,
                  "joinedOrders": joined, "factorialPrefix": prefix,
                  "literalPrefixDefect": literal}
        assert set(values) == set(row["values"])
        for name, expected in values.items():
            compare_complex(row["values"][name], u**(n+1)*expected)
            comparisons += 2
        compare_real(row["retainedCoefficientFraction"], defect/(arb(3)*total/2))
        comparisons += 1

    for row in data["scalars"]:
        n, uf = row["N"], Fraction(row["u"])
        length, bits = moving_length(uf, n)
        assert row["actualPrimeLabel"] is False and bits == row["cutoffBits"]
        x, z = arb(n)+arb(1)/5, arb(n)+arb(8)/5
        total = x+z
        fraction = (arb(3)/2-total/length-(x-z)**2/(2*total**2))/(arb(3)/2)
        assert fraction > arb(1)/30
        compare_real(row["length"], length)
        compare_real(row["retainedCoefficientFraction"], fraction)
        comparisons += 2

    result = {"passed": True, "precisionBits": 420,
              "actualPrimeAtomRows": len(data["rows"]),
              "scalarGeometryRows": len(data["scalars"]),
              "ballComparisons": comparisons, "relativeWidthsChecked": True,
              "producerImported": False, "prefixReplayMethod": "binomial marginals",
              "divisorResponseIndependentlyEnumerated": True,
              "swappedIncidencesChecked": True, "nativeCoreEnumerated": False,
              "actualZeroSamples": 0, "nativeEntryOrderCertified": False,
              "fullConstantCeilingProved": False, "newGlobalCeilingCredit": 0}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()

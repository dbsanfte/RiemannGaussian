#!/usr/bin/env python3
"""Independent 420-bit replay; floating continuum output is not certified."""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path

from flint import arb, ctx


def load(row: dict) -> arb:
    mid, rad = row["mid"], row["rad"]
    return arb(int(mid[0]))*arb(2)**int(mid[1])+arb(0, int(rad[0]))*arb(2)**int(rad[1])


def compare(row: dict, expected: arb) -> None:
    got = load(row)
    assert got.overlaps(expected), (got, expected)
    scale = abs(expected)
    assert scale > 0
    assert got.rad() < scale*arb(2)**(-280)
    assert expected.rad() < scale*arb(2)**(-330)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/riesz-selberg-signed-boundary/numeric-replay.json"))
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    ctx.prec = 420
    assert data["schemaVersion"] == 1 and data["precisionBits"] == 360
    assert data["actualPrimeSamples"] == data["actualZeroSamples"] == 0
    assert data["nativeEntryOrderCertified"] is False
    assert data["fullConstantCeilingProved"] is False and data["newGlobalCeilingCredit"] == 0
    uf = Fraction(data["radius"])
    u, y = arb(uf.numerator)/uf.denominator, 19*arb.pi()
    controls = {"height": y, "sineIntegral": 2/y, "phaseEndpoint": (2/y)**2,
                "limitingSaddleCoefficient": 3+2/u.log(),
                "continuumLimit": (3+2/u.log())*(2/y)**2,
                "phaseCertificateSlack": arb(1)/900-arb(1)/1500000-arb(1)/1000}
    assert controls["phaseCertificateSlack"] > 0 and 54 < y < 60
    for name, value in controls.items():
        compare(data["controls"][name], value)
    comparisons = len(controls)
    assert len(data["scalarRows"]) == 6
    for row in data["scalarRows"]:
        n, a, b = row["N"], Fraction(row["a"]), Fraction(row["b"])
        assert row["actualPrimeLabel"] is False and n >= 65536
        inv = (1/uf)**n/(n+1)  # Exact rational floor, independent formula.
        cutoff = inv.numerator//inv.denominator
        assert cutoff.bit_length() == row["cutoffBits"]
        L = 2*arb(cutoff+2).log()
        x, z = arb(n)+arb(a.numerator)/a.denominator, arb(n)+arb(b.numerator)/b.denominator
        T = x+z
        F = (n*((T/(2*n)).log()-(T-2*n)/(2*n))).exp()
        delta = -T*(T-L)/L+2*x*z/T
        B = 3*n-4*arb(n)**2/L
        assert L >= arb(277)*n/200 and B >= arb(n)/10
        assert abs(delta*F-B) < 26 and F <= 1 and abs(F-1) <= arb(2)/n
        for name, value in {"length": L, "saddleFactor": F,
                            "saddleCoefficient": B, "joinedSaddleError": delta*F-B}.items():
            compare(row["values"][name], value)
            comparisons += 1
    assert len(data["continuumDiagnostics"]) == 6
    assert all(row["certified"] is False and row["actualPrimeSum"] is False
               for row in data["continuumDiagnostics"])
    result = {"passed": True, "precisionBits": 420, "scalarRows": 6,
              "ballComparisons": comparisons, "relativeWidthsChecked": True,
              "producerImported": False, "continuumQuadratureCertified": False,
              "actualPrimeSamples": 0, "actualZeroSamples": 0,
              "nativeEntryOrderCertified": False, "newGlobalCeilingCredit": 0}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Independent optional 420-bit replay; keep interval widths visible."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import arb, ctx


def decode(entry: dict) -> arb:
    mid = arb(int(entry["mid"][0])) * arb(2) ** entry["mid"][1]
    rad = arb(int(entry["rad"][0])) * arb(2) ** entry["rad"][1]
    return arb(mid, rad)


def verify(value: arb, stored: dict) -> None:
    ball = decode(stored)
    assert value.overlaps(ball), (value, ball)
    assert ball.rad() <= (1 + ball.abs_upper()) * arb(10) ** -85


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path,
                        default=Path(".lake/riesz-ceiling-sparse-arithmetic/probe.json"))
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/riesz-ceiling-sparse-arithmetic/numeric-replay.json"))
    args = parser.parse_args()
    ctx.prec = 420
    data = json.loads(args.input.read_text())
    assert not data["fullCeilingProved"] and data["newGlobalCeilingCredit"] == 0
    assert not data["arithmeticMassNumericallyBounded"] and not data["nativeEntryOrderCertified"]
    source_exponent = 2 * arb("1.0001").log() - arb("0.00037")
    verify(source_exponent, data["sourceSquaredExponent"])
    verify(-source_exponent / 2 - arb(1) / 16384, data["pointwiseRateMargin"])
    verify(arb(2).log() / 1600, data["modulusRate"])
    verify(arb(2).log() / 1600 - arb(1) / 16384, data["allClassNormPriceExponent"])
    for row in data["rows"]:
        n, d = row["N"], int(row["modulus"])
        assert d == 1 << (n // 1600 + 1)
        # Replay via the combined logarithmic exponent, rather than separate powers.
        verify((source_exponent * n).exp(), row["sourceSquaredRate"])
        verify((-arb("0.00017") * n).exp(), row["provedSquaredRate"])
        verify((-arb(n) / 16384).exp(), row["pointwiseRate"])
        verify((-arb(n) / 32768).exp(), row["unionRate"])
        verify(((n + 1) ** 2) * (-arb(n) / 16384).exp(), row["pointwiseShapeWithoutConstant"])
        verify((arb(d).log() - arb(n) / 2500).exp(), row["modulusLowerRatio"])
        verify((arb(d).log() + 2 * arb(n + 1).log() - arb(n) / 16384).exp(),
               row["allClassNormPriceWithoutConstant"])
    for row in data["integerEndpointRows"]:
        d, m = row["d"], row["M"]
        # Closed arithmetic progression endpoints, independently of enumeration.
        counts = [0 if r > m else (m - r) // d + 1 for r in range(d)]
        assert counts == row["counts"]
        assert max(counts) <= row["completeQuotientBound"] == m // d + 1
    result = {"precisionBits": 420, "intervalWidthsChecked": True,
              "rateRowsReplayed": len(data["rows"]),
              "integerEndpointRowsReplayed": len(data["integerEndpointRows"]),
              "classification": "independent finite controls; not native core enumeration",
              "fullCeilingProved": False, "newGlobalCeilingCredit": 0,
              "nativeEntryOrderCertified": False}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()

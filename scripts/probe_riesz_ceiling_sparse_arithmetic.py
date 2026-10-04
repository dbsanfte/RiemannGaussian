#!/usr/bin/env python3
"""Optional quantitative controls for the actual sparse-population theorem.

The Lean theorem covers whole native residue populations. This probe checks
the numerical rate and exact integer progression endpoints; it neither
enumerates a native core nor certifies an actual-zero/ceiling entry order.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import arb, ctx


def record(value: arb) -> dict:
    mid, rad = value.mid().man_exp(), value.rad().man_exp()
    return {"ball": value.str(85), "mid": [str(mid[0]), int(mid[1])],
            "rad": [str(rad[0]), int(rad[1])]}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/riesz-ceiling-sparse-arithmetic/probe.json"))
    args = parser.parse_args()
    ctx.prec = 360
    u = arb(10001) / 20000
    raw_exponent = 2 * (2 * u).log() - arb(37) / 100000
    envelope_exponent = -arb(17) / 100000
    margin = -raw_exponent / 2 - arb(1) / 16384
    assert raw_exponent < envelope_exponent < 0 and margin > 0
    modulus_rate = arb(2).log() / 1600
    assert modulus_rate > arb(1) / 2500
    full_union_price_rate = modulus_rate - arb(1) / 16384
    assert full_union_price_rate > 0
    rows = []
    for n in (1, 1600, 4096, 16384, 65536, 131072, 524288, 1048576):
        d = 2 ** (n // 1600 + 1)
        source_squared = (2 * u) ** (2 * n) * (-arb(37) * n / 100000).exp()
        proved_squared = (-arb(17) * n / 100000).exp()
        pointwise_rate = (-arb(n) / 16384).exp()
        union_rate = (-arb(n) / 32768).exp()
        assert source_squared <= proved_squared <= pointwise_rate ** 2
        assert arb(d) >= (arb(n) / 2500).exp()
        rows.append({"N": n, "modulus": str(d),
                     "sourceSquaredRate": record(source_squared),
                     "provedSquaredRate": record(proved_squared),
                     "pointwiseRate": record(pointwise_rate),
                     "unionRate": record(union_rate),
                     "pointwiseShapeWithoutConstant": record((n + 1) ** 2 * pointwise_rate),
                     "modulusLowerRatio": record(arb(d) * (-arb(n) / 2500).exp()),
                     "allClassNormPriceWithoutConstant": record(arb(d) * (n + 1) ** 2 * pointwise_rate)})
    # Literal integers, including quotient/empty/end-point cases. Signs and
    # phases are irrelevant only to this combinatorial count, not to the carrier.
    endpoint_rows = []
    for d in (1, 2, 4, 8, 16, 33, 128):
        for m in (0, 1, 7, 31, 99, 250, 512):
            population = list(range(m + 1))
            counts = [sum(n % d == r for n in population) for r in range(d)]
            assert sum(counts) == m + 1
            assert max(counts) <= m // d + 1
            endpoint_rows.append({"d": d, "M": m, "counts": counts,
                                  "completeQuotientBound": m // d + 1})
    result = {"schemaVersion": 1, "precisionBits": 360,
              "classification": "scalar rate and exact integer controls; native theorem is Lean",
              "sourceSquaredExponent": record(raw_exponent),
              "pointwiseRateMargin": record(margin),
              "modulusRate": record(modulus_rate),
              "allClassNormPriceExponent": record(full_union_price_rate),
              "rows": rows, "integerEndpointRows": endpoint_rows,
              "actualZeroSamples": 0, "nativeCoreEnumerated": False,
              "arithmeticMassNumericallyBounded": False,
              "nativeEntryOrderCertified": False, "fullCeilingProved": False,
              "newGlobalCeilingCredit": 0,
              "paidPopulation": "literal residue union with card <= exp(N/32768)",
              "unpaidPopulation": "remaining native residue classes, with signed correlations retained"}
    args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()

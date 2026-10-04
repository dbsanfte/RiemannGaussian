#!/usr/bin/env python3
"""Independent 420-bit replay of whole-certificate scalar comparisons.

No producer import, actual zeros, prime sampling or native entry threshold.
Relative widths are checked even for the extremely large signed prices.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path

from flint import arb, ctx


def load_ball(row: dict) -> arb:
    mid, rad = row["mid"], row["rad"]
    return arb(int(mid[0]))*arb(2)**int(mid[1])+arb(0, int(rad[0]))*arb(2)**int(rad[1])


def compare(row: dict, expected: arb) -> None:
    stored = load_ball(row)
    assert stored.overlaps(expected), (stored, expected)
    if expected == 0:
        assert stored == expected == 0
    else:
        assert stored.rad() < abs(expected)*arb(2)**(-290)
        assert expected.rad() < abs(expected)*arb(2)**(-350)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/riesz-ceiling-sublinear-height/numeric-replay.json"))
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    ctx.prec = 420
    assert data["precisionBits"] == 360 and len(data["rows"]) == data["scalarRows"] == 24
    comparisons, improvements, quarters = 0, 0, 0
    for row in data["rows"]:
        exponent = int(row["logHeight"][2:])
        L = arb(10)**exponent
        uf, d = Fraction(row["u"]), row["degree"]
        u = arb(uf.numerator)/uf.denominator
        g = (arb(2)*u).log()
        target = (L+21).log()/(64*g)
        # Certify the integer degree by both floor inequalities independently.
        assert arb(d) <= target < arb(d+1)
        assert arb(d) >= 150*(L+21).log()
        exponential = (32*d*g).exp()
        height_term = (L+21)*arb(5)/(4*d)
        all_degree_lower = ((L+21)*(2*u-1)*160).sqrt()
        price = (L+21).sqrt()+arb(1)/120*((L+21)/(L+21).log())
        assert exponential+height_term <= price
        assert all_degree_lower <= exponential+height_term
        small = ((36922*arb(9)/100+840)+(L/35+57*L.log()))*312500/984028661
        wide = ((36922+840)+(L/35+57*L.log()))/6200
        old = arb(1) if L <= 60000 else min(small, wide)
        improved = bool(price < old)
        combined = price if improved else old
        c = (arb(32).log()-arb(13).log())/(-2*u*u.log())-(arb(19).log()-arb(13).log())
        old_signed = old*(c*old-1)
        new_signed = combined*(c*combined-1) if improved else old_signed
        ratio = new_signed/old_signed if improved else arb(1)
        if improved:
            assert new_signed < old_signed
        quarter = bool(old_signed > 0 and new_signed < old_signed/4)
        assert improved == row["strictPriceImprovement"]
        assert quarter == row["quarterPriceAtThisScalar"]
        values = {"orderExponent": exponential, "orderHeightTerm": height_term,
                  "allDegreePriceLower": all_degree_lower,
                  "proposedCap": price, "oldCap": old, "combinedCap": combined,
                  "oldSignedPrice": old_signed, "newSignedPrice": new_signed,
                  "signedPriceRatio": ratio}
        assert set(values) == set(row["values"])
        for name, value in values.items():
            compare(row["values"][name], value)
            comparisons += 1
        improvements += improved
        quarters += quarter
    assert data["newConstantCeilingCredit"] == 0
    result = {"passed": True, "precisionBits": 420, "scalarRows": len(data["rows"]),
              "ballComparisons": comparisons, "relativeWidthsChecked": True,
              "producerImported": False, "improvedRows": improvements,
              "quarterPriceRows": quarters, "actualZeroSamples": 0,
              "nativeCoreEnumerated": False, "nativeEntryOrderCertified": False,
              "largeHeightThresholdCertified": False,
              "constant42Over25CeilingProved": False, "newConstantCeilingCredit": 0}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()

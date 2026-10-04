#!/usr/bin/env python3
"""Independent optional 420-bit replay of the whole signed height prices."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import arb, ctx


def verify(value: arb, stored: dict) -> None:
    mid = arb(int(stored["mid"][0])) * arb(2) ** stored["mid"][1]
    rad = arb(int(stored["rad"][0])) * arb(2) ** stored["rad"][1]
    enclosed = arb(mid, rad)
    assert value.overlaps(enclosed), (value, enclosed)
    assert enclosed.rad() <= (1+enclosed.abs_upper())*arb(10)**-85


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path,
                        default=Path(".lake/riesz-ceiling-whole-height-bound/probe.json"))
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/riesz-ceiling-whole-height-bound/numeric-replay.json"))
    args = parser.parse_args()
    ctx.prec = 420
    data = json.loads(args.input.read_text())
    assert not data["fullConstantCeilingProved"] and data["newGlobalConstantCeilingCredit"] == 0
    assert not data["newZeroExclusion"] and not data["nativeEntryOrderCertified"]
    # Replay the physical lower through the normalized second moment, rather
    # than the physical rational formula used by the discovery probe.
    x = arb(22501)/2000
    lower = arb(225000)*x/(x*x+2)
    verify(lower, data["physicalSecondMomentLower"])
    gaussian = arb(225000)*arb.pi().sqrt()/2*(x*x/4).exp()*(x/2).erfc()
    verify(gaussian, data["physicalGaussianClosedForm"])
    assert gaussian > lower > 19650
    u = arb(10001)/20000
    retained = (arb(32)/13).log()/(-2*u*u.log())-(arb(19)/13).log()
    verify(retained, data["retainedCostAtRadiusCeiling"])
    verify(-2+4*retained, data["multipleSourceAtRadiusCeiling"])
    verify(-2+4*retained-arb(42)/25, data["multipleSourceMinusConstantTarget"])
    small_unit = arb(984028661)/312500
    verify(small_unit/6200, data["asymptoticMultiplicityPriceRatio"])
    verify((small_unit/6200)**2, data["asymptoticQuadraticPriceRatio"])
    margin = 3*small_unit-(arb("4162.98")+arb(160000)/35+57*12)
    verify(margin, data["tripleSourceMarginAtLogHeight160000"])
    assert margin > 0 and (arb(2718)/1000)**12 > 160000
    assert data["integerMultiplicityCapUpToLogHeight160000"] == 2
    for row in data["rows"]:
        height = int(row["logHeight"])
        L = arb(height)
        small_cap = (arb("4162.98")+L/35+57*L.log())/small_unit
        wide_cap = (37762+L/35+57*L.log())/6200
        cap = arb(1) if height <= 60000 else (small_cap if small_cap < wide_cap else wide_cap)
        price = cap*(retained*cap-1)
        old = small_cap*(retained*small_cap-1)
        verify(small_cap, row["smallCap"])
        verify(wide_cap, row["wideCap"])
        verify(price, row["joinedHeightPrice"])
        verify(old, row["smallComparisonPrice"])
        verify(price/old, row["priceRatio"])
        assert row["constantTargetProvedByThisBound"] == (height <= 60000)
        assert row["nearCeilingProvedByThisBound"] == (height <= 160000)
        if 60000 < height <= 160000:
            assert cap < 3 and -2+4*retained < arb(2101)/1250
        if height >= 10000000:
            assert price < arb(16)/49*old
    result = {"precisionBits": 420, "intervalWidthsChecked": True,
              "heightPriceRowsReplayed": len(data["rows"]),
              "independentSecondMomentAndGaussianReplay": True,
              "classification": "scalar controls; no native carrier or actual-zero samples",
              "fullConstantCeilingProved": False, "newGlobalConstantCeilingCredit": 0,
              "nativeEntryOrderCertified": False}
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()

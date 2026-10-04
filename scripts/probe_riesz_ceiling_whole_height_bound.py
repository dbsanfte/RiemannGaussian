#!/usr/bin/env python3
"""Optional interval controls for the proved whole-carrier height price.

These are complete scalar certificate constants, not sampled prime mass,
actual zeros, native carrier values or a finite-order ceiling certificate.
The Lean theorem, independently, covers all fixed heights in the original strip.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from flint import arb, ctx


def ball(f: F) -> arb:
    return arb(f.numerator) / f.denominator


def record(value: arb) -> dict:
    mid, rad = value.mid().man_exp(), value.rad().man_exp()
    return {"ball": value.str(85), "mid": [str(mid[0]), int(mid[1])],
            "rad": [str(rad[0]), int(rad[1])]}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/riesz-ceiling-whole-height-bound/probe.json"))
    args = parser.parse_args()
    ctx.prec = 360
    width, gap = F(1, 450000), F(1, 20000)
    damping = gap + width / 1000
    variance = 4 * width ** 2
    moment_lower = damping / (damping ** 2 + 2 * variance)
    assert moment_lower == F(1125050000000, 57143889) > 19650
    assert F(79, 250) * (19650 - 5) > 6200
    small_unit = F(984028661, 312500)
    assert F(79, 250) * (F(12462309, 1250) - 5) == small_unit
    triple_margin = 3*small_unit-(F(36922)*F(9,100)+F(160000,35)+57*12+840)
    assert triple_margin == F(61833131,2187500) > 0
    assert F(2718,1000)**12 > 160000
    # An independent closed-form Gaussian value checks the rational moment bound.
    b, a = ball(variance), ball(damping)
    gaussian = arb.pi().sqrt() / (2 * b.sqrt()) * (a*a/(4*b)).exp() * (a/(2*b.sqrt())).erfc()
    assert gaussian > ball(moment_lower)
    u = arb(10001) / 20000
    retained = (arb(32)/13).log()/(-2*u*u.log())-(arb(19)/13).log()
    assert arb("0.9") < retained < arb("0.921")
    multiple_source = -2+4*retained
    assert multiple_source > arb(42)/25
    rows = []
    heights = [1, 20, 60000, 60001, 100000, 158000, 160000, 160001, 1000000, 10000000,
               100000000, 10**10, 10**20, 10**50, 10**100, 10**150, 10**1000]
    for height in heights:
        L = arb(height)
        common = L/35+57*L.log()+840
        small_cap = (36922*arb(9)/100+common)/ball(small_unit)
        wide_cap = (36922+common)/6200
        selected = "low-height simplicity" if height <= 60000 else (
            "small complete Gaussian" if small_cap < wide_cap else "wide complete Gaussian")
        cap = arb(1) if height <= 60000 else (small_cap if small_cap < wide_cap else wide_cap)
        joined_price = -cap+retained*cap**2
        old_price = -small_cap+retained*small_cap**2
        if 60000 < height <= 160000:
            assert cap < 3
            assert -2+4*retained < arb(2101)/1250
        if height >= 10000000:
            assert wide_cap < arb(4)/7*small_cap
            assert joined_price < arb(16)/49*old_price
        rows.append({"logHeight": str(height), "activeCertificate": selected,
                     "smallCap": record(small_cap), "wideCap": record(wide_cap),
                     "joinedHeightPrice": record(joined_price),
                     "smallComparisonPrice": record(old_price),
                     "priceRatio": record(joined_price/old_price),
                     "constantTargetProvedByThisBound": height <= 60000,
                     "nearCeilingProvedByThisBound": height <= 160000})
    result = {"schemaVersion": 1, "precisionBits": 360,
              "classification": "scalar controls for a whole signed height-dependent Lean bound",
              "physicalSecondMomentLower": record(ball(moment_lower)),
              "physicalGaussianClosedForm": record(gaussian),
              "retainedCostAtRadiusCeiling": record(retained),
              "multipleSourceAtRadiusCeiling": record(multiple_source),
              "multipleSourceMinusConstantTarget": record(multiple_source-arb(42)/25),
              "asymptoticMultiplicityPriceRatio": record(ball(small_unit)/6200),
              "asymptoticQuadraticPriceRatio": record((ball(small_unit)/6200)**2),
              "tripleSourceMarginAtLogHeight160000": record(ball(triple_margin)),
              "integerMultiplicityCapUpToLogHeight160000": 2,
              "provedNearCeiling": "2101/1250", "nearCeilingMinusTarget": "1/1250",
              "provedLargeHeightPriceRatio": "16/49",
              "originalRadius": "1/2 < u <= 10001/20000", "rows": rows,
              "allFixedHeightsCoveredByHeightDependentTheorem": True,
              "fullConstantCeilingProved": False, "newGlobalConstantCeilingCredit": 0,
              "newZeroExclusion": False, "actualZeroSamples": 0,
              "nativeCoreEnumerated": False, "nativeEntryOrderCertified": False,
              "unpaid": "remove the growing height price using actual signed correlations",
              "warning": "Price ratios are certificate bounds, not measured carrier progress percentages."}
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"rows": len(rows), "output": str(args.output),
                      "fullConstantCeilingProved": False}))


if __name__ == "__main__":
    main()

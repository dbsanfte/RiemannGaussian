#!/usr/bin/env python3
"""Optional complete-certificate scalar checks, not prime or zero samples.

The native constant ceiling remains open. Numerical degree choices do not
certify a native entry order or the existential large-height threshold.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path

from flint import arb, ctx


def record(x: arb) -> dict:
    mid, rad = x.mid().man_exp(), x.rad().man_exp()
    return {"mid": [str(mid[0]), int(mid[1])],
            "rad": [str(rad[0]), int(rad[1])], "ball": x.str(65)}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/riesz-ceiling-sublinear-height/probe.json"))
    args = parser.parse_args()
    ctx.prec = 360
    rows = []
    for exponent in (3, 6, 10, 20, 100, 1000, 4000, 10000):
        L = arb(10)**exponent
        for uf in (Fraction(10001, 20000), Fraction(20001, 40000), Fraction(500001, 1000000)):
            u = arb(uf.numerator)/uf.denominator
            x = (L+21).log()/(64*(2*u).log())
            degree = int(x.floor().unique_fmpz())
            assert arb(degree) <= x < arb(degree+1)
            assert degree >= 150*(L+21).log()
            exponential = (2*u)**(32*degree)
            height_term = arb(5)*(L+21)/(4*degree)
            all_degree_lower = (160*(2*u-1)*(L+21)).sqrt()
            proposed = (L+21).sqrt()+(L+21)/(120*(L+21).log())
            assert exponential <= (L+21).sqrt()
            assert exponential+height_term <= proposed
            assert all_degree_lower <= exponential+height_term
            def gaussian_cap(q: arb, unit: arb) -> arb:
                return (36922*q+L/35+57*L.log()+840)/unit
            older = (arb(1) if L <= 60000 else
                     min(gaussian_cap(arb(9)/100, arb(984028661)/312500),
                         gaussian_cap(arb(1), arb(6200))))
            improved = bool(proposed < older)
            joined = proposed if improved else older
            c = (arb(32)/13).log()/(-2*u*u.log())-(arb(19)/13).log()
            old_signed = -older+c*older**2
            new_signed = -joined+c*joined**2 if improved else old_signed
            if improved:
                assert new_signed < old_signed
            values = {"orderExponent": exponential, "orderHeightTerm": height_term,
                      "allDegreePriceLower": all_degree_lower,
                      "proposedCap": proposed, "oldCap": older, "combinedCap": joined,
                      "oldSignedPrice": old_signed, "newSignedPrice": new_signed,
                      "signedPriceRatio": new_signed/old_signed if improved else arb(1)}
            rows.append({"logHeight": "1e"+str(exponent), "u": str(uf),
                         "degree": degree, "values": {k: record(v) for k, v in values.items()},
                         "strictPriceImprovement": improved,
                         "quarterPriceAtThisScalar": bool(old_signed > 0 and new_signed < old_signed/4)})
    result = {"schemaVersion": 1, "precisionBits": 360, "rows": rows,
              "scalarRows": len(rows), "classification": "complete certificate constants",
              "nativeCoreEnumerated": False, "actualZeroSamples": 0,
              "nativeEntryOrderCertified": False, "largeHeightThresholdCertified": False,
              "constant42Over25CeilingProved": False, "newConstantCeilingCredit": 0}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"scalarRows": len(rows),
                      "improvedRows": sum(r["strictPriceImprovement"] for r in rows),
                      "quarterPriceRows": sum(r["quarterPriceAtThisScalar"] for r in rows)}))


if __name__ == "__main__":
    main()

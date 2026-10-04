#!/usr/bin/env python3
"""Independent integer and interval replay of the finite-order test.

FLINT cross-products check the exact block inequalities. Arb ball arithmetic
then evaluates all five test terms independently, including the signed
selected source's complete arithmetic majorant. No producer is imported;
this does not certify a competing-zero gap or any native carrier entry order.
"""
import argparse
import json
from pathlib import Path

from flint import arb, ctx, fmpz


def rational(text):
    parts = text.split("/")
    return fmpz(parts[0]), fmpz(parts[1] if len(parts) == 2 else 1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    p = data["parameters"]
    assert p["radiusCeiling"] == "10001/20000"
    assert p["competingRadius"] == "11/20"
    assert p["logHeightCeiling"] == str(10**150)
    assert p["momentOrder"] == 4096 and p["realAxisLogUpper"] == 4
    assert data["competingGapIsExtraHypothesis"]
    assert data["isolatedSectorCeilingLeanProved"]
    assert data["provedSignedCounterweightThreshold"] == "-1/5"
    assert not data["signedCounterweightNeedsCompetingGap"]
    for field in ["actualPrimeData", "actualZeroData", "uniformExposedGapAssumed",
                  "allHeightFixedStripCeilingProved", "simpleZeroExclusionProved",
                  "nativeEntryOrderCertified"]:
        assert not data[field], field
    expected = [("10001/10000", "129/128"), ("10001/11000", "1/400"),
                ("10001/20000", "1/1000000000000000000"),
                ("10001/14000", "1/1000000000"), ("10001/15000", "1/10000000000")]
    assert len(data["exactBlockCertificates"]) == len(expected)
    for row, (base, upper) in zip(data["exactBlockCertificates"], expected):
        assert row["base"] == base and row["upper"] == upper and row["power"] == 64
        a, b = rational(base)
        c, d = rational(upper)
        assert a**64*d <= c*b**64
    ctx.prec = 400
    u, radius, height, order = arb(10001)/20000, arb(11)/20, arb(10)**150, 4096
    terms = {
        "realAxisPole": (2*u)**(order+1),
        "competingActualZeros": (height+11)*(u/radius)**(order+1),
        "zetaPoleAtHeight": u**(order+1),
        "completeResidualIncludingRealAxis":
            160*u*(height+4)*(order+1)*(10*u/7)**order,
        "canonicalReflectedChannels": (height+11)*(4*u/3)**(order+1),
    }
    for key, value in terms.items():
        assert abs(value-arb(data["fixedTestComponents"][key])) < arb("1e-85")
    total = sum(terms.values(), arb(0))
    assert total < 2
    assert total < arb(9)/5
    assert abs(total-arb(data["fixedTestUpper"])) < arb("1e-85")
    assert terms["realAxisPole"] < arb(7)/4
    assert all(value < arb(1)/1000 for key, value in terms.items() if key != "realAxisPole")
    paid = sum((value for key, value in terms.items() if key != "competingActualZeros"), arb(0))
    assert 2-paid > arb(1)/5
    assert abs(2-paid-arb(data["numericalCounterweightRequiredForDoubleSource"])) < arb("1e-85")
    result = {"exactIntegerBlockCertificates": len(expected), "intervalTerms": len(terms),
              "arbPrecisionBits": ctx.prec, "fixedTestInterval": str(total),
              "strictTestBelowNineFifths": True, "strictTestBelowTwo": True,
              "signedCounterweightExceedsOneFifth": True, "competingGapCertifiedByNumerics": False,
              "entryOrderCertified": False, "fullCeilingStillOpen": True}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Independent exact/Arb replay of the signed phase probe; imports no producer."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from flint import acb, arb, ctx


def ball(text):
    x = F(text)
    return arb(x.numerator)/x.denominator


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    p = data["parameters"]
    assert p["sourceRadius"] == "10001/20000" and p["nearbyRadius"] == "11/20"
    assert p["loggedPower"] == 4097 and p["momentOrder"] == 4096
    assert p["negativeSignedBudget"] == "-1/5" and p["uniformConstructiveOrdinateCone"] == "1/8194"
    assert data["heightCondition"] == "log(abs(y)+22)<=10^150"
    assert data["leanActualMultiplicityInequality"] and data["leanAdditionalSectorCeiling"]
    assert data["geometryConditionsRemainExplicit"]
    for name in ["actualZeroData", "actualPrimeData", "nativeEntryOrderCertified",
                 "fullAllHeightCeilingProved", "simpleZeroFloorProved", "zeroExclusionProved"]:
        assert not data[name], name
    ctx.prec = 420
    u, r = ball(p["sourceRadius"]), ball(p["nearbyRadius"])

    def evaluate(row):
        a, b = F(row["denominatorReal"]), F(row["denominatorImag"])
        assert row["multiplicity"] == 1 and row["loggedPower"] == 4097
        assert not row["actualZero"]
        assert row["constructiveCone"] == (4097*abs(b) <= a)
        d = acb(ball(a), ball(b))
        assert abs(d) <= r and abs(d) > u
        value = (acb(u)/d)**4097
        assert abs(value.real-arb(row["normalizedPowerReal"])) < arb("1e-93")
        assert abs(value.imag-arb(row["normalizedPowerImag"])) < arb("1e-93")
        if row["constructiveCone"]:
            assert value.real > 0
        return value

    for row in data["modeRows"]:
        evaluate(row)
    packet = data["mixedSignedPacket"]
    first, second = [evaluate(row) for row in packet["components"]]
    assert first.real > 0 and second.real < 0
    mixed = (first+second).real
    assert mixed > -arb(1)/5
    assert abs(mixed-arb(packet["collectedReal"])) < arb("1e-93")
    cloud = data["preservedCloudRegression"]
    assert cloud["modeCount"] == 131072 and cloud["characterIdentityUsed"]
    bound = 2*131072*(u**4097+(u/r)**4097)
    assert bound < arb("1e-160")
    assert abs(bound-arb(cloud["absoluteErrorUpper"]))/bound < arb("1e-93")
    assert -2+bound < -arb(1)/5
    assert cloud["failsSignedFloor"] and cloud["counterexampleIsSynthetic"]
    result = {"arbPrecisionBits": ctx.prec, "modeRows": len(data["modeRows"]),
              "mixedSignedRealInterval": str(mixed), "mixedPacketPassesSignedBudget": True,
              "frozenCloudNearErrorInterval": str(bound), "cloudStillUnpaid": True,
              "genuineZeroSamples": 0, "nativeEntryOrderCertified": False,
              "fullAllHeightCeilingProved": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()

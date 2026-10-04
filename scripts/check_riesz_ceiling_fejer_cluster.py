#!/usr/bin/env python3
"""Independent exact/Arb replay; imports no producer or cached functions."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from flint import acb, arb, ctx


def ball(x):
    x = F(x)
    return arb(x.numerator)/x.denominator


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    p = data["parameters"]
    assert p == {"radiusCeiling": "10001/20000", "stride": 1100, "degree": 8,
                 "momentOrders": [1100*j-1 for j in range(1, 9)],
                 "heightUpper": "10^150", "sourceCoefficient": 72,
                 "massCoefficient": 9, "leanWholeCostUpper": 107}
    for flag in ["separateOpposingPhaseDebits", "actualPrimeData", "actualZeroData",
                 "nativeEntryOrderCertified", "fullAllHeightCeilingProved",
                 "simpleZeroFloorProved", "zeroExclusionProved"]:
        assert not data[flag], flag
    ctx.prec = 420
    u, H = ball("10001/20000"), arb(10)**150

    def err(k):
        return u**k+160*u*(H+4)*k*(10*u/7)**(k-1)+(H+11)*(4*u/3)**k

    cost = 2*sum((9-j)*((2*u)**(1100*j)+err(1100*j)) for j in range(1, 9))
    assert cost < 107
    assert abs(cost-arb(data["exactArithmeticCost"])) < arb("1e-93")
    for j, recorded in enumerate(data["remainderCosts"], 1):
        computed = err(1100*j)
        assert computed < ball("1/1000")
        assert abs(computed-arb(recorded))/computed < arb("1e-93")
    source_cap = 2*sum((9-j)*F(1117, 1000)**j for j in range(1, 9))
    assert source_cap == F(data["exactRationalSourceCap"])
    assert source_cap < F(1069, 10) and source_cap+F(72, 1000) < 107
    # Replay every exact rational block separately from the decimals.
    for base, order, cap in [(F(10001,10000),100,F(10101,10000)),
                             (F(10101,10000),11,F(1117,1000)),
                             (F(10001,20000),64,F(1,3000)),
                             (F(10001,14000),100,F(1,400000000000000)),
                             (F(10001,14000),99,F(1,200000000000000)),
                             (F(10001,15000),100,F(1,400000000000000000))]:
        assert base**order <= cap

    for row in data["modeRows"]:
        assert row["multiplicity"] == 1 and not row["actualZero"]
        assert row["completeLogPowers"] == [1100*j for j in range(1, 9)]
        radius, turn = ball(row["normalizedNodeRadius"]), ball(row["stridePhaseTurns"])
        # Powers are logged before collection, matching the exact Lean ledger.
        v = acb(radius)*(acb(0, 2*arb.pi()*turn/1100)).exp()
        w = v**1100
        powers = [w**j for j in range(1, 9)]
        joined = 9+2*sum((9-j)*powers[j-1].real for j in range(1, 9))
        prefixes = [sum(w**j for j in range(n+1)) for n in range(9)]
        squares = abs(prefixes[8])**2+(1-abs(w)**2)*sum(abs(g)**2 for g in prefixes[:8])
        assert (joined-squares).contains(0)
        assert abs(joined-arb(row["collectedFejer"])) < arb("1e-93")
        assert abs(squares-arb(row["positiveSquare"])) < arb("1e-93")
        for computed, recorded in zip(powers, row["individualSignedTerms"]):
            assert abs(computed.real-arb(recorded)) < arb("1e-93")
        # Some exact unit-circle rows vanish; don't infer strict positivity
        # from a ball touching zero. Generic nonnegativity is proved in Lean.
        assert joined > -arb("1e-93")

    c = data["preservedDenseCloud"]
    assert c["modeCount"] == 131072 and c["competingMass"] == 262142
    assert c["stillUnpaid"] and c["characterIdentityUsed"]
    cloud = 9*c["competingMass"]+2*sum((9-j)*(-2+2*131072*u**(1100*j))
                                    for j in range(1, 9))
    assert cloud > 0 and abs(cloud-arb(c["joinedFejer"])) < arb("1e-93")
    result = {"arbPrecisionBits": ctx.prec, "modeRows": len(data["modeRows"]),
              "jointCostInterval": str(cost), "rationalSourceCapExact": str(source_cap),
              "costBelow107": True, "allSquareIdentitiesReplayed": True,
              "massAtMostFourExcludesMultipleSource": 9*4+107 < 72*2,
              "denseCloudStillUnpaid": True, "genuineZeroSamples": 0,
              "nativeEntryOrderCertified": False, "fullAllHeightCeilingProved": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()

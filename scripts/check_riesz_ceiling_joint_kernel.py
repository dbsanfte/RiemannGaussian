#!/usr/bin/env python3
"""Independent exact/Arb replay of the joined scalar kernel audit.

Imports neither the producer nor its functions. No arithmetic bound or
complete-prime transport is inferred from these scalar rows.
"""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from flint import arb, ctx


def ball(x):
    x = F(x)
    return arb(x.numerator)/x.denominator


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    ctx.prec = 420
    p = data["parameters"]
    orders = [64, 256, 640, 1536, 4096, 8192, 16384, 65536, 400000]
    assert p == {"radiusCeiling": "10001/20000", "arithmeticDamping": "1/2",
                 "separatedDamping": "7/10", "target": "42/25",
                 "sourceNormalization": "u^(N+1)",
                 "filterCoefficients": ["10001", "-10001/2"], "orders": orders}
    for flag in ["actualPrimeData", "actualZeroData", "primeDensityTransport",
                 "literalCarrierPriceIdentified", "newArithmeticCeilingCredit",
                 "nativeEntryOrderCertified", "fullAllHeightCeilingProved",
                 "simpleZeroFloorProved", "zeroExclusionProved"]:
        assert not data[flag], flag
    ledger = data["exactBookkeeping"]
    assert ledger["coefficientsCollectedBeforeNorm"]
    assert sum(map(F, ledger["sourceSlotValues"])) == 1
    assert sum(map(F, ledger["poleSlotCoefficients"])) == 0
    assert ledger["sourceSlotValues"] == ["10001", "-10000"]
    assert ledger["poleSlotCoefficients"] == ["10001", "-10001"]
    assert ledger["poleCommonFactor"] == "(2u)^(N+1)"
    uf = F(10001, 20000)
    assert 10001-F(10001, 2)/uf == 1
    assert 10001-F(10001, 2)/F(1, 2) == 0
    u, a, q = ball(uf), ball("1/2"), ball("7/10")
    g, b = 2*u, ball("1/10001")

    def replay(computed, recorded):
        assert abs(computed-arb(recorded))/computed < arb("1e-94")

    prices = []
    assert len(data["normPriceRows"]) == len(orders)
    for N, row in zip(orders, data["normPriceRows"]):
        j = N+1
        assert row["N"] == N and row["sourcePower"] == j
        assert row["factorialSlots"] == [N, N+1]
        assert row["joinedSourceExact"] == "1" and row["joinedPoleExact"] == "0"
        assert not row["literalCarrierBound"]
        # Independent closed-form Gamma absolute deviation calculation.
        pa = (j*g.log()+(2/b).log()+j*arb(j).log()-j-arb(j+1).lgamma()).exp()
        pq_upper = (u/q)**j*(1+1/(2*q))/b
        lower = (arb(N)/255936).exp()/2
        replay(pa, row["positiveFullKernelPrice"])
        replay(pq_upper, row["separatedPriceUpper"])
        replay(lower, row["leanMethodPriceLower"])
        assert pq_upper < (-arb(N)/32).exp()
        assert row["separatedPricePaidAtExpMinusNOver32"]
        assert pa > lower
        assert row["methodLowerExceedsTarget"] == bool(lower > ball("42/25"))
        if N >= 400000:
            assert lower > ball("42/25")
        prices.append(str(pa))

    assert len(data["movingKernelRows"]) == 3*len(orders)
    for row in data["movingKernelRows"]:
        N, j = row["N"], row["N"]+1
        assert N in orders and row["sourcePower"] == j
        assert row["sourceExact"] == "1" and not row["actualPrimeKernel"]
        rate = {"fixed-u": u, "sqrt-order": arb(j).sqrt(),
                "linear-order": arb(j)}[row["schedule"]]
        replay((rate/(rate-u+a))**j, row["priceA"])
        replay((rate/(rate-u+q))**j, row["priceQ"])
    replay((u-a).exp(), data["linearOrderLimits"]["priceA"])
    replay((-(q-u)).exp(), data["linearOrderLimits"]["priceQ"])
    assert data["linearOrderLimits"]["separatedBudgetDoesNotVanish"]
    result = {"arbPrecisionBits": ctx.prec, "joinedNormPriceRows": len(prices),
              "movingKernelRows": len(data["movingKernelRows"]),
              "exactSourceAndPoleSlotsReplayed": True,
              "fullKernelPrice4096": prices[4], "allNumericalRowsReplayed": True,
              "onlyScalarMethodAudit": True, "newArithmeticCeilingCredit": False,
              "fullAllHeightCeilingProved": False, "nativeEntryOrderCertified": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()

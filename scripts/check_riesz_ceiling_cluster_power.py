#!/usr/bin/env python3
"""Independent integer/Arb replay; imports no producer and proves no prime bridge."""
import argparse
import json
from pathlib import Path

from flint import acb, arb, ctx, fmpz


def rat(text):
    parts = str(text).split("/")
    return fmpz(parts[0]), fmpz(parts[1] if len(parts) == 2 else 1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    m = 131072
    assert data["parameters"]["modeCount"] == m
    assert data["parameters"]["sourceRadius"] == "10001/20000"
    assert data["exactBookkeeping"]["ordersZeroAndOneRetained"]
    assert not data["exactBookkeeping"]["fractionalResiduesUsed"]
    assert data["leanAllOrdersMajorantProved"]
    assert data["leanLocalRegularHasSumProved"]
    assert data["leanSameJoinedViolationProved"]
    for name in ["actualPrimeData", "actualZeroData", "actualZetaRemainderIdentified",
                 "globalAllNegativeActualDivisorCounterexample", "nativeEntryOrderCertified",
                 "fullCeilingProved"]:
        assert not data[name], name
    assert data["arithmeticCeilingCredit"] == "0"
    assert len(data["exactBlockCertificates"]) == 2
    for row, expected in zip(data["exactBlockCertificates"],
                             [("10001/10000", 256, "641/625"), ("641/625", 512, str(3*m))]):
        assert (row["base"], row["power"], row["bound"]) == expected
        a, b = rat(row["base"])
        c, d = rat(row["bound"])
        assert a**row["power"]*d >= c*b**row["power"]

    ctx.prec = 420
    u = arb(10001)/20000
    for row in data["powerRows"]:
        k = row["loggedPower"]
        indices = list(range(0, k+1, m))
        assert row["retainedHarmonics"] == indices
        assert row["momentOrder"] == k-1
        terms = [arb.bin_uiui(k, j)*u**(k-j)*(1-u)**j for j in indices]
        singular = -2*m*sum(terms, arb(0))
        regular = 2*m*u**k
        collected = -2*m*sum(terms[1:], arb(0))
        assert row["modelExactlyZero"] == (k < m)
        if k < m:
            assert collected.is_zero()
            assert arb(row["collectedModel"]).is_zero()
        for name, value in [("rawSingular", singular), ("regularCorrection", regular),
                            ("collectedModel", collected),
                            ("completeRealAxisPoleMajorant", (2*u)**k)]:
            # Relative replay even for the extraordinarily small uncollected trace.
            reference = arb(row[name])
            if value.is_zero():
                assert reference.is_zero()
            else:
                assert abs((reference-value)/value) < arb("1e-93"), (k, name)
        assert abs(collected) <= (2*u)**k

    def v(i):
        return acb(u)+(1-u)*acb(0, 2*arb.pi()*i/m).exp()

    for row in data["geometryRows"]:
        i = row["index"]
        vi, di = v(i), acb(u)/v(i)
        assert row["residue"] == -2 and not row["actualZetaZero"]
        for name, value in [("normalizedModeNorm", abs(vi)), ("denominatorReal", di.real),
                            ("denominatorImag", di.imag), ("denominatorNorm", abs(di)),
                            ("syntheticBeta", arb(3)/2-di.real)]:
            assert abs(value-arb(row[name])) < arb("1e-90"), (i, name)
        if row["insideLocalDisk"]:
            assert abs(di) < arb(4)/5
            assert arb(3)/2-di.real > 0 and arb(3)/2-di.real < 1
        else:
            assert abs(di) > arb(4)/5
        if i:
            assert abs(di) > u and abs(vi) < 1

    first = data["localPopulation"]["firstOmittedPositiveIndex"]
    assert abs(v(first-1)) > 5*u/4 and abs(v(first)) < 5*u/4
    assert data["localPopulation"]["localModeCount"] == 1+2*(first-1)
    assert data["localPopulation"]["localMultiplicityMass"] == 2*(1+2*(first-1))
    cost = (arb(32)/13).log()/(-2*u*u.log())-(arb(19)/13).log()
    joined = -2+4*cost
    assert joined > arb(42)/25
    assert abs(joined-arb(data["sameJoinedLimit"])) < arb("1e-93")
    result = {"exactIntegerCertificates": 2, "collectedPowerRows": len(data["powerRows"]),
              "geometryRows": len(data["geometryRows"]), "arbPrecisionBits": ctx.prec,
              "sameJoinedModelSourceInterval": str(joined),
              "allOrderClaimSuppliedByLean": True, "actualPrimeOrZetaBridge": False,
              "arithmeticCeilingCredit": "0", "fullCeilingStillOpen": True}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()

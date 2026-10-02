#!/usr/bin/env python3
"""Optional quantitative audit of the proved auxiliary supply-debit bound.

Evaluates the explicit lower bound in GlobalDebitAudit.supply_tailDebit_lower
on the repository's native dyadic orders. It does NOT evaluate the signed
carrier, prove the supply capacity at these finite orders, or bound either
the funded or direct phase energy. Floating values are not certificates.
"""

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path


def experiment(radius, height, indices):
    if radius <= Fraction(1, 2) or radius > Fraction(10001, 20000):
        raise ValueError("radius must lie in (1/2, 10001/20000]")
    if not math.isfinite(height) or height < 54:
        raise ValueError("height must be fixed, finite and at least 54")
    growth = math.log1p(float(2 * radius - 1))
    coefficient = 128 * float(radius) * math.e / (3 * (math.floor(2 * height) + 1))
    result = []
    for j in indices:
        order = 8 * (j + 4) * 2 ** (j + 3)
        value_log = math.log(coefficient) + order * growth - 5 * math.log1p(order)
        result.append({
            "dyadicIndex": j, "nativeOrder": order,
            "sourceTailDebitLowerBoundLog": value_log,
            "sourceTailDebitLowerBound": math.exp(value_log) if value_log < 700 else None,
            "lowerBoundExceedsOne": value_log > 0,
            "slabCapacityAtThisFiniteOrderCertified": False,
        })
    return {
        "radiusRational": str(radius), "fixedHeight": height,
        "amplitudeGrowthExponent": growth,
        "provedLowerBoundFormula":
            "128*u*exp(1)/(3*(floor(2*y)+1)) * (2*u)^N/(N+1)^5",
        "formulaLeanTheorem":
            "RiemannGaussian.ZetaRieszGlobalDebitAudit.supply_tailDebit_lower",
        "nativeDyadicOrdersUsed": True,
        "ordinaryBuildOrCIProbe": False,
        "floatingValuesCertified": False,
        "actualSupplyAtTheseFiniteOrdersCertified": False,
        "independentSignedCarrierBoundProved": False,
        "directOrFundedEnergyBoundProved": False,
        "floorProved": False,
        "cases": result,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--radius", type=Fraction, default=Fraction(10001, 20000))
    parser.add_argument("--height", type=float, default=54)
    parser.add_argument("--indices", type=int, nargs="+", default=list(range(5, 14)))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if any(j < 0 for j in args.indices):
        parser.error("indices must be nonnegative")
    report = experiment(args.radius, args.height, args.indices)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

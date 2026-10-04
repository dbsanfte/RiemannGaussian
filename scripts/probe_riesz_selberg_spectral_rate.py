#!/usr/bin/env python3
"""Rate gate for transferring Selberg/Banach cancellation to the floor.

No prime populations or zeta values are sampled. The probe distinguishes
fixed-test qualitative cancellation from a uniform moving-factorial bound.
Every contraction is a labelled scenario, not a proved arithmetic input.
Unknown constants are factored out, never certified as one.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path


def dec(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def number(value: Decimal) -> str:
    return format(value, ".26E")


def probe() -> dict:
    with localcontext() as context:
        context.prec = 90
        u = Fraction(10001, 20000)
        critical = u - Fraction(1, 2)
        critical_contraction = Fraction(1, 1) / (2 * u)
        orders = [65536, 196608, 1048576, 100000000]
        rows = []
        for delta in [Fraction(1, 1000000), critical, Fraction(1, 10000)]:
            # Exact Laplace/factorial identity, not a fixed T=2N substitute.
            ratio = u / (Fraction(1, 2) + delta)
            q = 1 / (1 + 2 * delta)
            assert ratio == 2 * u * q
            rows.append({
                "errorExponentScenario": str(delta),
                "actualPrimeErrorProvedByProbe": False,
                "radialRootContraction": str(q),
                "sourceNormalizedRate": str(ratio),
                "strictSourceDecayFromThisScenario": ratio < 1,
                "exactFactorialAverage": "(u/(1/2+delta))^(N+1)",
                "logFactorsOnly": [{"N": n, "logNormalizedFactor":
                                    number(Decimal(n + 1) * dec(ratio).ln())}
                                   for n in orders],
            })

        # Angular mean 2/pi is an unweighted phase-budget fact. We test the
        # proposed contraction ONLY as a scenario; the missing source-aware
        # algebra estimate is never imported as a hypothesis of a proof.
        pi = Decimal("3.141592653589793238462643383279502884197169399375105820974944592307816406286208998628")
        angular = 2 / pi
        growth = dec(2 * u).ln()
        contraction_rows = []
        for n in orders:
            linear_depth = Decimal(n)
            logarithmic_depth = Decimal(n + 1).ln() / 16
            contraction_rows.append({
                "N": n,
                "logFactorIfUniformContractionIteratedNtimes":
                number(Decimal(n + 1) * growth + linear_depth * angular.ln()),
                "logFactorAtLogN_over16Depth":
                number(Decimal(n + 1) * growth + logarithmic_depth * angular.ln()),
                "uniformMovingKernelContractionProved": False,
            })

        subexponential = []
        for c in [Decimal(1), Decimal(20), Decimal(200)]:
            subexponential.append({
                "coefficientScenario": number(c),
                "primeErrorEstimateAsserted": False,
                "kernelAllowanceEstimateAsserted": False,
                "comparisonOnly": "(2u)^(N+1)*exp(-c*sqrt(N+1))",
                "eventualExponentialGrowthFromThisFactor": True,
                "logFactorsOnly": [{"N": n, "logComparisonFactor":
                                    number(Decimal(n + 1) * growth - c * Decimal(n + 1).sqrt())}
                                   for n in orders],
            })

        assert critical == Fraction(1, 20000)
        assert critical_contraction == Fraction(10000, 10001)
        assert rows[1]["sourceNormalizedRate"] == "1"
        assert rows[2]["sourceNormalizedRate"] == "10001/10002"
        return {
            "schemaVersion": 1,
            "kind": "Selberg spectral-rate go/no-go; no prime or zeta sampling",
            "u": str(u), "criticalErrorExponent": str(critical),
            "requiredRadialRootContractionStrictlyBelow": str(critical_contraction),
            "fixedTestQualitativeDecayIsMovingFactorialControl": False,
            "exactFactorialPowerScenarios": rows,
            "angularContractionScenario": {
                "q": "2/pi", "sourceAwareSubmultiplicativityProved": False,
                "linearIterationDepthNeededForFixedExponentialRate": True,
                "comparison": contraction_rows,
            },
            "subexponentialScenarios": subexponential,
            "unknownArithmeticConstantsFactoredOut": True,
            "positiveBudgetFailureIsNoGoForSignedFloor": False,
            "newArithmeticBound": False, "newFloorSaving": False,
            "newZeroExclusion": False, "numericalProofUsed": False,
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/riesz-selberg-spectral-rate/rate-probe.json"))
    args = parser.parse_args()
    report = probe()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Wrote {args.output}; rate scenarios only.")
    print("Critical delta=1/20000; critical contraction=10000/10001.")
    print("No source-aware arithmetic contraction or floor saving proved.")


if __name__ == "__main__":
    main()

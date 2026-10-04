#!/usr/bin/env python3
"""Optional quantitative audit of the checked joined-radius estimate.

This computes bound factors, not literal-prime populations. Radius scenarios
are NOT certificates of zeta nonvanishing. Only the concrete radius and
log-height range explicitly identified below are instantiated in Lean.
Unknown height-dependent constants and entry orders are never set to one
when interpreting a result as a carrier bound.
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
    return format(value, ".24E")


def probe() -> dict:
    with localcontext() as context:
        context.prec = 90
        u = Fraction(10001, 20000)
        concrete_radius = Fraction(100011, 200000)
        radii = [
            Fraction(500001, 1000000),
            Fraction(50001, 100000),
            Fraction(20001, 40000),
            u,
            concrete_radius,
            Fraction(51, 100),
        ]
        orders = [65536, 262144, 1048576]
        rows = []
        for radius in radii:
            source_rate = u / radius
            relative_rate = Fraction(1, 1) / (2 * radius)
            rows.append(
                {
                    "radiusScenario": str(radius),
                    "sourceRateExact": str(source_rate),
                    "sourceRate": number(dec(source_rate)),
                    "relativeCreditRateExact": str(relative_rate),
                    "relativeCreditRate": number(dec(relative_rate)),
                    "sourceDecayFromThisBound": source_rate < 1,
                    "relativeCancellationFromThisBound": relative_rate < 1,
                    "actualRadiusCertifiedByThisProbe": False,
                    "factorsOnly": [
                        {
                            "N": order,
                            "sourceGeometricFactor": number(dec(source_rate) ** order),
                            "relativePolynomialGeometricFactor": number(
                                Decimal(order + 1) ** 3 * dec(relative_rate) ** order
                            ),
                        }
                        for order in orders
                    ],
                }
            )

        # Exact rational inequality used by the Lean concrete-height theorem.
        room = Fraction(792) - (concrete_radius - Fraction(1, 2)) * (
            7625 * 1800 - 2000
        )
        assert room > 0
        assert u / concrete_radius == Fraction(100010, 100011)

        # Already-proved exposed simple-mode source: a diagnostic, not an
        # independently proved arithmetic allowance or an actual prime probe.
        ud = dec(u)
        retained = dec(Fraction(32, 13)).ln() / (-2 * ud * ud.ln()) - dec(
            Fraction(19, 13)
        ).ln()
        source = 1 - retained
        threshold = dec(Fraction(399, 5000))

        return {
            "schemaVersion": 1,
            "kind": "joined-bound-factor audit; no prime sampling",
            "target": "Re prefixPairDefect <=399/5000+o(1)",
            "workingRadiusCeiling": str(u),
            "sameSignedMainAndExactCredit": True,
            "genericScenarios": rows,
            "concreteLeanInstantiation": {
                "radius": str(concrete_radius),
                "fixedHeightHypotheses": "54<=abs(y), log(abs(y)+3)<=1800",
                "remainingRationalDiskRoom": str(room),
                "uniformSourceRate": "100010/100011",
                "heightAlreadyExcludedByExistingRegion": True,
                "newZeroExclusion": False,
                "CauchyConstantNumericallyCertified": False,
                "entryOrderNumericallyCertified": False,
            },
            "selectedSourceRegression": {
                "retainedCostAtCeiling": number(retained),
                "pairSourceAtCeiling": number(source),
                "unchangedUpperTarget": number(threshold),
                "contradictionMarginNotMeasuredProgress": number(source - threshold),
                "radiusAtSelectedPole": str(u),
                "sourceRateAtThatRadius": "1",
                "relativeCancellationDoesNotImplyAbsoluteFloor": True,
            },
            "allHeightFloorProved": False,
            "numericsUsedAsLeanProof": False,
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(".lake/riesz-joined-phase-radius/rate-probe.json"),
    )
    args = parser.parse_args()
    report = probe()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Wrote {args.output}; bound factors only, no prime certificate.")
    print("Concrete source rate: 100010/100011; global relative rate: 1/(2R).")
    print("All-height absolute floor remains open; unknown constants retained.")


if __name__ == "__main__":
    main()

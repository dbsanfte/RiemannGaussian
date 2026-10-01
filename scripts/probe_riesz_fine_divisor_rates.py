#!/usr/bin/env python3
"""Optional scalar-rate exploration for the fine unsigned-divisor payment.

This is floating diagnostics only. It samples neither primes nor labels and
does not certify an arithmetic floor or a cofinal starting order. The Lean
module proves the exact rational rate inequalities and literal signed transfer.
"""

import json
import math


def report():
    u = 10001 / 20000
    growth = math.log(2 * u)
    tilt = 1 / 65536
    beta = 1 / 1000
    comparison = growth + 2.03 * tilt - beta / 4
    lattice = growth - beta
    radial = max(math.log(u * a) + 1 - a / 2 for a in (1.95, 2.03))
    return {
        "scope": "Floating scalar diagnostics, not a certificate or literal prime sum",
        "radius": u,
        "sourceGrowthExponent": growth,
        "summableTilt": tilt,
        "unsignedSlope": beta,
        "comparisonExponent": comparison,
        "latticeExponent": lattice,
        "roundedEndpointExponent": lattice,
        "provedRoundedEndpointExponentCeiling": -9 / 10000,
        "provedEndpointBudget": "18*(N+1)^3*exp(-9*N/10000)",
        "provedComparisonExponentCeiling": -1 / 10000,
        "radialExponent": radial,
        "minimumSlopeForThisScalarTilt": 4 * (growth + 2.03 * tilt),
        "oldFullWindowOuterCut": 1.85,
        "newFullWindowOuterCut": 1.95 - beta,
        "edgeBand": {
            "countingExponent": 17/32,
            "unsignedSlope": 1/2000,
            "outerCut": 3899/2000,
            "oldCountingExponentOnThisBand": growth+2.03*tilt-(1/2000)/4,
            "newComparisonExponent": growth+2.03*tilt-(1-17/32)/2000,
            "provedComparisonExponentCeiling": -1/10000,
            "latticeExponent": growth-1/2000,
            "provedEndpointBudget": "18*(N+1)^3*exp(-N/2500)",
        },
        "floorProvedByProbe": False,
        "startingOrderCertified": False,
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))

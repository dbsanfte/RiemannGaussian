#!/usr/bin/env python3
"""Optional multi-order signed detector; never actual prime/zero samples.

Collect each mode's factorial/logged order and integer multiplicity first.
Verify the exact positive-square identity before scanning phase geometry.
The resulting scalar cost is independently certified in Lean. Neither this
probe nor its parameter scan proves the remaining dense-cluster ceiling.
"""
from fractions import Fraction as F
import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 110
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".lake/riesz-ceiling-fejer-cluster/probe.json"
U, K, DEGREE, CLOUD_SIZE = F(10001, 20000), 1100, 8, 131072


def dec(x):
    if isinstance(x, F):
        return mp.mpf(x.numerator) / x.denominator
    return mp.mpf(x)


def fmt(x):
    return mp.nstr(x, 100)


def error(k):
    u, height = dec(U), mp.mpf(10)**150
    return u**k + 160*u*(height+4)*k*(10*u/7)**(k-1) + (height+11)*(4*u/3)**k


def cost(stride, degree):
    u = dec(U)
    return 2*sum((degree+1-j)*((2*u)**(stride*j)+error(stride*j))
                 for j in range(1, degree+1))


def mode_row(radius, turn):
    # turn is a fraction of a full turn at the joined stride, not at one
    # unlogged derivative order. There is no phase freezing or data transport.
    v = dec(radius)*mp.exp(2j*mp.pi*dec(turn)/K)
    w = v**K
    signed = 9+2*sum((9-j)*(w**j).real for j in range(1, 9))
    prefixes = [sum(w**j for j in range(n+1)) for n in range(9)]
    square = abs(prefixes[8])**2+(1-abs(w)**2)*sum(abs(g)**2 for g in prefixes[:8])
    assert abs(signed-square) < mp.mpf("1e-96")
    assert signed >= -mp.mpf("1e-96")
    return {"normalizedNodeRadius": str(radius), "stridePhaseTurns": str(turn),
            "multiplicity": 1, "completeLogPowers": [K*j for j in range(1, 9)],
            "individualSignedTerms": [fmt((w**j).real) for j in range(1, 9)],
            "collectedFejer": fmt(signed), "positiveSquare": fmt(square),
            "actualZero": False}


main_cost = cost(K, DEGREE)
assert main_cost < 107
exact_source_cap = 2*sum((9-j)*F(1117, 1000)**j for j in range(1, 9))
assert exact_source_cap < F(1069, 10)
assert exact_source_cap+F(72, 1000) < 107
assert all(error(K*j) < dec(F(1, 1000)) for j in range(1, 9))
assert F(10001, 10000)**100 <= F(10101, 10000)
assert F(10101, 10000)**11 <= F(1117, 1000)
assert F(10001, 14000)**100 <= F(1, 400000000000000)
assert F(10001, 14000)**99 <= F(1, 200000000000000)
assert F(10001, 15000)**100 <= F(1, 400000000000000000)

rows = [mode_row(radius, turn)
        for radius in [F(0), F(1, 2), F(99, 100), F(49999, 50000), F(1)]
        for turn in [F(0), F(1, 9), F(1, 4), F(1, 2), F(4, 9)]]
# The nonnegative kernel tolerates modes whose FIRST test contribution is
# almost -1. We do not replace those negative contributions by abs(cos).
opposing = next(q for q in rows if q["normalizedNodeRadius"] == "49999/50000"
                and q["stridePhaseTurns"] == "1/2")
assert dec(opposing["individualSignedTerms"][0]) < -dec(F(9, 10))
assert dec(opposing["collectedFejer"]) > 0

# Preserve the frozen dense-cloud no-go by its exact character identity.
# The selected-erased trace at each power is -2+2*M*u^k. Its Fejer kernel
# is positive, but the mass 2*(M-1) is far above the newly paid sector.
cloud_mass = 2*(CLOUD_SIZE-1)
cloud_joined = 9*cloud_mass+2*sum((9-j)*(-2+2*CLOUD_SIZE*dec(U)**(K*j))
                              for j in range(1, 9))
assert cloud_joined > 0 and cloud_mass > 4

scan = [{"stride": stride, "degree": degree,
         "wholeCost": fmt(cost(stride, degree)),
         "necessaryCompetingMassForDouble": fmt(
             (2*degree*(degree+1)-cost(stride, degree))/(degree+1))}
        for stride in [1050, 1080, 1100, 1120, 1200, 1500]
        for degree in range(3, 11)]

result = {
    "classification": "Exact multi-order signed Fejer control, with scalar geometry regressions",
    "parameters": {"radiusCeiling": str(U), "stride": K, "degree": DEGREE,
                   "momentOrders": [K*j-1 for j in range(1, 9)],
                   "heightUpper": "10^150", "sourceCoefficient": 72,
                   "massCoefficient": 9, "leanWholeCostUpper": 107},
    "exactArithmeticCost": fmt(main_cost),
    "exactRationalSourceCap": str(exact_source_cap),
    "remainderCosts": [fmt(error(K*j)) for j in range(1, 9)],
    "necessaryCompetingMassForDoubleAtNumericCost": fmt((144-main_cost)/9),
    "modeRows": rows, "opposingFirstOrderMode": opposing,
    "parameterScan": scan,
    "preservedDenseCloud": {"multiplicityPerNode": 2, "modeCount": CLOUD_SIZE,
                           "competingMass": cloud_mass, "characterIdentityUsed": True,
                           "joinedFejer": fmt(cloud_joined), "stillUnpaid": True},
    "actualArithmeticMomentUsedByLean": True,
    "actualDivisorMultiplicityUsedByLean": True,
    "geometryAndHeightHypothesesRetained": True,
    "separateOpposingPhaseDebits": False,
    "actualPrimeData": False, "actualZeroData": False,
    "nativeEntryOrderCertified": False, "fullAllHeightCeilingProved": False,
    "simpleZeroFloorProved": False, "zeroExclusionProved": False,
}
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps({"output": str(OUT.relative_to(ROOT)), "modeRows": len(rows),
                  "cost": fmt(main_cost), "newRequiredCompetingMass": 5,
                  "denseCloudStillUnpaid": True, "fullCeilingStillOpen": True}))

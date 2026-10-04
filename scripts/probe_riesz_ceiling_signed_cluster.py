#!/usr/bin/env python3
"""Optional signed phase regression, not samples of genuine zeros or primes.

All rows use the exact same logged power4097 and integer multiplicities.
Opposite phases are collected before taking a real part. The existing root
cloud is checked by exact character bookkeeping, never a cancelling float sum.
Outside ordinary builds and CI. Numerical rows establish no native entry order.
"""
from fractions import Fraction as F
import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 110
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".lake/riesz-ceiling-signed-cluster/probe.json"
U, R, K, M = F(10001, 20000), F(11, 20), 4097, 131072


def dec(value):
    if isinstance(value, F):
        return mp.mpf(value.numerator)/value.denominator
    return mp.mpf(value)


def fmt(value):
    return mp.nstr(value, 100)


def row(a, b):
    d = mp.mpc(dec(a), dec(b))
    value = (dec(U)/d)**K
    return {"denominatorReal": str(a), "denominatorImag": str(b), "multiplicity": 1,
            "loggedPower": K, "selectedRadius": str(U), "insideNearbyDisk": abs(d) <= dec(R),
            "exposedGeometry": abs(d) > dec(U), "normalizedPowerReal": fmt(value.real),
            "normalizedPowerImag": fmt(value.imag),
            "constructiveCone": K*abs(b) <= a,
            "actualZero": False}


rows = [row(a, b) for a in [F(25003, 50000), F(101, 200), F(13, 25)]
        for b in [F(0), F(1, 20000), F(1, 8194), F(1, 5000), F(6, 15625), F(3, 5000)]]
assert all(dec(q["normalizedPowerReal"]) >= 0 for q in rows if q["constructiveCone"])
first, second = row(F(25003, 50000), F(1, 20000)), row(F(25003, 50000), F(6, 15625))
mixed = dec(first["normalizedPowerReal"])+dec(second["normalizedPowerReal"])
assert dec(first["normalizedPowerReal"]) > 0 and dec(second["normalizedPowerReal"]) < 0
assert mixed > -mp.mpf(1)/5

# From the frozen character identity: total root trace=M*u^K. Remove the
# selected root and put the ||D||>R tail aside. Therefore the entire nearby
# competing profile is within this small error of -2. This regression remains
# UNPAID by the new theorem; it checks that the no-go has not been erased.
cloud_error = 2*M*(dec(U)**K+(dec(U)/dec(R))**K)
assert cloud_error < mp.mpf("1e-160")

result = {
    "classification": "Signed geometry probe of the new actual-cluster sector theorem",
    "parameters": {"sourceRadius": str(U), "nearbyRadius": str(R), "momentOrder": K-1,
                   "loggedPower": K, "negativeSignedBudget": "-1/5",
                   "uniformConstructiveOrdinateCone": "1/8194"},
    "modeRows": rows,
    "mixedSignedPacket": {"components": [first, second], "collectedReal": fmt(mixed),
                          "hasOpposingMode": True, "signedFloorSatisfied": True,
                          "noAbsoluteDebitIntroduced": True},
    "preservedCloudRegression": {
        "modeCount": M, "characterIdentityUsed": True,
        "nearbyCompetingCenter": "-2", "absoluteErrorUpper": fmt(cloud_error),
        "failsSignedFloor": True, "counterexampleIsSynthetic": True},
    "leanActualMultiplicityInequality": True,
    "leanAdditionalSectorCeiling": True,
    "heightCondition": "log(abs(y)+22)<=10^150",
    "geometryConditionsRemainExplicit": True,
    "actualZeroData": False, "actualPrimeData": False,
    "nativeEntryOrderCertified": False,
    "fullAllHeightCeilingProved": False, "simpleZeroFloorProved": False,
    "zeroExclusionProved": False,
    "limitations": [
        "Numerical positions are synthetic, not actual zero samples.",
        "The actual theorem proves a ceiling in additional signed sectors only.",
        "The negative signed floor for arbitrary opposing clusters is still open.",
        "The finite height condition must not be replaced by an all-height claim.",
        "The preserved root-cloud regression remains in the unpaid sector.",
        "A finite-order phase inequality cannot be combined with a cofinal phase limit.",
    ],
}
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps({"output": str(OUT.relative_to(ROOT)), "modeRows": len(rows),
                  "mixedSignedReal": fmt(mixed), "cloudStillUnpaid": True,
                  "fullCeilingStillOpen": True}))

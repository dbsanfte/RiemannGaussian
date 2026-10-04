#!/usr/bin/env python3
"""Optional exact-bookkeeping regression for the multi-order ceiling audit.

This is a synthetic finite local divisor, not prime or zeta-zero data.
Character orthogonality and the zero harmonic are collected BEFORE numerical
evaluation. The same joined evaluator's limiting value follows from Lean;
these samples do not certify a native entry order. Outside ordinary CI.
"""
from fractions import Fraction as F
import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 110
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".lake/riesz-ceiling-cluster-power-audit/probe.json"
M = 131072
U = F(10001, 20000)
u = mp.mpf(U.numerator) / U.denominator


def fmt(value):
    return mp.nstr(value, 100)


def power_row(k):
    # Exactly the harmonics divisible by M survive the root sum. Cancelling
    # the j=0 term against regularPower must precede evaluation; direct
    # floating summation of the root cloud loses this cancellation.
    indices = list(range(0, k+1, M))
    terms = [mp.binomial(k, j)*u**(k-j)*(1-u)**j for j in indices]
    singular = -2*M*sum(terms)
    regular = 2*M*u**k
    model = -2*M*sum(terms[1:])
    assert not terms[1:] or abs(singular+regular-model) <= mp.mpf("1e-95")*abs(model)
    return {"loggedPower": k, "momentOrder": k-1, "retainedHarmonics": indices,
            "modelExactlyZero": k < M, "rawSingular": fmt(singular),
            "regularCorrection": fmt(regular), "collectedModel": fmt(model),
            "completeRealAxisPoleMajorant": fmt((2*u)**k)}


blocks = [
    {"base": "10001/10000", "power": 256, "relation": ">=", "bound": "641/625"},
    {"base": "641/625", "power": 512, "relation": ">=", "bound": str(3*M)},
]
for row in blocks:
    base, bound = F(row["base"]), F(row["bound"])
    assert base**row["power"] >= bound
    row["numericalValue"] = fmt((mp.mpf(base.numerator)/base.denominator)**row["power"])
    row["exactRationalComparison"] = True


def node(i):
    return u+(1-u)*mp.exp(2j*mp.pi*i/M)


def geometry(i):
    v = node(i)
    d = u/v
    beta = mp.mpf("1.5")-d.real
    return {"index": i, "normalizedModeNorm": fmt(abs(v)),
            "denominatorReal": fmt(d.real), "denominatorImag": fmt(d.imag),
            "denominatorNorm": fmt(abs(d)), "syntheticBeta": fmt(beta),
            "insideLocalDisk": abs(d) < mp.mpf(4)/5,
            "residue": -2, "actualZetaZero": False}


# The local boundary is monotone in angle on the first half circle. Compute
# a candidate and check both adjacent nodes, rather than a float class scan.
c = ((5*u/4)**2-u**2-(1-u)**2)/(2*u*(1-u))
first_out = int(mp.ceil(M*mp.acos(c)/(2*mp.pi)))
assert abs(node(first_out-1)) > 5*u/4
assert abs(node(first_out)) < 5*u/4
local_count = 1+2*(first_out-1)

retained_cost = mp.log(mp.mpf(32)/13)/(-2*u*mp.log(u))-mp.log(mp.mpf(19)/13)
joined_limit = -2+4*retained_cost
assert joined_limit > mp.mpf(42)/25

data = {
    "classification": "Exact integer-mode/local-analytic countermodel for a method, not for zeta",
    "parameters": {"modeCount": M, "sourceRadius": str(U), "selectedResidue": -2,
                   "localPhysicalRadius": "4/5", "regularCoefficientRadius": "4/3"},
    "exactBookkeeping": {
        "rootTrace": "M*sum_{j divisible by M, 0<=j<=k} choose(k,j)*u^(k-j)*(1-u)^j",
        "regularCorrection": "2*M*u^k",
        "model": "-2*M*sum_{0<j<=k, M divides j} choose(k,j)*u^(k-j)*(1-u)^j",
        "firstPotentialNonzeroMomentOrder": M-1,
        "ordersZeroAndOneRetained": True,
        "fractionalResiduesUsed": False,
    },
    "exactBlockCertificates": blocks,
    "powerRows": [power_row(k) for k in [1, 2, 18, 256, 640, 1536, 4097, 8192,
                                          65536, M-1, M, 2*M, 4*M, 8*M]],
    "geometryRows": [geometry(i) for i in [0, 1, 2, 100, 10000,
                                           first_out-1, first_out, M-1]],
    "localPopulation": {"firstOmittedPositiveIndex": first_out,
                        "localModeCount": local_count,
                        "localMultiplicityMass": 2*local_count,
                        "boundaryAdjacentNodesChecked": True},
    "nearestCompetingDenominatorGap": fmt(abs(u/node(1))-u),
    "nearestCompetingEigenvalueGap": fmt(1-abs(node(1))),
    "sameJoinedLimit": fmt(joined_limit),
    "ceiling": "42/25",
    "leanAllOrdersMajorantProved": True,
    "leanLocalRegularHasSumProved": True,
    "leanSameJoinedViolationProved": True,
    "actualPrimeData": False,
    "actualZeroData": False,
    "actualZetaRemainderIdentified": False,
    "globalAllNegativeActualDivisorCounterexample": False,
    "nativeEntryOrderCertified": False,
    "fullCeilingProved": False,
    "arithmeticCeilingCredit": "0",
    "limitations": [
        "Synthetic coordinates in the genuine-zero strip are not genuine zeros.",
        "The regular correction has a synthetic positive pole outside the local disk.",
        "A free local analytic remainder is not the actual completed-xi remainder.",
        "No Euler product, complete prime measure or functional equation is asserted.",
        "The local cardinality is an optional numerical diagnostic, not a Lean count theorem.",
        "The exact joined limit is a model source, not a measured unpaid arithmetic mass.",
    ],
}
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(json.dumps(data, indent=2)+"\n")
print(json.dumps({"output": str(OUT.relative_to(ROOT)), "source": data["sameJoinedLimit"],
                  "localModes": local_count, "firstNonzeroOrder": M-1,
                  "actualZetaCounterexample": False, "fullCeilingStillOpen": True}))

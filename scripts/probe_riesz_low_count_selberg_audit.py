#!/usr/bin/env python3
"""Exact rational coefficient checks for the joined Selberg completion audit.

This probes the balanced boxes at native-sized orders, using the PROVED
interval for the actual moving length rather than pretending to enumerate
astronomically large primes. It is not an arithmetic/phase certificate.
The exponential envelope is an UNSIGNED diagnostic, never a floor budget.
"""

import argparse
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path


def encoded(x):
    return {"numerator": x.numerator, "denominator": x.denominator,
            "float": float(x)}


def case(N):
    corners = []
    for x in [F(N), F(N+1)]:
        for y in [F(N+1), F(N+2)]:
            for L in [F(277,200)*N, F(7,5)*N]:
                T = x+y
                literal = -T*(T-L)/L
                selberg = -2*x*y/T
                delta = literal-selberg
                assert delta >= F(N,20)
                corners.append({"xMinusN": encoded(x-N),
                                "yMinusN": encoded(y-N),
                                "LOverN": encoded(L/N),
                                "literalOverT": encoded(literal/T),
                                "selbergOverT": encoded(selberg/T),
                                "defectOverN": encoded(delta/N)})
    u = F(10001,20000)
    # The formal theorem gives this lower envelope for the defect's price.
    log_envelope = math.log(float(u))-4.5-math.log(216)
    log_envelope += N*math.log(float(2*u))-3*math.log(N+1)
    return {"N": N, "rationalCornerCases": corners,
            "provedCoefficientLower": encoded(F(N,20)),
            "minimumCornerDefectOverN": min(x["defectOverN"]["float"] for x in corners),
            "log10UnsignedLowerEnvelope": log_envelope/math.log(10)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    cases = [case(N) for N in [65536,90112,196608,500000,1000000]]
    root = Path(__file__).resolve().parents[1]
    paths = [Path(__file__), root/"RiemannGaussian/ZetaRieszLowCountSelbergAudit.lean"]
    report = {"cases": cases,
              "exactRationalCases": sum(len(row["rationalCornerCases"]) for row in cases),
              "actualMovingLengthBracket": "277*N/200 <= L <= 7*N/5",
              "sourceGrowthRate": math.log(10001/10000),
              "primeNormalizedCoefficient": "-log p",
              "pairSelbergCoefficient": "-2 log p log q / log(pq)",
              "unmatchedPairCoefficient": "-log(pq)*(log(pq)-L)/L",
              "literalPrimeEnumeration": False,
              "phaseCancellationTested": False,
              "signedFloorProved": False,
              "scope": "Only tests Selberg completion followed by an absolute defect payment.",
              "sourcePins": [{"path": str(path.relative_to(root)),
                              "sha256": hashlib.sha256(path.read_bytes()).hexdigest()} for path in paths]}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"exactRationalCases": report["exactRationalCases"],
                      "minimumDefectOverN": min(row["minimumCornerDefectOverN"] for row in cases),
                      "sourceGrowthRate": report["sourceGrowthRate"],
                      "noSignedFloor": True}))


if __name__ == "__main__":
    main()

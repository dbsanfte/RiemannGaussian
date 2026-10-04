#!/usr/bin/env python3
"""Optional algebra-first audit of the full prime-cofactor completion gate.

Actual finite pairs are checked BEFORE interpreting any phase statistics.
They are introduced completion heads, not samples of the native count>=3
core. Their fixed-label factorial kernels decay; no cofinal arithmetic
source is inferred from these finite rows. The retained-pair source scalars
are separate controls for the existing exposed-zero theorem.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

from flint import acb, arb, ctx


def record(v: arb) -> dict:
    m, r = v.mid().man_exp(), v.rad().man_exp()
    return {"ball": v.str(85), "mid": [str(m[0]), int(m[1])],
            "rad": [str(r[0]), int(r[1])]}


def hinge(v: arb) -> arb:
    if v > 0:
        return v
    if v < 0:
        return arb(0)
    raise AssertionError("Ambiguous hinge boundary in strict interior control")


def rectangle_head_slots(N: int) -> list[tuple[int, int]]:
    # A two-prime pi-antidiagonal has j+h=N+1. All other orders are zero.
    # The original rectangle's displayed conditions suffice to reject it;
    # no replacement of ownerOrders by an approximate band is needed.
    return [(j, N+1-j) for j in range(N+2)
            if 21*N <= 40*j <= 23*N and N <= 100*(N+2-j) <= 4*N]


def prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n)+1))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/riesz-ceiling-head-completion-audit/probe.json"))
    args = parser.parse_args()
    ctx.prec = 360
    orders = (0, 1, 8, 101, 256, 640, 1536, 4096, 8192)
    pairs = ((7, 5), (13, 11), (101, 97), (1013, 1009))
    heights = (0, 54, 142, 1000000)
    rows = []
    assert all(not rectangle_head_slots(N) for N in orders)
    for p, q in pairs:
        assert prime(p) and prime(q) and p > q
        x, z = arb(p).log(), arb(q).log()
        T, L = x+z, x+z/2
        # Original eligibility EXCLUDES a prime cofactor at each incidence,
        # even when BOTH primes are in the physical prime selection.
        assigned = {str(A): 0 for A in ((), (p,), (q,), (p, q))}
        first = hinge(L-x)-hinge(L-x-z)-(hinge(L)-hinge(L-z))
        second = hinge(L-z)-hinge(L-z-x)-(hinge(L)-hinge(L-x))
        response = hinge(L)-hinge(L-x)-hinge(L-z)+hinge(L-x-z)
        assert first.overlaps(second) and first.overlaps(L-T)
        assert first < 0 and response > 0
        # Both incidence signs AGREE; multiplying by a common product phase
        # cannot turn them into opposite algebraic coefficients.
        coefficient = -T*response/L
        expected_norm_coefficient = T*(T-L)/L
        assert coefficient < 0 and (-coefficient).overlaps(expected_norm_coefficient)
        for N in orders:
            amplitude = expected_norm_coefficient*T**N/arb(math.factorial(N))*(-arb(3)/2*T).exp()
            assert amplitude > 0
            for height in heights:
                atom = coefficient*acb(T**N/arb(math.factorial(N)))*(
                    -acb(arb(3)/2, arb(height))*T).exp()
                assert abs(atom).overlaps(amplitude)
                rows.append({"p": p, "q": q, "N": N, "height": height,
                             "movingLength": False, "testLength": record(L),
                             "assignedShareByPhysicalSelection": assigned,
                             "markedRectangleMass": 0, "fullComplementMass": 1,
                             "firstHinge": record(first), "secondHinge": record(second),
                             "atomRe": record(atom.real), "atomIm": record(atom.imag),
                             "exactNorm": record(amplitude),
                             "nativeCoreMember": False})
    u = arb(10001)/20000
    c = (arb(32)/13).log()/(-2*u*u.log())-(arb(19)/13).log()
    scalar_rows = []
    for m in (1, 2, 3, 4):
        correction = m*m*(1-c)
        joined = -m+m*m*c
        completed_trace = arb(m*m-m)
        assert (joined+correction).overlaps(completed_trace)
        assert correction > arb(399)/5000
        if m >= 2:
            assert correction > arb(319)/1000 and joined > arb(42)/25
        scalar_rows.append({"multiplicity": m, "retainedPairSource": record(correction),
                            "joinedSource": record(joined), "completedTrace": record(completed_trace)})
    result = {"schemaVersion": 1, "precisionBits": 360,
              "classification": "failed full-factorial head completion gate",
              "algebraBeforeStatistics": True,
              "primeRows": rows, "sourceScalarRows": scalar_rows,
              "sourceScalarsAreExistingConditionalTheoremControls": True,
              "nativeCoreEnumerated": False, "actualZeroSamples": 0,
              "finitePairRowsHaveNoCofinalSourceClaim": True,
              "hypotheticalCompletedEulerQuotientIdentifiedWithNativeCarrier": False,
              "fullConstantCeilingProved": False, "newGlobalCeilingCredit": 0,
              "newZeroExclusion": False,
              "routeVerdict": "Stop: rectangle-zero head does not transfer to full mass.",
              "remaining": "An independent signed estimate for the actual retained joint prime aggregate."}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")


if __name__ == "__main__":
    main()

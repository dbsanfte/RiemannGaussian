#!/usr/bin/env python3
"""Shared-row phase/PSD regression. Diagnostic only, no Lean proof input.

Integer traces and symbolic quadratic ledgers use exact rationals. The
fixed-height samples use floating complex phases and are labelled separately.
They are not samples of hypothetical zeros or asymptotic evidence.
"""

from fractions import Fraction as F
from math import log
from pathlib import Path
import cmath
import json

from probe_arithmetic_operator_cross_cancellation import primes, row_data, direct_row


def add(z, w):
    return z[0] + w[0], z[1] + w[1]


def mul(z, w):
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def conjugate(z):
    return z[0], -z[1]


def main():
    ps = primes(251)
    direct_count = 0
    for p in ps:
        trace, _ = row_data(p, p, p * p)
        assert trace == 1
        if p <= 31:
            assert direct_row(p, p, p * p) == 1
            direct_count += 1

    # Preserve all component products until after the exact finite join.
    # Formal results use the ACTUAL log(p) and fixed-height phase instead.
    Q = [3, 5, 7, 11, 13]
    rows = {(p, q): row_data(p, q, p * q)[0] for p in Q for q in Q}
    profiles = [
        {p: (F(1), F(0)) for p in Q},
        {p: (F((-1) ** i), F(0)) for i, p in enumerate(Q)},
        {p: (F(i + 1, 3), F((-1) ** i, 5)) for i, p in enumerate(Q)},
    ]
    ledger_count = 0
    for a in profiles:
        for phase_style in range(4):
            # Symmetric rational phases are symbolic bookkeeping probes.
            def kernel(p, q):
                phase = [(F(1), F(0)), (F(0), F(1)),
                         (F(-1), F(0)), (F(0), F(-1))][(p * q + phase_style) % 4]
                return rows[p, q] * phase[0], rows[p, q] * phase[1]
            full, diagonal, off = (F(0), F(0)), (F(0), F(0)), (F(0), F(0))
            for p in Q:
                for q in Q:
                    value = mul(mul(a[p], conjugate(a[q])), kernel(p, q))
                    full = add(full, value)
                    if p == q:
                        diagonal = add(diagonal, value)
                    else:
                        off = add(off, value)
            assert full == add(diagonal, off)
            ledger_count += 1

    height_samples = []
    for y in (54, 65, 100):
        negative = []
        for p in ps:
            value = log(p) ** 2 * cmath.exp(-1j * y * log(p * p))
            if value.real < 0:
                negative.append({"prime": p, "diagonalReal": value.real})
        assert negative
        height_samples.append({"height": y, "negativeDiagonalCount": len(negative),
                               "firstExamples": negative[:3]})

    pair_samples = []
    for p, q in ((53, 29), (61, 17), (19, 7)):
        trace, _ = row_data(p, q, p * q)
        coefficient = log(p) * log(q) * cmath.exp(-1j * 54 * log(p * q)) * float(trace)
        plus, minus = 2 * coefficient.real, -2 * coefficient.real
        assert min(plus, minus) < 0
        pair_samples.append({"p": p, "q": q, "sameParity": p % 4 == q % 4,
                             "exactTrace": str(trace), "height": 54,
                             "zeroDiagonalPlusReal": plus, "zeroDiagonalMinusReal": minus})

    report = {
        "checksPassed": True, "proofInput": False,
        "exactArithmetic": "actual integer binomial rows and rational quadratic component ledgers",
        "exactSquareRowDiagonals": len(ps), "directIntegerSquareRows": direct_count,
        "exactSymbolicQuadraticLedgers": ledger_count,
        "symbolicPhasesAreNotActualHeightPhases": True,
        "actualHeightRetainedByLean": True,
        "floatingHeightSamples": height_samples,
        "floatingSameParityTwoVectorSamples": pair_samples,
        "floatingSamplesAreNotZeroOrAsymptoticProofs": True,
        "unphasedGlobalPSDClaimed": False,
        "distinctPrimeSourceResponseEstablished": False,
        "nativeIntegerPrimeIndexedPhasedPSDGates": "whole unit-diagonal PSD false beyond every head; complete diagonal deletion plus unrestricted positivity forces the whole joined real part to zero",
        "changedDiagonalOrPrescribedSignedPacketsClosed": False,
    }
    path = Path(".lake/arithmetic-operator-cross-psd/probe.json")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if not k.startswith("floating")}, indent=2))


if __name__ == "__main__":
    main()

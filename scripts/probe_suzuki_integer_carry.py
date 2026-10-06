#!/usr/bin/env python3
"""Optional integer-carry probe; no certificate or Suzuki floor is claimed.

Keep the literal prime-power incidences joined, compare with the exact
binomial constraint, then test spectral sensitivity. In particular a
small Mellin symbol at a genuine zero is not arithmetic non-coherence.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np


def prime_power_bases(limit):
    prime = np.ones(limit + 1, dtype=bool)
    prime[:2] = False
    for p in range(2, math.isqrt(limit) + 1):
        if prime[p]:
            prime[p * p :: p] = False
    primes = np.flatnonzero(prime)
    bases = np.zeros(limit + 1, dtype=np.int64)
    bases[primes] = primes
    for p in primes[: np.searchsorted(primes, math.isqrt(limit), side="right")]:
        q = int(p) ** 2
        while q <= limit:
            bases[q] = p
            q *= int(p)
    return bases


def literal_row(N, bases):
    ds = np.arange(1, 2 * (N + 1) + 1, dtype=np.int64)
    here = 2 * N // ds - 2 * (N // ds)
    after = 2 * (N + 1) // ds - 2 * ((N + 1) // ds)
    delta = after - here
    prime_power = bases[ds] > 0
    logs = np.log(bases[ds[prime_power]].astype(np.longdouble))
    observed = np.sum(here[prime_power] * logs, dtype=np.longdouble)
    active = ds[(delta != 0) & prime_power]
    signed = mp.fsum(int(delta[d - 1]) * mp.log(int(bases[d])) for d in active)
    unjoined = mp.fsum(abs(int(delta[d - 1])) * mp.log(int(bases[d])) for d in active)
    expected = mp.log(4) - mp.log1p(1 / mp.mpf(2 * N + 1))
    exact_total = mp.loggamma(2 * N + 1) - 2 * mp.loggamma(N + 1)
    if abs(signed - expected) > mp.mpf("1e-65"):
        raise AssertionError("literal prime factors disagree with binomial recurrence")
    if not np.all((here == 0) | (here == 1)):
        raise AssertionError("integer binary carry is not binary")
    return {
        "N": N,
        "literalPrimePowerSupport": len(active),
        "joinedSignedAdjacentSum": float(signed),
        "exactAdjacentDefect": float(mp.log(4) - signed),
        "defectLowerBound": float(1 / mp.mpf(2 * N + 2)),
        "defectUpperBound": float(1 / mp.mpf(2 * N + 1)),
        "unjoinedAbsolutePrimeIncidences": float(unjoined),
        "recurrenceResidualHighPrecision": mp.nstr(abs(signed - expected), 8),
        "totalCarrySum": float(observed),
        "totalIdentityResidualFloating": float(abs(mp.mpf(str(observed)) - exact_total)),
        "integerCarryDefect": float(N * mp.log(4) - exact_total),
        "totalDefectUpperBound": float(mp.log(2 * N + 1)),
    }


def mode_row(beta, height, name):
    s = mp.mpc(beta, height)
    symbol = (mp.power(2, s) - 2) * mp.zeta(s) / s
    rows = []
    for M in (32, 256, 2048, 16384, 131072):
        n = np.arange(M, dtype=np.float64)
        rho = complex(s)
        terms = (np.exp(rho * np.log(2 / (2 * n + 1)))
                 - np.exp(rho * np.log(1 / (n + 1)))) / rho
        partial = complex(np.sum(terms))
        rows.append({"cells": M, "absolutePartialTransform": abs(partial),
                     "errorToExactSymbolFloating": abs(partial - complex(symbol))})
    return {
        "kind": name,
        "beta": float(beta), "height": float(height),
        "zetaAbsoluteValueHighPrecision": mp.nstr(abs(mp.zeta(s)), 12),
        "exactCarrySymbolReal": mp.nstr(symbol.real, 16),
        "exactCarrySymbolImaginary": mp.nstr(symbol.imag, 16),
        "absoluteCarrySymbol": mp.nstr(abs(symbol), 12),
        "cellTransformReplay": rows,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--maximum-n", type=int, default=1 << 18)
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/suzuki-integer-carry/probe.json"))
    args = parser.parse_args()
    if args.maximum_n < 8192:
        parser.error("maximum-n must be at least 8192")
    mp.mp.dps = 80
    limit = 2 * (args.maximum_n + 1)
    bases = prime_power_bases(limit)
    if tuple(bases[[1, 2, 4, 8, 9, 12, 27, 64]]) != (0, 2, 2, 2, 3, 0, 3, 2):
        raise AssertionError("prime-power base construction failed replay")
    cutoffs = sorted({1, 2, 3, 256, 640, 1536, 4096, 8192, args.maximum_n})
    cutoffs = [n for n in cutoffs if n <= args.maximum_n]
    report = {
        "scope": "optional numerical research replay, not a certificate",
        "arithmeticPrimePowersRetained": True,
        "joinedBeforeAbsoluteValues": True,
        "primePowerBasesSHA256": hashlib.sha256(bases.astype("<i8").tobytes()).hexdigest(),
        "maximumLiteralInteger": limit,
        "literalRows": [literal_row(N, bases) for N in cutoffs],
        "spectralSensitivity": [
            mode_row(mp.mpf("0.9"), 60, "synthetic density-control mode, not a zeta zero"),
            mode_row(mp.mpf("0.99995"), 60, "synthetic density-control mode, not a zeta zero"),
            mode_row(mp.mpf("0.5"), mp.zetazero(1).imag,
                     "known critical zero, numerical symbol-null control"),
        ],
        "newSuzukiFloor": False,
        "newZeroFreeRegion": False,
        "outwardRounded": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"output": str(args.output), "lastLiteralRow": report["literalRows"][-1],
                      "modeSymbolMagnitudes": [r["absoluteCarrySymbol"]
                                               for r in report["spectralSensitivity"]]}, indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Actual finite Schur-row regression; floating phases are diagnostic only.

Integer prime/coprimality/cutoff checks and exact polynomial constraint joins
are separated from floating native phase/matrix checks. No floating result
supplies Lean proof input, a PNT rate, a zero source, or an RH inequality.
"""
from __future__ import annotations

import argparse
import bisect
import cmath
import json
import math
from pathlib import Path


def primes_to(ceiling: int) -> list[int]:
    sieve = bytearray(b"\1") * (ceiling + 1)
    sieve[:2] = b"\0\0"
    for p in range(2, math.isqrt(ceiling) + 1):
        if sieve[p]:
            start = p * p
            sieve[start::p] = b"\0" * ((ceiling - start) // p + 1)
    return [p for p in range(2, ceiling + 1) if sieve[p]]


def phase(y: float, n: int) -> complex:
    return cmath.exp(-1j * y * math.log(n))


def native_diagonal(y: float, p: int, q: int) -> complex:
    # Entire literal divisor fiber 1,p,q,pq, including its diagonal credit.
    return 2 * (1 - phase(y, p) - phase(y, q) + phase(y, p * q))


def finite_constraint_vector(r: int) -> list[int]:
    # Density and r index-polynomial profiles, exact before reading the phase.
    a = [(-1)**i * math.comb(r + 1, i) for i in range(r + 2)]
    for power in range(r + 1):
        assert sum(a[i] * i**power for i in range(len(a))) == 0
    return a


def probe(ceiling: int) -> dict:
    primes = primes_to(ceiling)
    exact_coprime_checks = exact_constraints = literal_rows = 0
    float_diagonal_checks = float_quadratic_checks = 0
    max_phase_residual = 0.0
    cases = []
    for y in (54.0, -54.0, 65.0, 100.0, 350.0):
        width = math.exp(1 / (4 * abs(y)))
        for target in (100_000, 300_000, 800_000, 1_700_000):
            J = math.floor((abs(y) * math.log(target) - 0.25) / (2 * math.pi))
            x = math.exp((J * 2 * math.pi + 0.25) / abs(y))
            upper = width * x
            assert upper < ceiling
            ps = primes[bisect.bisect_right(primes, x):bisect.bisect_right(primes, upper)]
            rows = [(ps[i], ps[i + 1]) for i in range(0, len(ps) - 1, 2)]
            labels = [p * q for p, q in rows]
            X = math.ceil(upper)**2
            assert len(set(labels)) == len(labels)
            for p, q in rows:
                assert p != q and math.gcd(p, q) == 1
                assert 1 < p * q <= X
                # Phase interval boundaries are floating, explicitly not certified.
                for leg in (p, q):
                    angle = abs(y) * math.log(leg) - J * 2 * math.pi
                    assert 0.25 - 1e-10 <= angle <= 0.5 + 1e-10
            for i, n in enumerate(labels):
                for m in labels[i + 1:]:
                    assert math.gcd(n, m) == 1
                    exact_coprime_checks += 1
            ds = [native_diagonal(y, p, q) for p, q in rows]
            for (p, q), d in zip(rows, ds):
                factorized = 2 * (1 - phase(y, p)) * (1 - phase(y, q))
                max_phase_residual = max(max_phase_residual, abs(d - factorized))
                assert abs(d - factorized) < 2e-10
                assert d.real <= -1 / 25 + 1e-10
                float_diagonal_checks += 1
            tests = []
            for r in (0, 1, 2, 4, 8):
                if r + 2 > len(rows):
                    continue
                a = finite_constraint_vector(r)
                exact_constraints += r + 1
                mass = sum(v * v for v in a)
                # Positive identity and constant Schur matrices, actual phases retained.
                identity = sum(v*v*d for v, d in zip(a, ds)) / mass
                constant = sum(v*v*(d-1) for v, d in zip(a, ds)) / mass
                assert identity.real < -1 / 25 + 1e-10
                assert constant.real < -26 / 25 + 1e-10
                # A positive Gaussian Schur factor with a unit diagonal.
                logs = [math.log(n) for n in labels[:len(a)]]
                span = max(logs[-1] - logs[0], 1e-12)
                quadratic = 0j
                for i, ai in enumerate(a):
                    for j, aj in enumerate(a):
                        if i == j:
                            entry = ds[i]
                        else:
                            entry = complex(math.exp(-((logs[i]-logs[j])/span)**2))
                        quadratic += ai * aj * entry
                gaussian = quadratic / mass
                assert gaussian.real < 0
                float_quadratic_checks += 3
                tests.append({"r": r, "exactDensityAndProfiles": r + 1,
                              "identityReal": identity.real,
                              "constantReal": constant.real,
                              "gaussianReal": gaussian.real})
            literal_rows += len(rows)
            cases.append({"diagnosticHeight": y, "J": J, "bandStart": x,
                          "bandEnd": upper, "nativeIntegerCutoff": X,
                          "primeCount": len(ps), "disjointSquarefreeRows": len(rows),
                          "largestNativeDiagonalReal": max(d.real for d in ds),
                          "traceBudgetSufficientR": max((len(rows)-1)//26-1, -1),
                          "profileTests": tests})
    return {
        "scope": "actual finite native negative rows and growing projection-budget regression",
        "proofInput": False, "checksPassed": True,
        "integerPrimeCeiling": ceiling, "ordinaryPrimeCount": len(primes),
        "exact": {"literalSemiprimeRows": literal_rows,
                  "pairwiseCoprimeChecks": exact_coprime_checks,
                  "densityAndPolynomialConstraintJoins": exact_constraints,
                  "unitEndpointsRetainedInNativeDivisorFiber": True},
        "floatingDiagnosticOnly": {"diagonalChecks": float_diagonal_checks,
                                   "joinedQuadraticChecks": float_quadratic_checks,
                                   "maximumDivisorFactorizationResidual": max_phase_residual,
                                   "cases": cases},
        "growthOrSourceInferredFromNumerics": False,
        "nativePNTPrimeLocationTheoremUsedAsSignedPayment": False,
        "actualZeroModeResponseOrRHBoundClaimed": False,
        "scopeNotRuledOut": ["prescribed signed packet", "large-codimension projection",
                              "nonunit diagonal repair", "other operator interactions"]
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ceiling", type=int, default=2_000_000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = probe(args.ceiling)
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    print(json.dumps({"checksPassed": result["checksPassed"], "exact": result["exact"],
                      "floatingDiagonalChecks": result["floatingDiagnosticOnly"]["diagonalChecks"],
                      "floatingQuadraticChecks": result["floatingDiagnosticOnly"]["joinedQuadraticChecks"],
                      "proofInput": False}))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Diagnostic-only literal prefix GCD/source-collapse regression.

Integer and rational ledgers are exact. Floating height responses are
diagnostics, never proof input or claims about actual zeros/asymptotics.
"""
import cmath
import json
import math
from fractions import Fraction
from pathlib import Path


def prime_basis(n):
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def lambda_basis(n):
    f = prime_basis(n)
    return {next(iter(f)): 1} if len(f) == 1 else {}


def add_scaled(out, basis, scale):
    for p, e in basis.items():
        out[p] = out.get(p, Fraction(0)) + scale * e
        if out[p] == 0:
            del out[p]


def main():
    rows = 256
    checks = 0
    coefficients = {}
    ratios = 0
    for n in range(1, rows + 1):
        g, l = 0, 1
        for h in range(1, n + 2):
            g = math.gcd(g, math.comb(n, h) if h <= n else 0)
            l = math.lcm(l, h)
            assert g == n // math.gcd(n, l)
            tail = {}
            for d in range(1, n + 1):
                if n % d == 0 and d > h:
                    add_scaled(tail, lambda_basis(d), Fraction(1))
            assert prime_basis(g) == tail
            coefficients[n, h] = tail
            checks += 1
        for j in range(2, 10):
            if n < j:
                continue
            rhs = {}
            for e in range(1, j):
                if n % e == 0:
                    add_scaled(rhs, lambda_basis(n // e), Fraction(1))
            assert coefficients[n, n // j] == rhs
            ratios += 1

    ledgers = 0
    for seed in range(16):
        left, right = {}, {}
        for n in range(3, rows + 1):
            h = 1 + ((n * (seed + 3) + seed * seed) % n)
            weight = Fraction(((n * 17 + seed * 13) % 31) - 15, seed + 1)
            add_scaled(left, coefficients[n, h], weight)
            for d in range(1, n + 1):
                if n % d == 0 and d > h:
                    add_scaled(right, lambda_basis(d), weight)
        assert left == right
        ledgers += 1

    floating = []
    for y in (54, 65, 100):
        for beta in (0.5, 0.625, 0.75, 0.875):
            rho = beta + 1j * y
            multiplier = 1 + cmath.exp(-rho * math.log(2))
            floating.append({"height": y, "candidateRealPart": beta,
                             "multiplierNorm": abs(multiplier),
                             "provedLowerBoundTarget": 1 - 2 ** (-beta)})
    out = {
        "checksPassed": True, "proofInput": False,
        "integerRows": rows, "exactPrefixesIncludingUnitEndpoint": checks,
        "allProperPowersRetained": True,
        "exactLogPrimeBasisTailChecks": checks,
        "exactRelativeCutoffCofactorChecks": ratios,
        "symbolicRationalMovingMaskLedgers": ledgers,
        "rationalMasksAreNotActualHeightPhases": True,
        "floatingCandidateSourceFactors": floating,
        "newZeroAsymptoticOrRHClaimed": False,
        "scope": "all literal nonempty prefixes; log GCD equals truncated full Mangoldt divisor sum",
    }
    folder = Path(".lake/arithmetic-operator-kummer-prefix")
    folder.mkdir(parents=True, exist_ok=True)
    (folder / "probe.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({k: v for k, v in out.items() if k != "floatingCandidateSourceFactors"}))


if __name__ == "__main__":
    main()

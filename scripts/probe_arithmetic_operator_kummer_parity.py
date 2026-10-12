#!/usr/bin/env python3
"""Diagnostic-only exact even-binomial / all-power source-collapse audit.

Integer GCDs, carry witnesses and rational ledgers are exact. Floating
height factors are NOT proof input, actual-zero data, or an asymptotic
for the unmarked whole GCD / simultaneous two-prime packet.
"""
import cmath
import json
import math
from fractions import Fraction
from pathlib import Path


def primes_upto(x):
    return [p for p in range(2, x + 1)
            if all(p % d for d in range(2, math.isqrt(p) + 1))]


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


def two_powers(p, n):
    powers = []
    a = 1
    while a <= n:
        powers.append(a)
        a *= p
    return [(i, j) for j, b in enumerate(powers)
            for i, a in enumerate(powers[:j + 1]) if a + b == n]


def add_scaled(out, p, scale):
    out[p] = out.get(p, Fraction(0)) + scale
    if out[p] == 0:
        del out[p]


def main():
    ceiling = 512
    primes = primes_upto(ceiling)
    coefficients = {}
    valuation_checks = large_checks = proper = carry_checks = 0
    pair_checks = 0
    packet_examples = []
    for n in range(4, ceiling + 1, 2):
        g = 0
        for k in range(2, n, 2):
            g = math.gcd(g, math.comb(n, k))
        actual = prime_basis(g)
        expected = {}
        for p in primes:
            if p > n:
                break
            if p == 2:
                present = n >= 4 and n & (n - 1) == 0
                pairs = []
            else:
                pairs = two_powers(p, n)
                assert len(pairs) <= 1
                present = bool(pairs)
            exponent = actual.get(p, 0)
            assert exponent == int(present)
            valuation_checks += 1
            if present:
                expected[p] = 1
            if p > 2 and n < p * p:
                assert exponent == int(n == p + 1 or n == 2 * p)
                large_checks += 1
            if p > 2 and present:
                i, j = pairs[0]
                assert j > 0
                k = (p - 1) * p ** (j - 1)
                assert 0 < k < n and k % 2 == 0
                witness = math.comb(n, k)
                assert witness % p == 0 and witness % (p * p) != 0
                carry_checks += 1
                if n != p + 1 and n != 2 * p:
                    assert max(i, j) >= 2 and p * p <= n
                    proper += 1
        assert actual == expected
        coefficients[n] = actual
        large = [p for p in actual if p > 2 and n < p * p]
        assert len(large) <= 2
        if len(large) == 2:
            q, p = sorted(large)
            assert n == p + 1 == 2 * q and p == 2 * q - 1
            pair_checks += 1
        if n in (4, 6, 8, 10, 30, 64, 128, 256, 512):
            packet_examples.append({"label": n, "literalGcd": g,
                                    "exactPrimeFactorization": actual})

    ledgers = 0
    for seed in range(16):
        left, right = {}, {}
        weights = {n: Fraction(((n * 17 + seed * 13) % 31) - 15, seed + 1)
                   for n in coefficients}
        for n, basis in coefficients.items():
            for p, exponent in basis.items():
                add_scaled(left, p, weights[n] * exponent)
        for p in primes:
            joined = Fraction(0)
            for n in coefficients:
                present = (n & (n - 1) == 0) if p == 2 else bool(two_powers(p, n))
                if present and p <= n:
                    joined += weights[n]
            add_scaled(right, p, joined)
        assert left == right
        ledgers += 1

    marked = 0
    for n in range(1, ceiling + 1):
        p = n // 2
        if n % 2 == 0 and p in primes and p > 2:
            assert coefficients[n][p] == 1
            marked += 1
    floating = [{"candidateRealPart": beta, "height": y,
                 "markedDilationFactorNorm": abs(cmath.exp(-(beta + 1j * y) * math.log(2)))}
                for beta in (0.5, 0.625, 0.75, 0.875) for y in (54, 65, 100)]
    out = {
        "checksPassed": True, "proofInput": False,
        "literalEvenRows": len(coefficients), "ceiling": ceiling,
        "rawEmptyHeadAtTwo": 0,
        "exactAllPrimeValuationChecks": valuation_checks,
        "exactLargePrimeChecks": large_checks,
        "exactOneCarryWitnesses": carry_checks,
        "properPowerIncidencesRetained": proper,
        "exactOrderedTwoLargePrimeConstraints": pair_checks,
        "exactRationalWholePacketLedgers": ledgers,
        "rationalMasksAreNotActualHeightPhases": True,
        "exactMarkedDilationChannels": marked,
        "examples": packet_examples,
        "floatingMarkedSourceFactors": floating,
        "wholeGcdNativeSourceInferred": False,
        "twoPrimeSourceInferredFromLinearSource": False,
        "properPowerSupportIsNotAggregatePayment": True,
        "newRHOrZeroExclusionClaimed": False,
    }
    folder = Path(".lake/arithmetic-operator-kummer-parity")
    folder.mkdir(parents=True, exist_ok=True)
    (folder / "probe.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({k: v for k, v in out.items()
                      if k not in ("examples", "floatingMarkedSourceFactors")}))


if __name__ == "__main__":
    main()

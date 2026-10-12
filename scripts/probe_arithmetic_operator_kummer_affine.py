#!/usr/bin/env python3
"""Diagnostic-only audit of the actual even-row affine prime-pair sector.

Integer valuations and rational masked joins are exact. Height phases
are floating diagnostics, not proof input. No nonlinear actual-zero
source or asymptotic prime-pair estimate is inferred from finite data.
The parity source countermodel is an integer ARRAY, not actual primes.
"""
import cmath
import json
import math
from fractions import Fraction
from pathlib import Path


def primes_upto(n):
    prime = [True] * (n + 1)
    prime[0:2] = [False, False]
    for p in range(2, math.isqrt(n) + 1):
        if prime[p]:
            for k in range(p * p, n + 1, p):
                prime[k] = False
    return prime


def valuation(n, p):
    out = 0
    while n and n % p == 0:
        n //= p
        out += 1
    return out


def add(out, key, value):
    out[key] = out.get(key, Fraction(0)) + value
    if out[key] == 0:
        del out[key]


def main():
    ceiling = 512
    prime = primes_upto(2 * ceiling)
    primes = [p for p in range(3, ceiling + 1) if prime[p]]
    rows, literal_pairs = {}, []
    native_checks = 0
    for n in range(4, ceiling + 1, 2):
        g = 0
        for k in range(2, n, 2):
            g = math.gcd(g, math.comb(n, k))
        rows[n] = g
        large = [p for p in primes if p <= n and n < p * p]
        for q in large:
            for p in large:
                if q >= p:
                    continue
                actual = g % p == 0 and g % q == 0
                reduced = n == 2 * q and p == 2 * q - 1
                assert actual == reduced
                native_checks += 1
                if actual:
                    assert valuation(g, p) == valuation(g, q) == 1
                    literal_pairs.append((n, p, q))
    expected_pairs = [(2 * q, 2 * q - 1, q)
                      for q in primes if 2 * q <= ceiling and prime[2 * q - 1]]
    assert literal_pairs == expected_pairs

    ledger_checks = 0
    # Logs are kept as formal products indexed by BOTH primes.
    # These rational masks are not represented as actual height phases.
    for code in range(20):
        S = {n for n in rows if (n // 2 + code) % 5 != 0}
        P = {p for p in primes if (p + code) % 7 != 0}
        Q = {q for q in primes if (q + 2 * code) % 11 != 0}

        def w(n, p, q):
            return Fraction((-1) ** (n + p + q + code) *
                            (1 + (n + p * q + code) % 13), 1 + (n + p + q) % 17)

        literal, reduced = {}, {}
        for n, p, q in literal_pairs:
            if n in S and p in P and q in Q:
                add(literal, (p, q), valuation(rows[n], p) *
                    valuation(rows[n], q) * w(n, p, q))
        for q in Q:
            p, n = 2 * q - 1, 2 * q
            if prime[p] and p in P and n in S:
                add(reduced, (p, q), w(n, p, q))
        assert literal == reduced
        ledger_checks += 1

    # beta=0 makes the density-free residue model rational on every
    # positive physical index: g(n)=2*v/n on even n, else 0.
    # The complex-height exact residue is proved in Lean, not by this probe.
    v = Fraction(-3)

    def model(n):
        return 2 * v / n if n and n % 2 == 0 else Fraction(0)

    source_pair_checks = 0
    source_values = []
    for q in range(20001):
        right = max(0, 2 * q - 1)
        assert model(q) * model(right) == 0
        source_pair_checks += 1
    for code in range(12):
        val = sum(Fraction((-1) ** (q + code), 1 + q % 31) *
                  model(q) * model(max(0, 2 * q - 1))
                  for q in range(3001) if (q + code) % 5)
        assert val == 0
        source_values.append(str(val))

    phase_checks = []
    for y in (54, 65, 100, 350):
        native = sum(math.log(p) * math.log(q) * cmath.exp(-1j * y * math.log(n))
                     for n, p, q in literal_pairs)
        reduced = sum(math.log(2 * q - 1) * math.log(q) *
                      cmath.exp(-1j * y * math.log(2 * q))
                      for q in primes if 2 * q <= ceiling and prime[2 * q - 1])
        assert abs(native - reduced) < 1e-10
        phase_checks.append({"diagnosticHeight": y,
                             "wholeLabelPhase": True,
                             "nativePacketReal": native.real,
                             "nativePacketImag": native.imag,
                             "residualNorm": abs(native - reduced)})

    # Larger-range map: source status remains OPEN regardless of counts.
    cap = 200000
    big_prime = primes_upto(2 * cap)
    scales = []
    for top in (1000, 10000, 100000, cap):
        qs = [q for q in range(3, top + 1) if big_prime[q]]
        pairs = [q for q in qs if big_prime[2 * q - 1]]
        blocked = [q for q in qs if q % 3 == 2]
        assert all(not big_prime[2 * q - 1] for q in blocked)
        assert all(q == 3 or q % 3 == 1 for q in pairs)
        scales.append({"qCeiling": top,
                       "ordinaryOddPrimes": len(qs),
                       "affinePrimePairs": len(pairs),
                       "primesBlockedByModThree": len(blocked),
                       "nonlinearActualZeroSourceInferred": False})

    result = {"checksPassed": True, "proofInput": False,
              "literalEvenRows": len(rows), "ceiling": ceiling,
              "nativeOrderedLargePairChecks": native_checks,
              "literalPairCount": len(literal_pairs),
              "actualValuationsRetained": True,
              "allFinitePhysicalMasksRetained": True,
              "exactRationalMaskedLedgerChecks": ledger_checks,
              "rationalMasksAreNotActualHeightPhases": True,
              "literalPairExamples": [{"n": n, "p": p, "q": q}
                                      for n, p, q in literal_pairs],
              "exactParityCountermodelPairChecks": source_pair_checks,
              "exactCountermodelPacketChecks": len(source_values),
              "countermodelIsActualPrimeRow": False,
              "countermodelGrantedBinomialGammaCompatibility": False,
              "countermodelEulerSourceProof": "Lean phased_source/phased_has_source",
              "floatingWholeHeightRegressions": phase_checks,
              "finitePrimeMap": scales,
              "wholeHigherPowerComplementPaid": False,
              "newArithmeticEstimateOrZeroExclusion": False,
              "nextGate": "actual nonlinear prime-specific source, not linear residue alone"}
    directory = Path(".lake/arithmetic-operator-kummer-affine")
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "probe.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

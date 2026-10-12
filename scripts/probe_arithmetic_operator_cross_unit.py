#!/usr/bin/env python3
"""Exact diagnostics for fixed/coherent cofactor binomial-unit codes.

All finite arithmetic below is integer/rational. It is not an asymptotic
estimate or proof input. Rational phases test bookkeeping; the Lean leaf
retains the actual fixed-height prime phase. Cross-prime diagnostics do
not supply a zero-mode response or a global PSD/cancellation theorem.
"""

from collections import Counter
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path
import json


def primes(limit):
    return [n for n in range(2, limit + 1)
            if all(n % d for d in range(2, isqrt(n) + 1))]


def quadratic(p, x):
    if p == 2:
        return x % 2
    v = pow(x % p, (p - 1) // 2, p)
    return -1 if v == p - 1 else v


def fixed_bulk(n):
    return {1: F(1), 5: F(1, 3)}.get(n % 8, F(0))


def chi4(n):
    return {1: 1, 3: -1}.get(n % 4, 0)


def chi8(n):
    return {1: 1, 3: -1, 5: -1, 7: 1}.get(n % 8, 0)


def chi_neg8(n):
    return chi4(n) * chi8(n)


def endpoint(p):
    return F((2 + chi8(p)) * (1 - chi4(p)), 6 * p)


def exact_trace(p, a):
    return F(sum(quadratic(p, comb(p * a - 1, k))
                 for k in range(p * a)), p * a)


def joined_row(p, q):
    # Keep BOTH upper-digit tables modulo their own prime.
    lp = [quadratic(p, comb(q - 1, h)) for h in range(q)]
    lq = [quadratic(q, comb(p - 1, h)) for h in range(p)]
    ep, eq = quadratic(p, -1), quadratic(q, -1)
    return F(sum(ep ** (k % p) * eq ** (k % q) * lp[k // p] * lq[k // q]
                 for k in range(p * q)), p * q)


def add_symbolic(bucket, p, value):
    real, imag = value
    old = bucket.get(p, (F(0), F(0)))
    bucket[p] = old[0] + real, old[1] + imag


def main():
    ps = primes(127)
    fixed = {}
    for p in ps:
        actual = exact_trace(p, 3)
        fixed[p] = actual
        if p == 2:
            assert actual == F(2, 3)
        else:
            assert actual == fixed_bulk(p) + endpoint(p)
            assert abs(endpoint(p)) <= F(1, p)

    for n in range(1024):
        principal = n % 2
        assert fixed_bulk(n) == F(2 * principal + 2 * chi4(n) + chi8(n) + chi_neg8(n), 6)

    powers = {}
    for p in ps:
        n, exponent = p, 1
        while n <= 256:
            powers[n] = p, exponent
            n, exponent = n * p, exponent + 1
    phases = [(1, 0), (0, 1), (-1, 0), (0, -1)]
    # Symbolic log(p) coefficients: no approximate logarithms or actual
    # irrational height phases are promoted to exact equalities.
    for X in range(257):
        buckets = [dict() for _ in range(5)]
        for n, (p, exponent) in powers.items():
            if n > X:
                continue
            phase = phases[n % 4]
            vals = [fixed[p] if exponent == 1 else F(0),
                    fixed_bulk(n), fixed_bulk(n) if exponent > 1 else F(0),
                    endpoint(p) if exponent == 1 and p != 2 else F(0),
                    F(2, 3) if n == 2 else F(0)]
            for bucket, value in zip(buckets, vals):
                add_symbolic(bucket, p, (value * phase[0], value * phase[1]))
        full, bulk, proper, boundary, head = buckets
        for p in ps:
            values = [b.get(p, (F(0), F(0))) for b in buckets]
            assert all(values[0][i] == values[1][i] - values[2][i] + values[3][i] + values[4][i]
                       for i in range(2))

    pair_values = {}
    direct_rows = 0
    for i, p in enumerate(ps[1:]):
        for q in ps[1:i + 1]:
            joined = joined_row(p, q)
            pair_values[p, q] = joined
            if p <= 31:
                direct = F(sum(quadratic(p, comb(p*q-1, k)) * quadratic(q, comb(p*q-1, k))
                               for k in range(p*q)), p*q)
                assert joined == direct
                direct_rows += 1
    odd_odd = {(p, q): value for (p, q), value in pair_values.items()
               if p % 4 == q % 4 == 3}
    signs = Counter("negative" if v < 0 else "positive" if v > 0 else "zero"
                    for v in odd_odd.values())
    assert signs["negative"] and signs["positive"]
    assert odd_odd[19, 7] == F(-13, 133)

    # Exact diagnostic LDL, not a universal PSD statement.
    odd_ps = ps[1:]
    pivots, rows = [], []
    for i, p in enumerate(odd_ps):
        row = []
        for j in range(i):
            q = odd_ps[j]
            entry = pair_values[max(p, q), min(p, q)]
            row.append((entry - sum(row[k] * rows[j][k] * pivots[k] for k in range(j))) / pivots[j])
        pivot = F(1) - sum(row[k] ** 2 * pivots[k] for k in range(i))
        rows.append(row)
        pivots.append(pivot)

    report = {
        "checksPassed": True, "proofInput": False,
        "arithmetic": "actual integer binomials, complete upper-digit tables, exact fractions",
        "maxPrime": 127, "fixedCofactor": 3,
        "fixedCofactorActualRows": len(ps), "characterTableCases": 1024,
        "symbolicProperPowerPrefixJoins": 257,
        "literalFixedHeightPhaseInProbe": False,
        "actualHeightPhaseRetainedByLean": True,
        "distinctOddCrossPrimePairs": len(pair_values),
        "directIntegerCrossRowRegressions": direct_rows,
        "bothCharactersOddPairs": len(odd_odd), "oddOddSigns": dict(signs),
        "negativeDiagnostic": {"p": 19, "q": 7, "joinedTrace": "-13/133"},
        "largestAbsoluteOddOddSamples": [
            {"p": p, "q": q, "trace": str(value)}
            for (p, q), value in sorted(odd_odd.items(), key=lambda item: -abs(item[1]))[:8]],
        "exactFiniteLDL": {
            "matrixSize": len(odd_ps), "diagonalConvention": "actual p^2-1 aligned quadratic square trace = 1",
            "allLeadingPivotsPositive": all(d > 0 for d in pivots),
            "smallestPivot": str(min(pivots)),
            "universalPSDClaim": False, "zeroSourceGatePassed": False},
        "asymptoticOrRHClaim": False,
        "growingCofactorSourceEstimateOpen": True,
    }
    target = Path(".lake/arithmetic-operator-cross-unit/probe.json")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(report, indent=2) + "\n")
    compact = {k: v for k, v in report.items() if k not in ["largestAbsoluteOddOddSamples", "exactFiniteLDL"]}
    compact["finiteLDLPositivePivots"] = report["exactFiniteLDL"]["allLeadingPivotsPositive"]
    print(json.dumps(compact, indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact finite regression for binomial-unit/source and cross-prime gates.

This is diagnostic only. It uses actual binomial integers, exact rational
complex codes and symbolic prime logarithms, not an asymptotic estimate.
Gaussian rational outer phases below are controls, not fixed-height n^(-iy).
The Lean leaf, not this probe, retains the literal fixed-height phase.
"""

from collections import Counter
from fractions import Fraction
from math import comb
from pathlib import Path
import json


def primes(limit):
    return [p for p in range(2, limit + 1)
            if all(p % d for d in range(2, int(p ** .5) + 1))]


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def sub(a, b):
    return a[0] - b[0], a[1] - b[1]


def scale(a, c):
    return a[0] * c, a[1] * c


def mul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


ZERO = (Fraction(0), Fraction(0))
ONE = (Fraction(1), Fraction(0))
PHASES = [ONE, (0, 1), (-1, 0), (0, -1)]


def code(p, n, variant):
    if variant == 0:
        return lambda _x: ONE
    return lambda x: (Fraction((x * x + n + variant) % 7 - 3, 8),
                      Fraction((3 * x + 2 * n + variant) % 5 - 2, 8))


def sum_code(residues, f):
    out = ZERO
    for x in residues:
        out = add(out, f(x))
    return out


def encoded(z):
    return [str(Fraction(z[0])), str(Fraction(z[1]))]


def quadratic(p, x):
    if p == 2:
        return x % 2
    v = pow(x % p, (p - 1) // 2, p)
    return -1 if v == p - 1 else v


def main():
    ps = primes(31)
    prime_powers = {}
    rows = residues_checked = trace_cases = 0
    traces = {}
    for p in ps:
        n, r = 1, 0
        while n <= 256:
            residues = [comb(n - 1, k) % p for k in range(n)]
            assert residues == [pow(-1, k, p) for k in range(n)]
            residues_checked += n
            rows += 1
            for variant in range(3):
                f = code(p, n, variant)
                trace = scale(sum_code(residues, f), Fraction(1, n))
                mean = scale(add(f(1 % p), f((-1) % p)), Fraction(1, 2))
                endpoint = scale(sub(f(1 % p), f((-1) % p)), Fraction(n % 2, 2 * n))
                assert trace == add(mean, endpoint)
                assert abs(endpoint[0]) + abs(endpoint[1]) <= Fraction(1, n)
                traces[p, n, variant] = trace, mean, endpoint
                trace_cases += 1
            if r:
                prime_powers[n] = p, r
            n, r = n * p, r + 1

    symbolic_joins = 0
    for X in range(129):
        for variant in range(3):
            full, bulk, boundary = {}, {}, {}
            for n, (p, _r) in prime_powers.items():
                if n > X:
                    continue
                trace, mean, endpoint = traces[p, n, variant]
                phase = PHASES[n % 4]
                for bucket, value in [(full, trace), (bulk, mean), (boundary, endpoint)]:
                    bucket[p] = add(bucket.get(p, ZERO), mul(phase, value))
            for p in set(full) | set(bulk) | set(boundary):
                assert full.get(p, ZERO) == add(bulk.get(p, ZERO), boundary.get(p, ZERO))
            symbolic_joins += 1

    common_cases = 0
    for p in ps:
        for a in range(1, 33):
            for k in range(p * a):
                actual = comb(p * a - 1, k) % p
                rhs = pow(-1, k % p, p) * comb(a - 1, k // p) % p
                assert actual == rhs
                common_cases += 1

    cross_rows = 0
    nonindependent_rows = []
    upper_factor_failures = 0
    for p in ps:
        for q in ps:
            if p <= q:
                continue
            n = p * q
            pairs = [(comb(n - 1, k) % p, comb(n - 1, k) % q) for k in range(n)]
            # Largest-prime column has no zero residue: its upper row lies below p.
            assert all(x != 0 for x, _ in pairs)
            upper_factor_failures += sum(x != pow(-1, k % p, p)
                                         for k, (x, _) in enumerate(pairs))
            cp = Fraction(sum(quadratic(p, x) for x, _ in pairs), n)
            cq = Fraction(sum(quadratic(q, x) for _, x in pairs), n)
            joined = Fraction(sum(quadratic(p, x) * quadratic(q, z) for x, z in pairs), n)
            covariance = joined - cp * cq
            if covariance:
                nonindependent_rows.append({
                    "p": p, "q": q, "rowLength": n,
                    "quadraticMeanLargest": str(cp), "quadraticMeanSmallest": str(cq),
                    "joinedQuadraticMean": str(joined), "covariance": str(covariance),
                    "zeroCountSmallest": sum(z == 0 for _, z in pairs),
                    "distinctJointResidues": len(Counter(pairs)),
                })
            cross_rows += 1

    assert comb(14, 6) % 3 == 0 and pow(-1, 6 % 3, 3) == 1
    result = {
        "checksPassed": True, "proofInput": False,
        "scope": "complete aligned unit rows and literal common-row Lucas upper factors",
        "arithmetic": "integer binomials, rational complex codes, symbolic log(prime)",
        "fixedHeightPhaseNumericallyApproximated": False,
        "gaussianRationalOuterPhaseControlsOnly": True,
        "maxAlignedRowLength": 256, "maxPrime": 31,
        "alignedRows": rows, "alignedResidues": residues_checked,
        "exactCodeTraceCases": trace_cases, "symbolicPrimePowerJoins": symbolic_joins,
        "commonRowDigitCases": common_cases, "distinctCrossPrimeRows": cross_rows,
        "droppingUpperFactorFailureAtoms": upper_factor_failures,
        "nonindependentQuadraticCodeRows": len(nonindependent_rows),
        "crossPrimeSamples": nonindependent_rows[:10],
        "asymptoticSourceOrCancellationClaim": False,
        "sourceSensitiveCrossPrimeEstimateProved": False,
        "regressionCounterexample": {"p": 3, "q": 5, "k": 6,
                                     "actualResidue": 0, "lowerSignOnly": 1},
    }
    target = Path(".lake/arithmetic-operator-lucas-unit/probe.json")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "crossPrimeSamples"}, indent=2))


if __name__ == "__main__":
    main()

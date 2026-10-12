#!/usr/bin/env python3
"""Literal binomial-GCD preflight, with exact integer and symbolic logs.

Diagnostics only, never Lean proof input. Rational masks test arbitrary
outer arrays; the separate floating tests keep the actual height phase.
No nonlinear zero response or asymptotic theorem is inferred from samples.
"""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import cmath
import json
import math


def prime_power_base(n):
    if n < 2:
        return None
    p = next((d for d in range(2, math.isqrt(n) + 1) if n % d == 0), n)
    rest = n
    while rest % p == 0:
        rest //= p
    return p if rest == 1 else None


def gcd_row(n, endpoints):
    if endpoints:
        values = (math.comb(n, k) for k in range(n + 1))
    else:
        values = (math.comb(n, k) for k in range(1, n))
    return max(1, math.gcd(*values))


def log_basis(n):
    base = prime_power_base(n)
    return {} if base is None else {base: Fraction(1)}


def joined(bases, cutoff, weight):
    out = defaultdict(Fraction)
    for n in range(1, cutoff + 1):
        for p, value in bases[n].items():
            out[p] += value * weight(n)
    return {p: v for p, v in out.items() if v}


def main():
    bound = 512
    interior = [gcd_row(n, False) for n in range(bound + 1)]
    complete = [gcd_row(n, True) for n in range(bound + 1)]
    expected = [prime_power_base(n) or 1 for n in range(bound + 1)]
    assert interior == expected
    assert complete == [1] * (bound + 1)
    bases = [({g: Fraction(1)} if g > 1 else {}) for g in interior]
    actual = [log_basis(n) for n in range(bound + 1)]
    assert bases == actual
    masks = [lambda n: Fraction(1), lambda n: Fraction(n % 5 - 2),
             lambda n: Fraction((-1) ** n, n + 1),
             lambda n: Fraction((n * n + 3 * n) % 17 - 8, 7)]
    symbolic_tests = 0
    for cutoff in (1, 2, 16, 64, 128, 512):
        for mask in masks:
            assert joined(bases, cutoff, mask) == joined(actual, cutoff, mask)
            symbolic_tests += 1
    pair_tests = 0
    for cutoff in (16, 32, 64):
        left, right = defaultdict(Fraction), defaultdict(Fraction)
        for n in range(1, cutoff + 1):
            for m in range(1, cutoff + 1):
                w = Fraction((n + 2 * m) % 9 - 4, n + m)
                for p in bases[n]:
                    for q in bases[m]:
                        left[(p, q)] += w
                for p in actual[n]:
                    for q in actual[m]:
                        right[(p, q)] += w
        assert dict(left) == dict(right)
        pair_tests += 1
    floating = []
    for y in (54, 65, 100):
        for k in (0, 1, 4, 8):
            v = w = 0j
            for n in range(1, bound + 1):
                feature = (math.log(n) ** k / math.factorial(k)) * cmath.exp(
                    -(1.5 + 1j * y) * math.log(n))
                v += math.log(interior[n]) * feature
                p = prime_power_base(n)
                w += (math.log(p) if p else 0) * feature
            assert abs(v - w) < 1e-12
            floating.append({"height": y, "order": k,
                             "finiteMomentError": abs(v - w),
                             "interiorMomentNorm": abs(v),
                             "completeEndpointMoment": 0})
    report = {"checksPassed": True, "proofInput": False,
              "exactLiteralRows": bound + 1,
              "exactInteriorGcdClassifications": bound + 1,
              "exactEndpointRowGcdClassifications": bound + 1,
              "properPowerRowsRetained": [n for n in range(2, bound + 1)
                                          if prime_power_base(n) not in (None, n)],
              "symbolicMaskedLogLedgers": symbolic_tests,
              "symbolicJoinedTwoRowLedgers": pair_tests,
              "rationalMasksAreNotActualHeightPhases": True,
              "floatingActualHeightRegressions": floating,
              "countermodelsGrantedActualBinomialGcdData": False,
              "newAsymptoticZeroOrRHClaimed": False,
              "scope": "full literal GCD with endpoints is one; interior GCD logarithm is exactly actual Mangoldt, including all proper powers"}
    target = Path('.lake/arithmetic-operator-kummer-minimum/probe.json')
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({"passed": True, "integerRows": bound + 1,
                      "symbolicLogLedgers": symbolic_tests,
                      "joinedTwoRowLedgers": pair_tests,
                      "floatingHeightRegressions": len(floating),
                      "report": str(target)}))


if __name__ == '__main__':
    main()

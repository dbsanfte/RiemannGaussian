#!/usr/bin/env python3
"""Exact native common-row Fourier regression; no probe is proof input.

Integer/Gaussian-rational checks are separated from floating theta samples.
Both Lucas upper digits and every crossing and endpoint are retained.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb, cos, sin, pi
from pathlib import Path
import json


def primes(limit: int) -> list[int]:
    return [n for n in range(2, limit + 1) if all(n % d for d in range(2, int(n**0.5) + 1))]


def legendre(v: int, p: int) -> int:
    v %= p
    if v == 0:
        return 0
    if p == 2:
        return 1
    return 1 if pow(v, (p - 1) // 2, p) == 1 else -1


def lucas(n: int, k: int, p: int) -> int:
    value = 1
    while n or k:
        a, b = n % p, k % p
        if b > a:
            return 0
        value = (value * comb(a, b)) % p
        n //= p
        k //= p
    return value


def add(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return a[0] + b[0], a[1] + b[1]


def mul(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def scale(a: tuple[int, int], s: int) -> tuple[int, int]:
    return a[0] * s, a[1] * s


def power(a: tuple[int, int], n: int) -> tuple[int, int]:
    answer = 1, 0
    while n:
        if n & 1:
            answer = mul(answer, a)
        a = mul(a, a)
        n //= 2
    return answer


def row(p: int, q: int, d: int) -> list[int]:
    assert d > 0 and d % p == d % q == 0
    # The complete upper residues are genuine Lucas residues, not signs alone.
    upper_p = [legendre(lucas(d // p - 1, k, p), p) for k in range(d // p)]
    upper_q = [legendre(lucas(d // q - 1, k, q), q) for k in range(d // q)]
    sp, sq = legendre(-1, p), legendre(-1, q)
    return [(sp ** (k % p)) * upper_p[k // p] * (sq ** (k % q)) * upper_q[k // q]
            for k in range(d)]


def main() -> None:
    ps = primes(83)
    units = [(1, 0), (-1, 0), (0, 1), (0, -1)]
    finite_rows = 0
    atom_checks = 0
    direct_checks = 0
    recurrence_checks = 0
    exact_fourier_identities = 0
    exact_gap_bounds = 0
    proper_power_rows = 0
    examples = []
    rows = [(p, q, p * q, False) for p in ps for q in ps if p != q]
    rows += [(p, q, (p**r) * (q**s), True)
             for p in primes(13) for q in primes(13) if p != q
             for r in range(1, 4) for s in range(1, 4)
             if r + s > 2 and (p**r) * (q**s) <= 4096]
    for p, q, d, proper in rows:
        values = row(p, q, d)
        sigma = legendre(-1, p) * legendre(-1, q)
        crossings = [k for k in range(d - 1) if (k + 1) % p == 0 or (k + 1) % q == 0]
        assert len(crossings) <= d // p + d // q
        assert values[0] == values[-1] == 1
        for k in range(d - 1):
            if k not in crossings:
                assert values[k + 1] == sigma * values[k]
                recurrence_checks += 1
        atom_checks += d
        if d <= 600:
            for k, value in enumerate(values):
                literal = comb(d - 1, k)
                assert legendre(literal, p) * legendre(literal, q) == value
                direct_checks += 1
        for lam in units:
            coded = (0, 0)
            lk = (1, 0)
            for value in values:
                coded = add(coded, scale(lk, value))
                lk = mul(lk, lam)
            gap = add((1, 0), scale(lam, -sigma))
            rhs = add((1, 0), scale(power(lam, d), -sigma))
            for k in crossings:
                rhs = add(rhs, scale(power(lam, k + 1), values[k + 1] - sigma * values[k]))
            assert mul(gap, coded) == rhs
            exact_fourier_identities += 1
            gap_sq = gap[0]**2 + gap[1]**2
            if gap_sq:
                trace_sq = Fraction(coded[0]**2 + coded[1]**2, d*d)
                envelope = Fraction(2, d) + Fraction(2, p) + Fraction(2, q)
                assert trace_sq * gap_sq <= envelope * envelope
                exact_gap_bounds += 1
        finite_rows += 1
        proper_power_rows += int(proper)
        if p > q and not proper and p in (19, 31, 59, 83) and q in (7, 13, 23, 41):
            float_codes = []
            for theta in (0., pi/2, pi, 1/p, 1/d):
                phase = complex(cos(theta), sin(theta))
                result = sum(value * phase**k for k, value in enumerate(values))/d
                actual_gap = abs(1 - sigma * phase)
                float_codes.append({"theta": theta, "actual_gap": actual_gap,
                                    "trace_abs": abs(result), "trace_real": result.real,
                                    "trace_imag": result.imag,
                                    "bound": None if actual_gap == 0 else
                                        (2/d + 2/p + 2/q)/actual_gap})
            examples.append({"p": p, "q": q, "D": d, "sigma": sigma,
                             "floating_codes": float_codes})
    output = {
        "scope": "native shared-binomial internal Fourier source barrier",
        "exact_integer_and_Gaussian_rational_diagnostics": {
            "native_rows": finite_rows, "proper_power_common_rows": proper_power_rows,
            "atoms_with_both_upper_digits": atom_checks,
            "direct_literal_binomial_checks": direct_checks,
            "noncrossing_recurrences": recurrence_checks,
            "exact_Fourier_defect_identities": exact_fourier_identities,
            "exact_squared_gap_bounds": exact_gap_bounds,
        },
        "floating_diagnostics_not_certificates": examples,
        "not_inferred": ["actual uncoded same-parity zero source", "RH arithmetic inequality",
                         "summed proper-power complement payment", "generic internal mask bound"],
        "all_probes_diagnostic_only": True,
    }
    target = Path(".lake/arithmetic-operator-joint-constraint")
    target.mkdir(parents=True, exist_ok=True)
    (target / "probe.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output["exact_integer_and_Gaussian_rational_diagnostics"]))


if __name__ == "__main__":
    main()

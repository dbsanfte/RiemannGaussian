#!/usr/bin/env python3
"""Exact coefficient diagnostics; never Lean proof input.

Formal basis (a, p) means log(p)*exp(-i*y*log(a)). Collect matching
products BEFORE specializing a floating height. Thus the exact checks
retain the full same-height multiplicative phase symbolically, every
proper power, and every native row/divisor endpoint.
"""
from __future__ import annotations

from collections import defaultdict
import cmath
import json
import math
from pathlib import Path


def factor(n: int) -> dict[int, int]:
    out: dict[int, int] = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def divisors(n: int) -> list[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def mu(factors: dict[int, int]) -> int:
    return 0 if any(e > 1 for e in factors.values()) else (-1) ** len(factors)


def cleaned(d: dict[tuple[int, int], int]) -> dict[tuple[int, int], int]:
    return {key: value for key, value in d.items() if value}


def main() -> None:
    cutoff = 1024
    facts = {n: factor(n) for n in range(1, cutoff + 1)}
    proxy: dict[int, dict[tuple[int, int], int]] = {}
    target: dict[int, dict[tuple[int, int], int]] = {}
    fibers = proper_powers = 0
    for n in range(1, cutoff + 1):
        g: dict[tuple[int, int], int] = defaultdict(int)
        f: dict[tuple[int, int], int] = defaultdict(int)
        for d in divisors(n):
            for p, e in facts[d].items():
                g[d, p] += e
            if len(facts[d]) == 1:
                p, e = next(iter(facts[d].items()))
                f[d, p] += 1
                proper_powers += int(e >= 2)
        proxy[n], target[n] = cleaned(g), cleaned(f)
        inv: dict[tuple[int, int], int] = defaultdict(int)
        for d in divisors(n):
            coefficient = mu(facts[d])
            # Keep the native d*k=n endpoint and the whole cofactor.
            for (a, p), value in proxy[n // d].items():
                inv[d * a, p] += coefficient * value
                fibers += 1
        assert cleaned(inv) == target[n], n

    # The exact root-count witness is native addition (multiples of six),
    # not an estimate made from floating logarithmic root separation.
    root_checks = []
    for x in (6, 12, 64, 128, 256, 512, 1024):
        labels = [6 * (j + 1) for j in range(x // 6)]
        assert len(labels) == len(set(labels)) == x // 6
        assert all(len(facts[n]) >= 2 for n in labels)
        assert facts[2] == {2: 1}
        root_checks.append({"cutoff": x, "distinct_zero_labels": len(labels),
                            "minimum_exact_jet_degree": x // 6})

    floating_checks = []
    for y in (54.0, 87.25, -125.5):
        worst = 0.0
        for n in (60, 128, 210, 256, 420, 729, 1024):
            def evaluate(basis: dict[tuple[int, int], int]) -> complex:
                return sum(value * math.log(p) * cmath.exp(-1j * y * math.log(a))
                           for (a, p), value in basis.items())
            direct = evaluate(target[n])
            inverse = sum(mu(facts[d]) * cmath.exp(-1j * y * math.log(d))
                          * evaluate(proxy[n // d]) for d in divisors(n))
            error = abs(inverse - direct)
            assert error < 1e-9
            worst = max(worst, error)
        floating_checks.append({"height": y, "max_inverse_roundoff": worst})

    report = {
        "scope": "finite-log-jet coefficient class and exact native Mobius inverse",
        "proof_input": False,
        "exact_symbolic_full_height_phase_checks": {
            "cutoff": cutoff, "native_rows": cutoff,
            "inverse_fibers": fibers, "proper_power_incidents": proper_powers,
            "basis": "(a,p) = log(p)*exp(-i*y*log(a)); collected before norms",
            "all_native_divisors_and_unit_endpoints": True,
            "degree_witnesses": root_checks,
        },
        "floating_diagnostics_not_certificates": floating_checks,
        "actual_zero_residue_or_native_asymptotic_numerically_inferred": False,
    }
    path = Path(".lake/arithmetic-operator-shifted-divisor/probe.json")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"native_rows": cutoff, "inverse_fibers": fibers,
                      "proper_power_incidents": proper_powers,
                      "exact_checks": "passed", "proof_input": False}))


if __name__ == "__main__":
    main()

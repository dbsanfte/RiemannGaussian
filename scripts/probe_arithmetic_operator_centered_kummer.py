#!/usr/bin/env python3
"""Exact finite diagnostics for complete constant-centered Kummer columns.

Integer incidence and rational means only. These checks are not proof
inputs and do not infer any native incomplete-cutoff source or payment.
"""

import json
import math
from fractions import Fraction
from pathlib import Path


def carry(n, d):
    return (2 * n) // d - 2 * (n // d)


def check_pair(d, e):
    period = d * e
    sd = sum(carry(n, d) for n in range(d))
    se = sum(carry(n, e) for n in range(e))
    assert sd == d // 2 and se == e // 2
    md, me = Fraction(sd, d), Fraction(se, e)
    sfirst = sum(carry(n, d) for n in range(period))
    ssecond = sum(carry(n, e) for n in range(period))
    sboth = sum(carry(n, d) * carry(n, e) for n in range(period))
    assert sfirst == sd * e and ssecond == se * d
    assert Fraction(sboth, period) == md * me
    centered = Fraction(sboth, period) / (md * me) - 1
    assert centered == 0
    for eta in (Fraction(0), Fraction(1), Fraction(1, 2), Fraction(-2)):
        for xi in (Fraction(0), Fraction(1), Fraction(2, 3), Fraction(3)):
            actual = (Fraction(sboth, period) / (md * me)
                      - xi * Fraction(sfirst, period) / md
                      - eta * Fraction(ssecond, period) / me + eta * xi)
            assert actual == (1 - eta) * (1 - xi)
    last = ((Fraction(carry(period - 1, d), 1) / md - 1)
            * (Fraction(carry(period - 1, e), 1) / me - 1))
    assert last > 0
    # Deleting the literal final endpoint restores a nonzero residual.
    partial = -last
    assert partial != 0
    return period


def main():
    pairs = 0
    native_endpoint_products = 0
    for d in range(2, 41):
        for e in range(2, 41):
            if math.gcd(d, e) == 1:
                native_endpoint_products += check_pair(d, e)
                pairs += 1
    towers = []
    for p in (2, 3, 5, 7, 11, 13):
        for r in range(1, 5):
            if p ** r <= 81:
                towers.append((p, r, p ** r))
    tower_pairs = 0
    proper_power_pairs = 0
    for p, r, d in towers:
        for q, s, e in towers:
            if p != q:
                check_pair(d, e)
                tower_pairs += 1
                proper_power_pairs += int(r >= 2 or s >= 2)
    report = {
        "status": "diagnostic_only_exact_integer_and_rational_checks",
        "complete_coprime_denominator_pairs": pairs,
        "native_endpoint_products": native_endpoint_products,
        "fixed_scalar_interpolation_checks": 16 * pairs,
        "actual_distinct_prime_power_pairs": tower_pairs,
        "proper_prime_power_pairs": proper_power_pairs,
        "one_deleted_endpoint_nonzero_checks": pairs + tower_pairs,
        "zero_source_is_Lean_theorem_not_probe_inference": True,
        "no_incomplete_boundary_payment_or_source_claim": True,
        "no_controls_granted_actual_Gamma_binomial_compatibility": True,
    }
    out = Path(".lake/arithmetic-operator-centered-kummer")
    out.mkdir(parents=True, exist_ok=True)
    (out / "probe.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

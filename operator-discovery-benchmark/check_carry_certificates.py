#!/usr/bin/env python3
"""Independent coefficient and inequality verifier for carry certificates.

Uses the proved rising-factor coefficient formula and valuations of integer
binomial coefficients. It imports neither root_probe's recursive solver nor
mixed_root_search's factorial-valuation kernel or local product interpreter.
"""

from __future__ import annotations

import json
from fractions import Fraction as Q
from functools import lru_cache
from math import comb
from pathlib import Path


@lru_cache(maxsize=None)
def integer_binomial_valuation(total, left, prime):
    integer = comb(total, left)
    exponent = 0
    while integer % prime == 0:
        integer //= prime
        exponent += 1
    return exponent


def coefficients(order, prime, parameter, degree):
    local_root = [Q(1)]
    for e in range(1, degree + 1):
        local_root.append(local_root[-1] * (Q(1, order) + e - 1) / e)
    polynomial = [Q(1)] + [Q(0)] * degree
    for _ in range(order):
        result = [Q(0)] * (degree + 1)
        for e in range(degree + 1):
            for left in range(e + 1):
                exponent = integer_binomial_valuation(e, left, prime)
                result[e] += polynomial[left] * local_root[e - left] * parameter ** exponent
        polynomial = result
    return [Q(1)] + [polynomial[e] - polynomial[e - 1] for e in range(1, degree + 1)]


def verify(record):
    degree = record["local_degree"]
    order = record["root_order"]
    operator = record["operator"]
    prime = operator["prime"]
    parameter = Q(operator["parameter"])
    radius = Q(record["radius"])
    if prime not in (2, 3, 5, 7) or not (2 * radius ** 2 > 1 and radius < 1):
        return False
    exact = coefficients(order, prime, parameter, degree)
    if exact[1] != 0:
        return False
    finite = sum((abs(exact[e]) * radius ** e for e in range(2, degree + 1)), Q(0))
    if abs(parameter) <= 1:
        tail = 2 * radius ** (degree + 1) / (1 - radius)
    elif parameter == 2:
        ratio = radius * Q(degree + 2, degree + 1) ** (order - 1)
        if ratio >= 1:
            return False
        tail = 2 ** order * (degree + 2) ** (order - 1) * radius ** (degree + 1) / (1 - ratio)
    else:
        return False
    total = finite + tail
    return (finite == Q(record["finite_absolute_sum"])
            and tail == Q(record["tail_bound"])
            and total == Q(record["total_bound"])
            and (total < 1) == record["certifies_no_correction_zeros_Re_s_gt_half"])


def main():
    output_dir = Path(__file__).resolve().parent / "root-results"
    original = json.loads((output_dir / "carry_zero_audit.json").read_text())
    checks = []
    for record in original["certificates"]:
        passed = verify(record)
        checks.append({"root_order": record["root_order"], "operator": record["operator"],
                       "independent_coefficient_and_bound_verification": passed})
    uniform_checks = []
    for record, multiplier, base in zip(original["uniform_parameter_theorems"], (1, 2), (5, 7)):
        radius = Q(record["radius"])
        bound = multiplier * radius ** base / (1 - radius)
        uniform_checks.append({"minimum_base_prime": base,
                               "rational_bound_verified": bound == Q(record["bound"]) and bound < 1
                               and radius ** 2 > Q(1, 2)})
    result = {"checks": checks, "all_passed": all(x["independent_coefficient_and_bound_verification"] for x in checks),
              "uniform_bound_checks": uniform_checks,
              "source": "Independent rising-factor root coefficients and integer binomial valuations",
              "does_not_establish_historical_novelty": True}
    (output_dir / "carry_certificate_verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"Independent certificate checks: {sum(x['independent_coefficient_and_bound_verification'] for x in checks)}/{len(checks)} passed")
    assert result["all_passed"]
    assert all(x["rational_bound_verified"] for x in uniform_checks)


if __name__ == "__main__":
    main()

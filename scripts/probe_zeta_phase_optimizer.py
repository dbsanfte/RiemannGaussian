#!/usr/bin/env python3
"""Explore the sparse phase optimizer's algebraic contact equations.

Copyright (c) 2026 David Sanftenberg. Released under Apache 2.0.

Requires mpmath. The output contains stationary numerical candidates, not
proofs of existence, positivity, uniqueness, or global optimality. The
kernel-checked rational bound is in ZetaPhaseContactCertificate.lean.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp


FREQUENCIES = (0, 1, 2, 3, 4, 7, 10, 13, 24)


def chebyshev_values(x):
    """Return T_n(x) and T'_n(x), for n from zero through 24."""
    values = [mp.mpf(1), x]
    derivatives = [mp.mpf(0), mp.mpf(1)]
    for _ in range(2, 25):
        values.append(2 * x * values[-1] - values[-2])
        derivatives.append(2 * values[-2] + 2 * x * derivatives[-1] - derivatives[-2])
    return values, derivatives


def source_coefficient(n, shift):
    if n == 0:
        return -1 / shift
    return 1 / (shift + 1) if n == 1 else mp.mpf(0)


def cost(n):
    return mp.mpf(1) if n == 0 else mp.mpf(n + 1) / 2


def fixed_shift_equations(*unknowns):
    cosines, weights, efficiency = unknowns[:4], unknowns[4:8], unknowns[8]
    values = [chebyshev_values(q)[0] for q in cosines]
    shift = mp.mpf(13) / 4
    return [
        efficiency * cost(n)
        - source_coefficient(n, shift)
        - sum(weights[j] * values[j][n] for j in range(4))
        for n in FREQUENCIES
    ]


def free_shift_equations(*unknowns):
    coefficients = [mp.mpf(1)] + list(unknowns[:8])
    cosines, weights = unknowns[8:12], unknowns[12:16]
    efficiency, shift = unknowns[16:18]
    pairs = [chebyshev_values(q) for q in cosines]
    equations = [
        sum(a * values[n] for a, n in zip(coefficients, FREQUENCIES))
        for values, _ in pairs
    ]
    equations += [
        sum(a * derivative[n] for a, n in zip(coefficients, FREQUENCIES))
        for _, derivative in pairs
    ]
    equations += [
        efficiency * cost(n)
        - source_coefficient(n, shift)
        - sum(weights[j] * pairs[j][0][n] for j in range(4))
        for n in FREQUENCIES
    ]
    equations.append(1 / shift**2 - coefficients[1] / (shift + 1)**2)
    return equations


def describe(coefficients, cosines, weights, efficiency, shift, residual, digits):
    def number(value):
        return mp.nstr(value, digits - 10)

    return {
        "frequencies": FREQUENCIES,
        "coefficients": [number(a) for a in coefficients],
        "contact_cosines": [number(q) for q in cosines],
        "contact_weights": [number(w) for w in weights],
        "efficiency": number(efficiency),
        "shift": number(shift),
        "max_equation_residual": number(residual),
        "leading_denominator_without_quadratic_pole_cost": number(448 / efficiency),
        "kernel_at_pi": number(sum(a * (-1)**n for a, n in zip(coefficients, FREQUENCIES))),
    }


def explore(digits):
    mp.mp.dps = digits
    tolerance = mp.mpf(10) ** (15 - digits)
    initial = [mp.mpf(x) for x in (
        "-.26857", "-.7355", "-.95037", "-.99989",
        ".11183916", ".0816504", ".08453074", ".04727236", ".017600",
    )]
    fixed = list(mp.findroot(fixed_shift_equations, tuple(initial), tol=tolerance, maxsteps=80))
    pairs = [chebyshev_values(q) for q in fixed[:4]]
    rows = [values for values, _ in pairs] + [derivative for _, derivative in pairs]
    matrix = mp.matrix([[row[n] for n in FREQUENCIES[1:]] for row in rows])
    coefficients = [mp.mpf(1)] + list(mp.lu_solve(matrix, mp.matrix([-1] * 4 + [0] * 4)))
    fixed_result = describe(
        coefficients, fixed[:4], fixed[4:8], fixed[8], mp.mpf(13) / 4,
        max(abs(x) for x in fixed_shift_equations(*fixed)), digits,
    )
    initial_free = coefficients[1:] + fixed[:8] + [fixed[8], mp.mpf(13) / 4]
    free = list(mp.findroot(free_shift_equations, tuple(initial_free), tol=tolerance, maxsteps=50))
    free_result = describe(
        [mp.mpf(1)] + free[:8], free[8:12], free[12:16], free[16], free[17],
        max(abs(x) for x in free_shift_equations(*free)), digits,
    )
    return {
        "status": "Numerical stationary candidates only; no global optimality certificate.",
        "fixed_shift": fixed_result,
        "free_shift": free_result,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--digits", type=int, default=90)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.digits < 40:
        parser.error("--digits must be at least 40")
    result = json.dumps(explore(args.digits), indent=2) + "\n"
    if args.output:
        args.output.write_text(result)
    else:
        print(result, end="")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact blocked Frobenius-screen prototype; native order promises are NOT checked.

Run using the scratch venv described in implementation-notes.md.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import json
from math import gcd, isqrt

try:
    from flint import fmpz_mod_poly_ctx
except ImportError as exc:
    raise SystemExit("Requires python-flint; use the documented scratch venv.") from exc


def _product_tree(polynomials):
    """Balanced multiplication; retain all levels for a remainder tree."""
    levels = [list(polynomials)]
    while len(levels[-1]) > 1:
        current = levels[-1]
        levels.append([
            current[i] * current[i + 1] if i + 1 < len(current) else current[i]
            for i in range(0, len(current), 2)
        ])
    return levels


def _multipoint_eval(polynomial, points, context):
    """Evaluate using only monic divisors, including coincident points.

    No distinctness test, field interpolation, or inverse of a point difference.
    """
    if not points:
        return []
    levels = _product_tree([context([-point, 1]) for point in points])
    # Every leaf is monic; products remain monic over any modulus.
    remainders = [polynomial % levels[-1][0]]
    for level in reversed(levels[:-1]):
        assert all(divisor.is_monic() for divisor in level)
        remainders = [remainders[i // 2] % divisor
                      for i, divisor in enumerate(level)]
    return [int(remainder[0]) for remainder in remainders]


def orbit_product(modulus: int, w: int, length: int) -> int:
    """Return product_(j=1..length)(w**j - 1) modulo modulus.

    This kernel is valid for arbitrary modulus >= 2 and even nonunit w.
    Its loop counts are O(sqrt(length)), apart from polynomial arithmetic.
    """
    if modulus < 2 or length < 0:
        raise ValueError("Require modulus >= 2 and length >= 0")
    if length == 0:
        return 1
    w %= modulus
    b = isqrt(length)
    if b * b < length:
        b += 1
    full_blocks, tail = divmod(length, b)
    context = fmpz_mod_poly_ctx(modulus)
    leaves = []
    power = w
    for _ in range(b):
        leaves.append(context([-1, power]))
        power = power * w % modulus
    block_polynomial = _product_tree(leaves)[-1][0]
    # F_b(X)=product_(r=1..b)(w**r X - 1).
    step = pow(w, b, modulus)
    point = 1
    points = []
    for _ in range(full_blocks):
        points.append(point)
        point = point * step % modulus
    values = _multipoint_eval(block_polynomial, points, context)
    result = 1
    for value in values:
        result = result * value % modulus
    power = pow(w, full_blocks * b, modulus)
    for _ in range(tail):
        power = power * w % modulus
        result = result * (power - 1) % modulus
    return result


@dataclass(frozen=True)
class ScreenResult:
    N: int
    k: int
    A: int
    B: int
    w: int
    Z: int
    gcd: int
    block_size: int
    full_blocks: int
    tail: int
    native_order_contract_verified: bool = False


def screen_details(N: int, k: int, q: int) -> ScreenResult:
    """Compute the requested formula; check only cheap public preconditions.

    Semiprimality and the two hidden local-order bounds are not verified.
    A result of N is returned unchanged, never silently interpreted as a factor.
    """
    if N < 2 or k < 1:
        raise ValueError("Require N >= 2 and k >= 1")
    if N > k ** 6:
        raise ValueError("Public size condition N <= k**6 is false")
    if gcd(q, N) != 1:
        raise ValueError("q must be a unit modulo N")
    A = 16 * k * k + 1
    B = N // (A * A)
    w = pow(q, N, N)
    Z = orbit_product(N, w, B)
    b = isqrt(B)
    if b * b < B:
        b += 1
    blocks, tail = divmod(B, b) if b else (0, 0)
    return ScreenResult(N, k, A, B, w, Z, gcd(Z, N), b, blocks, tail)


def frobenius_screen(N: int, k: int, q: int) -> int:
    """Return gcd(product_(j=1..B)(q**(N*j)-1), N)."""
    return screen_details(N, k, q).gcd


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int)
    parser.add_argument("k", type=int)
    parser.add_argument("q", type=int)
    args = parser.parse_args()
    try:
        result = screen_details(args.N, args.k, args.q)
    except ValueError as exc:
        parser.error(str(exc))
    print(json.dumps(asdict(result), sort_keys=True))


if __name__ == "__main__":
    main()

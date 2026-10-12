#!/usr/bin/env python3
"""Exact carry bookkeeping, followed by a floating phase diagnostic.

This is optional local research tooling, not a theorem or a CI certificate.
The tested rows are choose(2N,N) and choose(3N,N). All positive prime-power
carry orders are summed exactly. No floating result supplies an asymptotic
source assertion; the companion Lean leaf proves the uniform excess bound.
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
from pathlib import Path


def primes_through(limit: int) -> list[int]:
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for prime in range(2, math.isqrt(limit) + 1):
        if flags[prime]:
            flags[prime * prime : limit + 1 : prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1
            )
    return [prime for prime in range(2, limit + 1) if flags[prime]]


def binomial_valuation(prime: int, a: int, b: int) -> int:
    order = prime
    result = 0
    while order <= a + b:
        result += (a + b) // order - a // order - b // order
        order *= prime
    return result


def probe(n: int, height: float, beta: float) -> dict:
    full = 0j
    common = 0j
    correction = 0j
    absolute_excess = 0.0
    exceptional = []
    for prime in primes_through(3 * n):
        v1 = binomial_valuation(prime, n, n)
        v2 = binomial_valuation(prime, 2 * n, n)
        product = v1 * v2
        boolean = int(v1 > 0 and v2 > 0)
        excess = product - boolean
        assert excess >= 0
        weight = math.log(prime) * cmath.exp(-1j * height * math.log(prime))
        full += weight * product
        common += weight * boolean
        correction += weight * excess
        if excess:
            assert prime * prime <= 3 * n
            exceptional.append([prime, v1, v2, excess])
            absolute_excess += math.log(prime) * excess
    residual = abs(full - common - correction)
    assert residual <= 1e-8 * (1 + abs(full) + abs(common) + abs(correction))
    return {
        "N": n,
        "physical_top": 3 * n,
        "height": height,
        "beta": beta,
        "exact_exceptional_rows_p_v1_v2_excess": exceptional,
        "full_complex": [full.real, full.imag],
        "unpaid_common_complex": [common.real, common.imag],
        "correction_complex": [correction.real, correction.imag],
        "absolute_excess": absolute_excess,
        "source_scaled_absolute_excess": absolute_excess / (3 * n) ** beta,
        "floating_ledger_residual": residual,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--height", type=float, default=54.0)
    parser.add_argument("--beta", type=float, default=19999 / 20000)
    parser.add_argument("--orders", type=int, nargs="+", default=[32, 128, 512, 2048, 8192, 32768])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if any(n <= 0 for n in args.orders):
        parser.error("orders must be positive")
    result = {
        "schema": "kummer-gcd-local-diagnostic-v1",
        "proof": False,
        "source_or_zero_exclusion_certified": False,
        "exact_arithmetic": "All carry orders, nonnegative excess, square-root support",
        "floating_diagnostics": "Complex phase sums and normalization only",
        "samples": [probe(n, args.height, args.beta) for n in args.orders],
    }
    encoded = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    else:
        print(encoded, end="")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Optional finite sieve-cost probe; not a signed-carrier certificate.

Run manually with ../.venv/bin/python. Ordinary builds and CI do not run it.
The displayed rate omits countingConstant, hinge factors and the actual
masked variation. It therefore proves no error payment or arithmetic floor.
"""

import argparse
import json
import math
from pathlib import Path

import numpy as np


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="+", default=[32, 64, 128, 256, 640, 1536, 4096])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if any(n < 1 for n in args.orders):
        parser.error("orders must be positive")
    bound = max(args.orders) ** 2
    sieve = np.ones(bound + 1, dtype=np.bool_)
    sieve[:2] = False
    for p in range(2, math.isqrt(bound) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    primes = np.flatnonzero(sieve)
    weights = np.exp(-0.75 * np.log(primes.astype(float)))
    cumulative = np.cumsum(np.log1p(weights * (1 + weights)))
    rows = []
    for n in args.orders:
        count = int(np.searchsorted(primes, n * n, side="right"))
        cost = float(cumulative[count - 1]) if count else 0.0
        rate = cost - n / 128 + n * math.log(10001 / 10000)
        rows.append({"N": n, "prime_count": count,
                     "log_weighted_exclusion_cost": cost,
                     "log_source_rate_prefactor": rate})
    report = {"scope": "Optional numerical evaluation of the exact finite "
              "sieveCost(3/4, primes <= N^2) prefactor only; neither literal "
              "variation nor signed carrier evaluated; not a certificate or floor.",
              "radius_ceiling": "10001/20000", "rows": rows}
    output = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()

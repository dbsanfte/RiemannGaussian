#!/usr/bin/env python3
"""Optional exact endpoint certificates; no build/CI hook or zero claim."""
from fractions import Fraction as F
import json
import math


def main():
    u = F(10001, 20000)
    sigma = 1 + F(1, 1048576)
    rows = []
    for name, endpoint, root in [
        ("lower", F(1971, 1000), F(99985495, 100000000)),
        ("upper", F(2029, 1000), F(100014497, 100000000)),
    ]:
        assert u * endpoint <= root**100
        bound = 100 * (root - 1) + 1 - (F(3, 2) - sigma) * endpoint
        assert bound <= -F(1, 1000000)
        actual = math.log(float(u * endpoint)) + 1 - float((F(3, 2) - sigma) * endpoint)
        rows.append({"side": name, "endpoint": str(endpoint),
                     "certified_exponent": str(bound),
                     "exploratory_exponent": actual})
    for n in [1000, 4096, 100000]:
        assert F(197, 100) * n + 1 <= F(1971, 1000) * n
        assert F(2029, 1000) * n <= F(203, 100) * n - 1
    print(json.dumps({"exact_certificates": rows,
                      "boundary_geometry": "passed",
                      "scope": "Constant-width radial clips only; no whole-floor deficit or effective asymptotic start."}, indent=2))


if __name__ == "__main__":
    main()

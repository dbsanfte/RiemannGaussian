#!/usr/bin/env python3
"""Optional actual-xi normal-growth probe; not an arithmetic packet estimate.

Uses the repository normalization xi(s)=s(1-s)*Gamma_R(s)*zeta(s).
At v=2 and z=2n+3, reflection gives xi(v-z)=xi(2n+2).
The exact norm xi(2)=pi/3 fixes the denominator normalization.
No zero data, prime-density approximation, or finite-mode truncation is used.
"""

import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp


def row(n, primitive_orders):
    log_xi_even = (
        mp.log(2 * (n + 1) * (2 * n + 1))
        + mp.loggamma(n + 1)
        - (n + 1) * mp.log(mp.pi)
        + mp.log(mp.zeta(2 * n + 2))
    )
    log_ratio = log_xi_even - mp.log(mp.pi / 3)
    # All chosen n have ratio > 1; expm1 keeps the subtraction stable.
    assert log_ratio > 0
    log_numerator = log_ratio + mp.log(-mp.expm1(-log_ratio))
    return {
        "n": n,
        "z": 2 * n + 3,
        "log10_norm_after_primitive": {
            str(r): mp.nstr(
                (log_numerator - (r + 2) * mp.log(2 * n + 3)) / mp.log(10), 24
            )
            for r in primitive_orders
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    mp.mp.dps = 80
    orders = [0, 10, 100]
    report = {
        "status": "Actual-xi transform exploration; no literal packet or zero-free estimate.",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "mpmath": mp.__version__,
        "precision_decimal_digits": mp.mp.dps,
        "v": 2,
        "primitive_orders": orders,
        "quantity": "abs((1-xi(2-z)/xi(2))/z**(r+2)), z=2n+3",
        "rows": [row(n, orders) for n in [16, 32, 64, 128, 256, 512, 1024]],
        "interpretation": [
            "Finite negative-mode weak inverses retain triangular support.",
            "The actual complete xi count factor has factorial normal growth.",
            "Every fixed primitive eventually grows; initial small values are misleading.",
            "Lean proves the fixed-primitive domination obstruction independently of this probe.",
            "The result does not assert divergence of an arithmetic packet.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"report": str(args.output), "last_row": report["rows"][-1]}, indent=2))


if __name__ == "__main__":
    main()

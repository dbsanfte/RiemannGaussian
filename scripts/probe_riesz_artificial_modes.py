#!/usr/bin/env python3
"""Optional regression of finite artificial-mode interpolation and its joint lift.

No zeta data or arithmetic packet approximation is used. The fixed slice
is w=1,z=-t; neighboring slices use z=-w*t so the selected pole is t=1.
"""

import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp


def string(x):
    return mp.nstr(x, 30)


def remaining_tail(m, a, n):
    # Exact convergent hypergeometric expression for sum_{j>n} [t^j](1-a*t)^(-m).
    return mp.binomial(n+m, m-1)*a**(n+1)*mp.hyp2f1(1, m+n+1, n+2, a)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    mp.mp.dps = 90
    orders = [1, 3, 5, 8, 12, 16, 32, 128, 640, 4096]
    rows = []
    for m in [8, 16, 64]:
        a = 1-mp.root(2, m)
        xi = 1-1/a
        sample = {
            "m": m, "a": string(a), "artificial_pole_t": string(1/a),
            "fixed_mode_location_xi": string(xi), "slices": [],
        }
        for w in map(mp.mpf, ["0.99", "0.999", "1", "1.001", "1.01"]):
            b = w/(w-xi)
            surface = (1-w/xi)**m
            mismatch = surface-1/(w+1)
            # At the exactly interpolated slice enforce the algebraic equality,
            # so finite working-precision subtraction does not mask a tiny tail.
            if w == 1:
                mismatch = mp.mpf(0)
            sample["slices"].append({
                "w": string(w), "normalized_parameter": string(b),
                "surface_mismatch": string(mismatch),
                "normal_residue": string(mismatch/w),
                "residual_coefficients": {
                    str(n): string(mismatch-remaining_tail(m, b, n)) for n in orders
                },
            })
        rows.append(sample)
    report = {
        "status": "Toy finite-renormalization regression; no actual-zeta or packet estimate.",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "precision_decimal_digits": mp.mp.dps, "mpmath": mp.__version__,
        "slice_coefficient": "[t^N]((1-b_w*t)^(-m)-(1-w*t/(w+1)))/(1-t)",
        "two_variable_factor": "((w-xi)/(w+z-xi))^m",
        "selected_pole_surface": "w+z=0",
        "surface_mismatch": "(1-w/xi)^m-1/(w+1)",
        "rows": rows,
        "interpretation": [
            "At w=1, m=8 reproduces the supplied geometrically decaying coefficient table.",
            "For nearby w, coefficients instead approach the nonzero surface mismatch.",
            "Pushing the fixed artificial poles farther out does not make the polynomial trace equal a reciprocal.",
            "Lean proves the local surface mismatch for every fixed finite complex mode family, not only repeated modes.",
            "The failure concerns joint pole removal; it does not disprove other coupled decay estimates for the actual carrier.",
            "Choosing mode locations depending on w would fall outside the fixed-mode support theorem.",
            "Numerical values are exploratory; no physical-cutoff or arithmetic bridge is claimed.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"report": str(args.output), "m8_a": rows[0]["a"],
                      "m8_neighbor_mismatch": rows[0]["slices"][3]["surface_mismatch"]}, indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Optional count-factor stability probe; no actual-zeta or packet estimate.

The meromorphic leg generator is integrated before exponentiation.  For an
analytic leg A(t), B'(t)=-A(t), B(0)=0, and H(t)=exp(B(t)).  The selected
negative mode has count factor 1/(1-t), not exp(-1/(1-t)).
"""

import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp


def exp_coefficients(b):
    h = [mp.exp(b[0])]
    for n in range(1, len(b)):
        h.append(mp.fsum(k * b[k] * h[n-k] for k in range(1, n+1)) / n)
    return h


def negative_count_coefficients(nodes, nmax):
    p = [mp.mpf(1)] + [mp.mpf(0)] * nmax
    for node in nodes:
        for n in range(1, nmax + 1):
            p[n] += p[n-1] / node
    return p


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    mp.mp.dps = 70
    h_degree = 512
    orders = [32, 128, 512, 2048, 8192]
    a, r = mp.mpf("0.1"), mp.mpf("0.75")
    models = [
        ("constant_leg", lambda n: a if n == 0 else mp.mpf(0), -a),
        ("linear_leg", lambda n: a if n == 1 else mp.mpf(0), -a/2),
        ("geometric_leg", lambda n: a*r**n, a/r*mp.log(1-r)),
        ("finite_geometric_envelope_leg", lambda n: a*r**n if n < 16 else mp.mpf(0),
         -mp.fsum(a*r**n/(n+1) for n in range(16))),
        ("exact_counterexample_leg", lambda n: mp.mpf(2)**(-n-1), mp.log(mp.mpf("0.5"))),
    ]
    factors = []
    for name, leg, b_at_one in models:
        b = [mp.mpf(0)] + [-leg(n-1)/n for n in range(1, h_degree+1)]
        h = exp_coefficients(b)
        factors.append((name, h, mp.expm1(b_at_one)))
    # A constant COUNT exponent is a different experiment from a constant LEG.
    factors.append(("constant_count_exponent", [mp.exp(a)] + [mp.mpf(0)]*h_degree,
                    mp.expm1(a)))
    rows = []
    for nodes in [[mp.mpf(1)], [mp.mpf(1), mp.mpf(8)/5],
                  [mp.mpf(1), mp.mpf(8)/5, mp.mpf(9)/5]]:
        p = negative_count_coefficients(nodes, max(orders))
        q_at_one = mp.fprod(1/(1-1/node) for node in nodes[1:])
        for name, h, residue_factor in factors:
            difference = h.copy()
            difference[0] -= 1
            rows.append({
                "model": name,
                "negative_mode_nodes": [mp.nstr(x, 20) for x in nodes],
                "coefficient_samples": {
                    str(n): mp.nstr(mp.fsum(difference[k]*p[n-k]
                                           for k in range(min(n, h_degree)+1)), 25)
                    for n in orders
                },
                "predicted_coefficient_limit": mp.nstr(q_at_one*residue_factor, 25),
                "principal_part_numerator_over_t_minus_one":
                    mp.nstr(-q_at_one*residue_factor, 25),
            })
    s, d = mp.mpf(9)/20, mp.mpf(3)/20
    report = {
        "status": "Toy analytic-factor no-go; not an actual zeta remainder or arithmetic estimate.",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "mpmath": mp.__version__,
        "precision_decimal_digits": mp.mp.dps,
        "analytic_factor_series_degree": h_degree,
        "coefficient_quantity": "[t^N] product_j(1-t/node_j)^(-1)*(exp(B(t))-1)",
        "normalization": "B'(t)=-A_leg(t), B(0)=0; constant_count_exponent is explicitly separate",
        "rows": rows,
        "ordinary_inverse_counterexample": {
            "leg": "1/(2-t)",
            "factor": "(w+z+1)/(w+1)",
            "full_response": "1/(z*(w+z)*(w+1))",
            "inverse_for_positive_s_d": "exp(-s)*(exp(min(s,d))-1)",
            "s": "9/20", "d": "3/20", "gap": "3/10 > 7/25",
            "largest_share": "11/20 in [43/80,9/16]",
            "inverse_value": mp.nstr(mp.exp(-s)*mp.expm1(d), 30),
        },
        "interpretation": [
            "A radius greater than one for an analytic leg does not ensure decay after count multiplication.",
            "The residue depends on B(1), the integrated leg remainder, and on the other-mode prefactor.",
            "A constant count multiplier alone preserves support, despite a nondecaying coefficient sequence.",
            "Consequently coefficient persistence alone is not the support no-go; the exact double inverse is.",
            "Lean independently proves the rational inverse and its nonzero value below the core gap.",
            "The series truncation and numerical samples are exploration, not rigorous error certificates.",
            "No physical cutoff, generic Abel transport, or literal packet estimate is asserted.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"report": str(args.output), "inverse_value": report[
        "ordinary_inverse_counterexample"]["inverse_value"],
        "models": len(rows), "largest_order": max(orders)}, indent=2))


if __name__ == "__main__":
    main()

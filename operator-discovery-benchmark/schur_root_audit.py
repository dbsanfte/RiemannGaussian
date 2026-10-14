#!/usr/bin/env python3
"""Resolve root-correction zero-free cases using certified Schur reduction.

The polynomial is certified on a disk with Arb balls. A proved analytic tail
then transfers its zero count to the full local Euler factor by Rouche's
theorem. A failed certificate is unresolved, never a zero counterexample.
"""

from __future__ import annotations

import json
from fractions import Fraction as Q
from pathlib import Path
import time

import flint

from carry_zero_audit import tail_bound
from check_carry_certificates import coefficients


def ball_rational(value):
    value = Q(value)
    return flint.arb(value.numerator) / value.denominator


def schur_certificate(local_coefficients, radius, tail, precision=600):
    flint.ctx.prec = precision
    r = ball_rational(radius)
    polynomial = [ball_rational(value) * r ** e
                  for e, value in enumerate(local_coefficients)]
    if local_coefficients[0] != 1:
        raise ValueError("The certificate requires a normalized constant term")
    margin = flint.arb(1)
    reflection_bounds = []
    for degree in range(len(polynomial) - 1, 0, -1):
        last = polynomial[-1]
        cap = last.abs_upper()
        reflection_bounds.append({"degree": degree, "reflection_absolute_upper_ball": str(cap)})
        if not bool(cap < 1):
            return {"schur_polynomial_disk_certified": False,
                    "full_local_disk_certified": False, "first_failed_degree": degree,
                    "reflection_bounds": reflection_bounds}
        margin *= 1 - cap
        denominator = 1 - last * last
        # The new constant is mathematically exactly 1. Setting it exactly
        # removes avoidable interval dependency from (1-last**2)/(1-last**2).
        polynomial = [flint.arb(1)] + [
            (polynomial[k] - last * polynomial[degree - k]) / denominator
            for k in range(1, degree)]
    tail_ball = ball_rational(tail)
    passed = bool(margin > tail_ball)
    return {"schur_polynomial_disk_certified": True,
            "full_local_disk_certified": passed,
            "first_failed_degree": None, "precision_bits": precision,
            "boundary_modulus_lower_ball": str(margin.lower()),
            "boundary_modulus_decimal_diagnostic": float(margin.mid()),
            "analytic_tail_upper_ball": str(tail_ball.upper()),
            "analytic_tail_decimal_diagnostic": float(tail_ball.mid()),
            "reflection_bounds": reflection_bounds}


def cocycle_coefficients(order, prime, parameter, degree):
    """Separate coefficient route: ordinary convolution under the transport.

    The discovery/verifier route instead uses integer binomial valuations
    inside every weighted convolution. The two routes must agree exactly.
    """
    def factorial_value(n):
        result = 0
        while n:
            n //= prime
            result += n
        return result
    root = [Q(1)]
    for e in range(1, degree + 1):
        root.append(root[-1] * (Q(1, order) + e - 1) / e)
    transported = [value / parameter ** factorial_value(e) for e, value in enumerate(root)]
    polynomial = [Q(1)] + [Q(0)] * degree
    for _ in range(order):
        polynomial = [sum((polynomial[i] * transported[e-i] for i in range(e+1)), Q(0))
                      for e in range(degree+1)]
    lifted = [value * parameter ** factorial_value(e) for e, value in enumerate(polynomial)]
    return [lifted[0]] + [lifted[e] - lifted[e-1] for e in range(1, degree+1)]


def main():
    started = time.monotonic()
    output = Path(__file__).resolve().parent / "root-results"
    source = json.loads((output / "carry_zero_audit.json").read_text())
    unresolved = [record for record in source["certificates"]
                  if not record["certifies_no_correction_zeros_Re_s_gt_half"]]
    degree, radius = 192, Q(71, 100)
    results = []
    for record in unresolved:
        order, operator = record["root_order"], record["operator"]
        prime, parameter = operator["prime"], Q(operator["parameter"])
        local = coefficients(order, prime, parameter, degree)
        independent = cocycle_coefficients(order, prime, parameter, degree)
        agreement = local == independent
        if not agreement:
            raise AssertionError("Independent exact coefficient computations disagree")
        tail, theorem = tail_bound(order, operator["parameter"], degree, radius)
        certified = schur_certificate(local, radius, tail)
        result = {"root_order": order, "operator": operator, "radius": str(radius),
                  "local_degree": degree, "exact_local_coefficients": [str(value) for value in local],
                  "independent_exact_coefficient_routes_agree": agreement,
                  "tail_theorem": theorem, "tail_rational": str(tail),
                  "proof": "schur_root_proof.txt", **certified,
                  "certifies_nonzero_correction_Re_s_gt_half": certified["full_local_disk_certified"],
                  "historical_novelty": "unresolved", "counts_as_verified_new_operator": False}
        results.append(result)
        print(f"Schur audit q={order}, prime={prime}, t={parameter}: certified={result['certifies_nonzero_correction_Re_s_gt_half']}", flush=True)
    result = {"previously_unresolved": len(unresolved), "records": results,
              "newly_certified": sum(x["certifies_nonzero_correction_Re_s_gt_half"] for x in results),
              "elapsed_seconds": time.monotonic() - started, "verified_new_operators": []}
    destination = output / "schur_root_audit.json"
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Saved {destination}; elapsed {result['elapsed_seconds']:.1f}s", flush=True)


if __name__ == "__main__":
    main()

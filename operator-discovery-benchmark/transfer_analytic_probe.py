#!/usr/bin/env python3
"""Compare the nonlinear arithmetic transfer to fresh actual zeta values.

Uses Arb complex balls, a direct generic arithmetic LOG/EXP computation,
independent bit-partition local coefficients, and proved uniform tails.
"""

from __future__ import annotations

import json
from fractions import Fraction as Q
from pathlib import Path

import flint

from check_root_transfer import partitions
from exact_arithmetic import factorization, sequence
from root_transfer_probe import transfer


def partition_coefficients(degree):
    result = [Q(1)]
    for e in range(1, degree + 1):
        bits = [1 << j for j in range(e.bit_length()) if e & (1 << j)]
        value = Q(0)
        for partition in partitions(bits):
            summand = Q(1)
            for block in partition:
                summand /= sum(block)
            value += summand
        result.append(value)
    return result


def ball(value):
    value = Q(value)
    return flint.arb(value.numerator) / value.denominator


def analytic_checks(cutoff=512, prime_cutoff=257, local_degree=32):
    flint.ctx.prec = 350
    # This coefficient route is generic, including nonmultiplicative inputs.
    arithmetic = transfer(sequence([1] * cutoff))
    # Separate route for the Euler product: partitions of exponent bits.
    local = partition_coefficients(local_degree)
    predicted = [Q(0), Q(1)]
    for n in range(2, cutoff + 1):
        value = Q(1)
        for e in factorization(n).values():
            value *= local[e]
        predicted.append(value)
    assert arithmetic == predicted
    correction = [local[0]] + [local[e] - local[e-1]
                               for e in range(1, local_degree + 1)]
    primes = [n for n in range(2, prime_cutoff + 1) if factorization(n) == {n: 1}]
    records = []
    for sigma, height in ((3, "0"), (3, "41.17"), (4, "97.31"),
                          (4, "-83.19"), (6, "211.07"), (6, "-193.13")):
        s = flint.acb(sigma, height)
        finite_sum = flint.acb(0)
        for n in range(1, cutoff + 1):
            finite_sum += ball(arithmetic[n]) * (-s * flint.arb(n).log()).exp()
        product = flint.acb(1)
        for prime in primes:
            x = (-s * flint.arb(prime).log()).exp()
            factor = flint.acb(0)
            for coefficient in reversed(correction):
                factor = factor * x + ball(coefficient)
            product *= factor
        zeta = s.zeta()
        two = flint.arb(2)
        # |H(n)|<=1 gives the Dirichlet sum tail. |r_e|<=2 is the
        # deliberately conservative local bound used in the written proof.
        series_tail = flint.arb(cutoff) ** (1-sigma) / (sigma-1)
        multiplier = 2 / (1 - two ** (-sigma))
        exponent = 2 * sigma
        full_product_majorant = (multiplier * (two ** (-exponent)
                                                + two ** (1-exponent) / (exponent-1))).exp()
        prime_tail_exponent = multiplier * flint.arb(prime_cutoff) ** (1-exponent) / (exponent-1)
        local_tail_exponent = sigma * (local_degree+1)
        local_tail_sum = multiplier * (two ** (-local_tail_exponent)
                                      + two ** (1-local_tail_exponent) / (local_tail_exponent-1))
        euler_error = full_product_majorant * (prime_tail_exponent.expm1() + local_tail_sum)
        allowed_error = series_tail + zeta.abs_upper() * euler_error
        error = (finite_sum - zeta * product).abs_upper()
        # Perturb one coefficient by an exact, controlled amount. This is
        # well outside the certified truncation errors and must be rejected.
        corrupted = finite_sum + ball(Q(1, 7)) * (-s * flint.arb(4).log()).exp()
        control_error = (corrupted - zeta * product).abs_lower()
        records.append({"s": [str(sigma), height], "coefficient_cutoff": cutoff,
                        "prime_cutoff": prime_cutoff, "local_degree": local_degree,
                        "difference_upper_ball": str(error),
                        "proved_combined_tail_bound_ball": str(allowed_error),
                        "within_proved_bound": bool(error < allowed_error),
                        "coefficient_4_perturbation": "1/7",
                        "perturbed_difference_lower_ball": str(control_error),
                        "perturbation_rejected": bool(control_error > allowed_error)})
    return {"generic_arithmetic_and_partition_coefficients_agree": arithmetic == predicted,
            "actual_zeta_ball_checks": records,
            "all_passed": all(x["within_proved_bound"] and x["perturbation_rejected"] for x in records),
            "proof": "root_transfer_proof.txt sections 4, 5 and 7",
            "limitation": "Fresh samples verify implementations; the wider zero-preserving domain comes from proof, not samples"}


def main():
    result = analytic_checks()
    destination = Path(__file__).resolve().parent / "transfer-results" / "transfer_analytic_probe.json"
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Actual zeta transfer checks: {sum(x['within_proved_bound'] for x in result['actual_zeta_ball_checks'])}/6; negative controls rejected: {sum(x['perturbation_rejected'] for x in result['actual_zeta_ball_checks'])}/6")
    assert result["all_passed"]


if __name__ == "__main__":
    main()

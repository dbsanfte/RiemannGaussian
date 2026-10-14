#!/usr/bin/env python3
"""Independent rational bit-partition and Bernstein verification.

No FLINT or production polynomial/search implementation is imported.
The finite witnesses support the universal argument in dyadic_root_proof.txt;
they do not independently establish historical originality or RH.
"""

from __future__ import annotations

from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import json

from check_root_transfer import bernstein, partitions, poly_add, poly_mul, trim


def independent_local_polynomial(exponent):
    if not exponent:
        return [Q(1)]
    bits = [1 << j for j in range(exponent.bit_length()) if exponent & (1 << j)]
    output = [Q(0)]
    for partition in partitions(bits):
        weight = Q(1)
        for block in partition:
            weight /= sum(block)
        term = [Q(0)]*len(partition) + [weight]
        output = poly_add(output, term)
    return output


def independent_corrections(local, degree):
    ordinary = [[Q(1)]]
    for exponent in range(1, degree+1):
        falling = [Q(1)]
        for j in range(exponent):
            falling = poly_mul(falling, [Q(-j), Q(1)])
        ordinary.append([x*Q((-1)**exponent, factorial(exponent)) for x in falling])
    output = []
    for exponent in range(degree+1):
        value = [Q(0)]
        for j in range(exponent+1):
            value = poly_add(value, poly_mul(ordinary[j], local[exponent-j]))
        output.append(value)
    return output


def evaluate(poly, parameter):
    return sum((coefficient*parameter**j for j, coefficient in enumerate(poly)), Q(0))


def main():
    output = Path(__file__).resolve().parent/"dyadic-results"
    source = json.loads((output/"dyadic_root_search.json").read_text())
    stored = [trim([Q(x) for x in coefficients] or [Q(0)])
              for coefficients in source["local_polynomial_coefficients"]]
    independent = [independent_local_polynomial(e) for e in range(len(stored))]
    local_agreement = independent == stored
    cert = source["uniform_real_parameter_certificate"]
    degree = cert["degree"]
    corrections = independent_corrections(independent, degree)
    stored_corrections = [trim([Q(x) for x in coefficients] or [Q(0)])
                          for coefficients in source["correction_polynomial_coefficients"]]
    correction_agreement = corrections == stored_corrections
    lower, upper = map(Q, cert["beta_interval"])
    radius = Q(cert["radius"])
    bounds_agree, finite = True, Q(0)
    expected_exponents = list(range(2, degree+1))
    complete = [x["exponent"] for x in cert["coefficient_bounds"]] == expected_exponents
    for detail in cert["coefficient_bounds"]:
        exponent = detail["exponent"]
        values = bernstein(corrections[exponent], lower, upper)
        cap = max(map(abs, values))
        bounds_agree &= [str(x) for x in values] == detail["bernstein_coefficients"]
        bounds_agree &= cap == Q(detail["coefficient_bound"])
        finite += cap*radius**exponent
    tail = 2*radius**(degree+1)/(1-radius)
    total = finite+tail
    search = source["search"]
    search_agreement = True
    counterexamples = []
    fresh = [Q(search["training_beta"])] + [Q(x) for x in search["fresh_beta_values"]]
    for detail in search["all_candidates"]:
        m, scale = detail["multiplier"], Q(detail["learned_parameter_scale"])
        training = all(evaluate(independent[m*e], Q(1)) == evaluate(independent[e], scale)
                       for e in search["training_exponents"])
        passed = True
        count = 0
        first = None
        for parameter in fresh:
            for e in range(1, search["held_out_exponent_cutoff"]+1):
                if parameter == 1 and e in search["training_exponents"]:
                    continue
                left = evaluate(independent[m*e], parameter)
                right = evaluate(independent[e], scale*parameter)
                count += 1
                if left != right:
                    passed = False
                    if first is None:
                        first = {"beta": str(parameter), "exponent": e,
                                 "observed": str(left), "predicted": str(right)}
        search_agreement &= training == detail["training_passed"]
        search_agreement &= passed == detail["held_out_passed"]
        search_agreement &= count == detail["held_out_checks"]
        search_agreement &= first == detail["first_counterexample"]
        if first is not None:
            counterexamples.append(m)
    checks = {
        "independent_bit_partition_polynomials_agree": local_agreement,
        "independent_binomial_correction_polynomials_agree": correction_agreement,
        "all_degree_48_Bernstein_coefficients_agree": bool(bounds_agree),
        "every_required_coefficient_is_present": complete,
        "entire_real_parameter_interval_covered": lower == 0 and upper == 1,
        "constant_and_linear_terms_correct": corrections[0] == [Q(1)] and corrections[1] == [Q(0)],
        "quadratic_term_exactly_minus_beta_squared_over_two": corrections[2] == [Q(0), Q(0), Q(-1, 2)],
        "finite_head_bound_agrees": finite == Q(cert["finite_sum_bound"]),
        "tail_bound_agrees": tail == Q(cert["uniform_tail_bound"]),
        "rational_total_agrees": total == Q(cert["total_bound"]),
        "strict_nonzero_disk_witness": total < 1 and radius**2 > Q(1, 2),
        "all_training_and_held_out_decisions_recomputed": bool(search_agreement),
        "all_31_models_present": [x["multiplier"] for x in search["all_candidates"]] == list(range(2, 33)),
    }
    result = {"checks": checks, "all_passed": all(checks.values()),
              "independent_local_exponent_lookahead": len(independent)-1,
              "rejected_training_fits": counterexamples,
              "total_bound_decimal_diagnostic": float(total),
              "proof": "dyadic_root_proof.txt"}
    (output/"dyadic_root_verification.json").write_text(json.dumps(result, indent=2)+"\n")
    print(f"Independent dyadic extraction, partition and rational witnesses: {result['all_passed']}")
    assert result["all_passed"]


if __name__ == "__main__":
    main()

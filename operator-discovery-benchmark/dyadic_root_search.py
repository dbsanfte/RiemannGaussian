#!/usr/bin/env python3
"""Learn exponent extraction laws and certify a real zeta-root parameter.

The secondary grammar is explicitly allowed prime-exponent indices, a
scalar fitted from training data, and formal arithmetic LOG/EXP. No dyadic
index restriction or target parameter-scaling law is supplied to the fit.
"""

from __future__ import annotations

import json
from fractions import Fraction as Q
from pathlib import Path
import random
import time

import flint

from exact_arithmetic import convolve, sequence
from root_transfer_probe import (algebra_exp, bernstein_bound, evaluate,
                                 local_no_carry_product,
                                 no_carry_arithmetic_product)


def parameter_polynomials(degree):
    """Generic local EXP_A(beta LOG_D(u)), using no factor/partition formula."""
    beta = flint.fmpq_poly([0, 1])
    zero, one = flint.fmpq_poly(), flint.fmpq_poly([1])
    source = [zero] + [beta / e for e in range(1, degree + 1)]
    term = [one] + [zero] * degree
    output = list(term)
    coefficient = Q(1)
    maximum_factors = max(e.bit_count() for e in range(degree + 1))
    for k in range(1, maximum_factors + 1):
        term = local_no_carry_product(term, source)
        coefficient /= k
        output = [a + b * flint.fmpq(coefficient.numerator, coefficient.denominator)
                  for a, b in zip(output, term)]
    return output


def correction_polynomials(local):
    """Coefficients of (1-x)^beta times the local no-carry exponential."""
    beta = flint.fmpq_poly([0, 1])
    ordinary = [flint.fmpq_poly([1])]
    for e in range(1, len(local)):
        ordinary.append(ordinary[-1] * (e - 1 - beta) / e)
    return [sum((ordinary[j] * local[e-j] for j in range(e+1)),
                flint.fmpq_poly()) for e in range(len(local))]


def search_extraction(polynomials, maximum_multiplier=32, held_exponent=12):
    candidates = []
    # Data are anonymized local coefficient profiles. The one scalar is
    # inferred from e=1. Subsequent exponents and parameters are withheld.
    training_parameter = Q(1)
    fresh_parameters = (Q(1), Q(-1, 2), Q(2, 3), Q(3, 2), Q(5, 7))
    for multiplier in range(2, maximum_multiplier+1):
        scale = evaluate(polynomials[multiplier], training_parameter)
        training_passed = all(
            evaluate(polynomials[multiplier*e], training_parameter)
            == evaluate(polynomials[e], scale*training_parameter)
            for e in (1,))
        if not training_passed:
            continue
        counterexample = None
        checks = 0
        for parameter in fresh_parameters:
            for e in range(1, held_exponent+1):
                if parameter == training_parameter and e == 1:
                    continue
                left = evaluate(polynomials[multiplier*e], parameter)
                right = evaluate(polynomials[e], scale*parameter)
                checks += 1
                if left != right and counterexample is None:
                    counterexample = {"beta": str(parameter), "exponent": e,
                                      "observed": str(left), "predicted": str(right)}
        candidates.append({"multiplier": multiplier, "learned_parameter_scale": str(scale),
                           "training_passed": training_passed,
                           "held_out_checks": checks, "held_out_passed": counterexample is None,
                           "first_counterexample": counterexample})
    return {"index_grammar": "e -> m*e for each integer 2<=m<=32",
            "parameter_grammar": "beta -> c*beta, c fitted exactly from training",
            "training_beta": str(training_parameter), "training_exponents": [1],
            "fresh_beta_values": [str(x) for x in fresh_parameters[1:]],
            "held_out_exponent_cutoff": held_exponent,
            "declared_local_input_lookahead": maximum_multiplier*held_exponent,
            "models_scored": maximum_multiplier-1, "training_fits": len(candidates),
            "survivors": [x for x in candidates if x["held_out_passed"]],
            "rejected_training_fits": [x for x in candidates if not x["held_out_passed"]],
            "all_candidates": candidates}


def uniform_parameter_certificate(corrections, radius=Q(71, 100)):
    degree = len(corrections)-1
    finite, bounds = Q(0), []
    for e in range(2, degree+1):
        cap, bernstein = bernstein_bound(corrections[e], Q(0), Q(1))
        finite += cap * radius**e
        bounds.append({"exponent": e, "coefficient_bound": str(cap),
                       "bernstein_coefficients": [str(x) for x in bernstein]})
    tail = 2 * radius**(degree+1)/(1-radius)
    total = finite + tail
    return {"beta_interval": ["0", "1"], "radius": str(radius), "degree": degree,
            "finite_sum_bound": str(finite), "uniform_tail_bound": str(tail),
            "total_bound": str(total), "total_decimal_diagnostic": float(total),
            "linear_coefficient_identically_zero": not bool(corrections[1]),
            "strict_zero_free_bound_proved": total < 1 and radius**2 > Q(1, 2),
            "coefficient_bounds": bounds}


def local_extraction(values, multiplier):
    return [values[multiplier*e] for e in range((len(values)-1)//multiplier+1)]


def integer_extraction(values, multiplier):
    # Never silently replace an unavailable lookahead coefficient by zero.
    output = [Q(0)]
    n = 1
    while n**multiplier < len(values):
        output.append(values[n**multiplier])
        n += 1
    return output


def extraction_checks():
    rng = random.Random(2026100614)
    records = []
    for degree in (64, 128, 256):
        a, b = [[Q(rng.randint(-3, 3), rng.randint(1, 5)) for _ in range(degree+1)]
                for _ in range(2)]
        product = local_no_carry_product(a, b)
        for multiplier in (2, 4, 8, 16):
            passed = (local_extraction(product, multiplier)
                      == local_no_carry_product(local_extraction(a, multiplier),
                                                local_extraction(b, multiplier)))
            records.append({"local_lookahead_degree": degree, "multiplier": multiplier,
                            "endomorphism_law_passed": passed})
    a, b = [sequence([Q(rng.randint(-2, 2), rng.randint(1, 5)) for _ in range(256)])
            for _ in range(2)]
    product = no_carry_arithmetic_product(a, b)
    dense = []
    for multiplier in (2, 4, 8):
        left = integer_extraction(product, multiplier)
        right = no_carry_arithmetic_product(integer_extraction(a, multiplier),
                                           integer_extraction(b, multiplier))
        dense.append({"integer_input_cutoff": 256, "multiplier": multiplier,
                      "integer_output_cutoff": len(left)-1, "passed": left == right})
    rejected = []
    for multiplier in range(2, 33):
        if multiplier.bit_count() == 1:
            continue
        first = multiplier & -multiplier
        second = multiplier-first
        a, b = [[Q(0)]*(multiplier+1) for _ in range(2)]
        a[first] = b[second] = Q(1)
        left = local_extraction(local_no_carry_product(a, b), multiplier)
        right = local_no_carry_product(local_extraction(a, multiplier),
                                       local_extraction(b, multiplier))
        rejected.append({"multiplier": multiplier, "impulse_exponents": [first, second],
                         "extracted_product_coefficient_at_1": str(left[1]),
                         "product_of_extracted_coefficient_at_1": str(right[1]),
                         "false_endomorphism_rejected": left != right})
    # Ordinary multiplication permits a carry at exponents 1+1=2.
    impulse = sequence([0, 1, 0, 0])
    ordinary_left = integer_extraction(convolve(impulse, impulse), 2)
    ordinary_right = convolve(integer_extraction(impulse, 2),
                              integer_extraction(impulse, 2))
    ordinary_square_index_rejected = ordinary_left != ordinary_right
    normalized_impulse_input = sequence([1, 1, 0, 0])
    extracted_transfer = integer_extraction(direct_parameter_transfer(normalized_impulse_input, Q(1)), 2)
    halved_transfer = direct_parameter_transfer(normalized_impulse_input, Q(1, 2))
    zeta_specific_scaling_not_universal = extracted_transfer[2] != halved_transfer[2]
    return {"unrelated_local_inputs": records, "unrelated_arithmetic_inputs": dense,
            "non_dyadic_impulse_counterexamples": rejected,
            "ordinary_square_index_negative_control": {
                "input": "delta_p times delta_p under ordinary Dirichlet convolution",
                "E_2_of_product_at_p": str(ordinary_left[2]),
                "product_of_E_2_inputs_at_p": str(ordinary_right[2]),
                "rejected": ordinary_square_index_rejected},
            "overgeneralized_parameter_halving_negative_control": {
                "input": "f=delta_1+delta_2, f(1)=1",
                "E_2_T_1_f_at_2": str(extracted_transfer[2]),
                "T_one_half_f_at_2": str(halved_transfer[2]),
                "false_scaling_on_all_normalized_inputs_rejected": zeta_specific_scaling_not_universal},
            "all_passed": (all(x["endomorphism_law_passed"] for x in records)
                           and all(x["passed"] for x in dense)
                           and all(x["false_endomorphism_rejected"] for x in rejected)
                           and ordinary_square_index_rejected and zeta_specific_scaling_not_universal)}


def direct_parameter_transfer(values, beta):
    from exact_arithmetic import formal_log
    return algebra_exp([Q(beta)*x for x in formal_log(values)], no_carry_arithmetic_product)


def main():
    started = time.monotonic()
    output = Path(__file__).resolve().parent / "dyadic-results"
    output.mkdir(parents=True, exist_ok=True)
    print("Learning exponent extraction from generic local arithmetic exponentials", flush=True)
    local = parameter_polynomials(384)
    search = search_extraction(local)
    degree = 48
    correction = correction_polynomials(local[:degree+1])
    certificate = uniform_parameter_certificate(correction)
    checks = extraction_checks()
    expected_survivors = [2, 4, 8, 16, 32]
    assert [x["multiplier"] for x in search["survivors"]] == expected_survivors
    assert all(Q(x["learned_parameter_scale"]) == Q(1, x["multiplier"])
               for x in search["survivors"])
    assert checks["all_passed"] and certificate["strict_zero_free_bound_proved"]
    result = {"operator_family": "T_beta(f)=EXP_infinitary(beta*LOG_Dirichlet(f)), f(1)=1",
              "detected_law": "T_beta(u)(n^(2^k))=T_(beta/2^k)(u)(n)",
              "proved_index_classification": "E_m(f)(n)=f(n^m) preserves infinitary convolution iff m is a power of 2",
              "search": search, "exact_operator_checks": checks,
              "local_polynomial_coefficients": [[str(x) for x in p.coeffs()] for p in local],
              "correction_polynomial_coefficients": [[str(x) for x in p.coeffs()] for p in correction],
              "uniform_real_parameter_certificate": certificate,
              "analytic_domain": "Every real beta in [0,1]: H_beta=zeta^beta*R_beta initially Re(s)>1; R_beta holomorphic and nonzero on Re(s)>1/2",
              "RH_criterion": "RH iff every k>=1 pole-cancelled H_(1/2^k) has a single-valued holomorphic continuation to Re(s)>1/2",
              "RH_limitation": "A finite root order permits zeros with divisible multiplicity; no global continuation or RH proof is supplied",
              "proof": "dyadic_root_proof.txt", "historical_novelty": "unresolved; known algebra and fractional powers, specific extraction/certificate application under review",
              "counts_as_verified_new_operator": False, "elapsed_seconds": time.monotonic()-started}
    (output/"dyadic_root_search.json").write_text(json.dumps(result, indent=2)+"\n")
    print(f"Extraction fits: {search['training_fits']}; fresh survivors: {expected_survivors}; rejected: {len(search['rejected_training_fits'])}")
    print(f"Uniform beta in [0,1] correction bound: {float(Q(certificate['total_bound'])):.12g} < 1")
    print(f"Saved {output/'dyadic_root_search.json'}; elapsed {result['elapsed_seconds']:.1f}s")


if __name__ == "__main__":
    main()

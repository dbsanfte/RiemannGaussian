#!/usr/bin/env python3
"""Search zeta-root lifts using different exact arithmetic products.

This stage builds outputs rather than fitting only twelve preselected zeta
profiles. Known products and their root applications are reported honestly.
An unexplored application is a candidate, not a verified historical novelty.
"""

from __future__ import annotations

import argparse
import json
import time
from fractions import Fraction as Q
from math import comb, gcd
from pathlib import Path

from exact_arithmetic import (convolve, factorial_valuation, factorization,
                              normalized_power, sequence, unit,
                              unitary_convolution)
from root_probe import ROOT_ORDERS, local_root_coefficients


def exponent_weight(kind, left, right, prime=None, parameter=None):
    if kind == "ordinary":
        return Q(1)
    if kind == "unitary":
        return Q(int(left == 0 or right == 0))
    if kind == "binomial":
        return Q(comb(left + right, left))
    if kind == "carry":
        exponent = (factorial_valuation(left + right, prime)
                    - factorial_valuation(left, prime)
                    - factorial_valuation(right, prime))
        return Q(parameter) ** exponent
    raise ValueError(kind)


def local_product(left, right, operator):
    size = len(left)
    if len(right) != size:
        raise ValueError("Local cutoffs must agree")
    result = [Q(0)] * size
    for total in range(size):
        for i in range(total + 1):
            result[total] += left[i] * right[total - i] * exponent_weight(
                **operator, left=i, right=total - i)
    return result


def local_fold(values, order, operator):
    result = [Q(1)] + [Q(0)] * (len(values) - 1)
    for _ in range(order):
        result = local_product(result, values, operator)
    return result


def lift_multiplicative(local, cutoff):
    result = [Q(0), Q(1)]
    for n in range(2, cutoff + 1):
        value = Q(1)
        for e in factorization(n).values():
            value *= local[e]
        result.append(value)
    return result


def operator_programs():
    yield {"kind": "ordinary"}
    yield {"kind": "unitary"}
    yield {"kind": "binomial"}
    for prime in (2, 3, 5, 7):
        for parameter in ("0", "1/2", "2", "-1"):
            yield {"kind": "carry", "prime": prime, "parameter": parameter}


def coefficient_support(values):
    nonzero = [n for n in range(2, len(values)) if values[n]]
    return {
        "nonzero_count": len(nonzero),
        "first_indices": nonzero[:16],
        "minimum_prime_exponent": min((min(factorization(n).values()) for n in nonzero),
                                      default=None),
        "all_squarefull": all(all(e >= 2 for e in factorization(n).values()) for n in nonzero),
        "all_square": all(all(e % 2 == 0 for e in factorization(n).values()) for n in nonzero),
    }


def classify(operator):
    kind = operator["kind"]
    if kind == "ordinary":
        return {"operator_status": "known", "application_status": "known_power_law"}
    if kind == "unitary":
        return {"operator_status": "known", "application_status": "derived_composite_under_literature_review"}
    if kind == "binomial":
        return {"operator_status": "known", "application_status": "derived_composite_under_literature_review"}
    if operator["prime"] == 2 and operator["parameter"] == "0":
        return {"operator_status": "known_infinitary_convolution",
                "application_status": "derived_composite_under_literature_review"}
    if operator["parameter"] != "0":
        return {"operator_status": "known_weight_transport_framework",
                "application_status": "derived_composite_under_literature_review"}
    return {"operator_status": "no_carry_convolution_requires_specific_prior_art_check",
            "application_status": "derived_composite_under_literature_review"}


def unitary_analytic_check(order, cutoff=512, prime_cutoff=257):
    """Check the exact root-lift identity with independent complex balls.

    H_q=sum q**omega(n)*b_(1/q)(n)/n**s = zeta(s)*R_q(s), sigma>1.
    R_q's Euler product is holomorphic and nonzero for sigma>1/2. All
    displayed numerical errors include a proven series/product tail bound.
    """
    import flint

    flint.ctx.prec = 300
    roots = normalized_power(sequence([1] * cutoff), Q(1, order))
    lifted = [Q(0)] + [order ** len(factorization(n)) * roots[n]
                       for n in range(1, cutoff + 1)]
    primes = [n for n in range(2, prime_cutoff + 1) if factorization(n) == {n: 1}]
    records = []
    for sigma, height in ((4, "0"), (4, "17.3"), (6, "109.7")):
        s = flint.acb(str(sigma), height)
        finite_sum = flint.acb(0)
        for n in range(1, cutoff + 1):
            coefficient = flint.arb(lifted[n].numerator) / lifted[n].denominator
            finite_sum += coefficient * (-s * flint.arb(n).log()).exp()
        correction = flint.acb(1)
        for prime in primes:
            x = (-s * flint.arb(prime).log()).exp()
            y = 1 - x
            correction *= order * (y.log() * Q(order - 1, order).numerator
                                   / Q(order - 1, order).denominator).exp() - (order - 1) * y
        zeta = s.zeta()
        series_tail = flint.arb(cutoff) ** (1 - sigma) / (sigma - 1)
        euler_tail_exponent = flint.arb(prime_cutoff) ** (1 - 2 * sigma) / (2 * sigma - 1)
        product_error = correction.abs_upper() * euler_tail_exponent.expm1()
        allowed_error = series_tail + zeta.abs_upper() * product_error
        error = (finite_sum - zeta * correction).abs_upper()
        records.append({"order": order, "s": [str(sigma), height],
                        "difference_upper_ball": str(error),
                        "combined_proved_tail_bound_ball": str(allowed_error),
                        "within_proved_bound": bool(error < allowed_error)})
    return records


def exact_unitary_implementation_check():
    size = 128
    records = []
    for order in (2, 3, 4, 5):
        root = normalized_power(sequence([1] * size), Q(1, order))
        folded = unit(size)
        for _ in range(order):
            folded = unitary_convolution(folded, root)
        expected = [Q(0)] + [order ** len(factorization(n)) * root[n]
                             for n in range(1, size + 1)]
        records.append({"order": order, "cutoff": size,
                        "direct_arithmetic_fold_matches_local_interpretation": folded == expected})
    return records


def nonmultiplicative_control():
    size = 64
    f = sequence([1] * size)
    f[6] += 1
    root = normalized_power(f, Q(1, 2))
    lifted = unitary_convolution(root, root)
    quotient = convolve(lifted, normalized_power(f, -1))
    violation = next((n for n in range(2, size + 1) if quotient[n]
                      and any(e == 1 for e in factorization(n).values())), None)
    return {"input": "u+delta_6", "cutoff": size,
            "squarefull_claim_on_arbitrary_inputs_rejected": violation is not None,
            "first_counterexample_n": violation,
            "coefficient": str(quotient[violation]) if violation else None}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent / "root-results")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    records = []
    degree = 24
    # This is not a uniform convergence theorem for every family: weights
    # like the binomial kernel can cause exponential local growth. Keeping
    # this distinction stops an exact formal identity being promoted to a
    # falsely wide analytic domain.
    for order in ROOT_ORDERS:
        root = local_root_coefficients(order, degree)
        for operator in operator_programs():
            lifted = local_fold(root, order, operator)
            correction = [lifted[0]] + [lifted[e] - lifted[e - 1]
                                        for e in range(1, len(lifted))]
            training = lift_multiplicative(correction, 64)
            validation = lift_multiplicative(correction, 2048)
            records.append({
                "root_order": order, "operator": operator,
                "program": {"kind": "generalized_fold", "order": order,
                            "operator": operator,
                            "arg": {"kind": "root", "order": order,
                                    "arg": {"kind": "input", "name": "zeta_coefficients"}}},
                "first_local_coefficients": [str(x) for x in lifted[:13]],
                "first_correction_local_coefficients": [str(x) for x in correction[:13]],
                "first_degree_with_correction": next((e for e in range(1, len(correction))
                                                      if correction[e]), None),
                "training_support": coefficient_support(training),
                "validation_support": coefficient_support(validation),
                "lifted_local_values_are_all_at_most_one_through_cutoff":
                    all(x <= 1 for x in lifted),
                "first_lifted_local_value_above_one":
                    next((e for e, x in enumerate(lifted) if x > 1), None),
                "universal_support_proof": "mixed_root_proofs.txt: shared first coefficient",
                "analytic_bridge_status": (
                    "proved_nonzero_correction_Re_s_gt_half" if operator["kind"] == "unitary" else
                    "known_identity_H_equals_zeta" if operator["kind"] == "ordinary" else
                    "proved_holomorphic_correction_Re_s_gt_half_nonvanishing_unresolved"
                    if operator["kind"] == "carry" else
                    "rejected_half_plane_bridge_local_radius_is_1_over_q"),
                **classify(operator),
                "counts_as_verified_new_operator": False,
            })
        print(f"Completed root order {order}: {len(records)} mixed operator programs", flush=True)
    implementation = exact_unitary_implementation_check()
    analytic = [check for order in ROOT_ORDERS for check in unitary_analytic_check(order)]
    result = {"training_cutoff": 64, "validation_cutoff": 2048,
              "local_exponent_cutoff": degree, "programs_checked": len(records),
              "candidates": records, "unitary_implementation_checks": implementation,
              "unitary_analytic_checks": analytic,
              "nonmultiplicative_negative_control": nonmultiplicative_control(),
              "verified_new_operators": [],
              "elapsed_seconds": time.monotonic() - started}
    destination = args.output_dir / "mixed_root_search.json"
    destination.write_text(json.dumps(result, indent=2) + "\n")
    assert all(record["validation_support"]["all_squarefull"] for record in records)
    assert all(record["direct_arithmetic_fold_matches_local_interpretation"] for record in implementation)
    assert all(record["within_proved_bound"] for record in analytic)
    assert result["nonmultiplicative_negative_control"]["squarefull_claim_on_arbitrary_inputs_rejected"]
    print(f"Saved {destination}; elapsed {result['elapsed_seconds']:.1f}s", flush=True)


if __name__ == "__main__":
    main()

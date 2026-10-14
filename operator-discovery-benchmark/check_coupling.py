#!/usr/bin/env python3
"""Independent exact audit of tensor interactions, using labelled EGFs.

No production module is imported. Triangular Euler-degree LOG/EXP replace
the power-series evaluator; weighted bit partitions replace the local
Euler recurrence. Rational power coefficients use their independent
rising-factorial formula.
"""

from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import json


BASE = Path(__file__).resolve().parent


def triangular(values, kind, operation):
    e_max, k_max = len(values)-1, len(values[0])-1
    output = [[Q(0)]*(k_max+1) for _ in values]
    output[0][0] = Q(1 if operation == "EXP" else 0)
    for grade in range(1, e_max+k_max+1):
        for e in range(max(0, grade-k_max), min(e_max, grade)+1):
            k = grade-e
            total = Q(0)
            for i in range(e+1):
                for j in range(k+1):
                    if i+j == 0 or (i == e and j == k):
                        continue
                    if kind == "A" and i & (e-i):
                        continue
                    if kind == "G" and (i+j) & (e-i+k-j):
                        continue
                    if operation == "LOG":
                        total += (i+j)*output[i][j]*values[e-i][k-j]
                    else:
                        total += (i+j)*values[i][j]*output[e-i][k-j]
            output[e][k] = values[e][k]+(total/grade if operation == "EXP" else -total/grade)
    return output


def action(values, kind):
    return triangular(triangular(values, "D", "LOG"), kind, "EXP")


def independent_zeta_power(alpha, e_max, k_max):
    alpha = Q(alpha)
    local = [Q(1)]
    for e in range(1, e_max+1):
        local.append(local[-1]*(alpha+e-1)/e)
    return [[local[e]*alpha**k/factorial(k) for k in range(k_max+1)] for e in range(e_max+1)]


def independent_local(degree):
    h = [Q(1)]
    for e in range(1, degree+1):
        bit, rest = e & -e, e ^ (e & -e)
        subset, total = rest, Q(0)
        while True:
            block = bit | subset
            total += h[e-block]/block
            if subset == 0:
                break
            subset = (subset-1) & rest
        h.append(total)
    inverse = [Q(1)]
    for e in range(1, degree+1):
        inverse.append(-sum((h[i]*inverse[e-i] for i in range(1, e+1)), Q(0)))
    a = [Q(0)]
    for e in range(1, degree+1):
        a.append(sum((i*h[i]*inverse[e-i] for i in range(1, e+1)), Q(0))/e)
    t2 = [Q(1)]
    for e in range(1, degree+1):
        bit, rest = e & -e, e ^ (e & -e)
        subset, total = rest, Q(0)
        while True:
            block = bit | subset
            total += a[block]*t2[e-block]
            if subset == 0:
                break
            subset = (subset-1) & rest
        t2.append(total)
    g = [sum((h[i]*inverse[e-i] for i in range(0, e+1, 2)), Q(0)) for e in range(degree+1)]
    d = []
    for e in range(degree+1):
        value = sum((t2[i]*g[e-i] for i in range(e+1) if i & (e-i) == 0), Q(0))
        d.append(value-(t2[e] if e % 2 == 0 else 0))
    return {"H": h, "LOG_H": a, "T_H": t2, "H_even_over_H": g, "commutator": d}


def main():
    source = json.loads((BASE/"coupling-results/coupling_search.json").read_text())
    e_max = source["declared_tensor_cutoffs"]["one_prime_exponent"]
    k_max = source["declared_tensor_cutoffs"]["other_distinct_prime_count"]
    checks = {"all_tensor_input_and_composition_coefficients_agree": True,
              "factorial_family_all_fresh_parameters_and_arities_pass": True,
              "arity_one_factorial_extrapolation_rejected": True}
    compared = 0
    for alpha, profile in source["commutator_tensor_profiles"].items():
        f = independent_zeta_power(alpha, e_max, k_max)
        input_table = source["input_tensor_profiles"][alpha]
        ts, st = action(action(f, "G"), "A"), action(action(f, "A"), "G")
        for e in range(e_max+1):
            for k in range(k_max+1):
                checks["all_tensor_input_and_composition_coefficients_agree"] &= f[e][k]*factorial(k) == Q(input_table[e][k])
                checks["all_tensor_input_and_composition_coefficients_agree"] &= (ts[e][k]-st[e][k])*factorial(k) == Q(profile[e][k])
                compared += 1
        for k in range(2, k_max+1):
            expected = Q((-1)**(k+1)*factorial(k), 2)*Q(alpha)**(k+2)
            checks["factorial_family_all_fresh_parameters_and_arities_pass"] &= Q(profile[2][k]) == expected
        checks["arity_one_factorial_extrapolation_rejected"] &= Q(profile[2][1]) == Q(alpha)**3
    degree = len(source["first_other_prime_local_profile"]["H"])-1
    local = independent_local(degree)
    checks["all_local_bit_partition_inverse_and_log_coefficients_agree"] = all(
        [str(x) for x in values] == source["first_other_prime_local_profile"][key]
        for key, values in local.items())
    cert = source["local_norm_certificate"]
    radius, bound_degree = Q(cert["radius"]), cert["degree"]
    r_bound = sum((abs(local["H"][e]-local["H"][e-1])*radius**e for e in range(1, bound_degree+1)), Q(0))
    r_bound += radius**(bound_degree+1)/(1-radius)
    k_bound = 1/((1-radius)*(1-r_bound))
    checks["local_zero_free_and_Banach_norm_certificate_recomputed"] = (
        r_bound == Q(cert["R_total_norm_bound"]) and r_bound < 1
        and k_bound*(k_bound+1) == Q(cert["first_other_prime_commutator_weighted_norm_bound"]))
    checks["leading_commutator_coefficients_are_0_0_1"] = local["commutator"][:3] == [0, 0, 1]
    module_records = []
    for item in source["generic_first_other_prime_module_checks"]["records"]:
        f0, f1 = [[Q(x) for x in item[key]] for key in ("f0", "f1")]
        values = [[a, b] for a, b in zip(f0, f1)]
        t, s = action(values, "A"), action(values, "G")
        # Independently derive the local logarithm and ratio by triangular
        # ordinary series, then its A-exponential.
        one_row = [[x] for x in f0]
        local_t = [x[0] for x in action(one_row, "A")]
        ratio = []
        for e in range(len(f0)):
            ratio.append(f1[e]-sum((f0[i]*ratio[e-i] for i in range(1, e+1)), Q(0)))
        predicted_t = [sum((local_t[i]*ratio[e-i] for i in range(e+1) if not i & (e-i)), Q(0)) for e in range(len(f0))]
        predicted_s = [sum((local_t[i]*ratio[e-i] for i in range(e+1) if not i & (e-i+1)), Q(0)) for e in range(len(f0))]
        passed = all(t[e][0] == s[e][0] == local_t[e] and t[e][1] == predicted_t[e] and s[e][1] == predicted_s[e]
                     for e in range(len(f0)))
        module_records.append({"degree": item["degree"], "independently_recomputed_module_laws_passed": passed})
    checks["generic_first_other_prime_module_laws_pass"] = all(x["independently_recomputed_module_laws_passed"] for x in module_records)
    kernel = source["suspension_kernel_grammar"]
    decisions = []
    for model in kernel["training_fits"]:
        a, b = model["first_offset"], model["second_offset"]
        witness = next(((i, j) for i in range(64) for j in range(64)
                        if ((i+a)&(j+b) == 0) != (i & (j+1) == 0)), None)
        decisions.append((witness is None) == model["held_out_passed"]
                         and (list(witness) if witness else None) == model["first_counterexample"])
    checks["suspension_kernel_search_decisions_recomputed"] = all(decisions)
    # The k>=2 universal formula is also verified symbolically as an EGF:
    # D_2(Y)=alpha^3*Y-alpha^4*Y^2/[2*(1+alpha*Y)].
    # Its geometric coefficients are precisely the factorial family after
    # multiplying by k!, and its k=0,1 terms are checked separately.
    checks["symbolic_geometric_EGF_coefficients_match_all_profiles"] = all(
        Q(table[2][0]) == 0 and Q(table[2][1]) == Q(alpha)**3
        and all(Q(table[2][k])/factorial(k) == -Q(alpha)**4*Q(-Q(alpha))**(k-2)/2 for k in range(2, k_max+1))
        for alpha, table in source["commutator_tensor_profiles"].items())
    result = {"checks": checks, "tensor_coefficients_independently_compared": compared,
              "local_degree_independently_compared": degree, "generic_module_records": module_records,
              "all_passed": all(checks.values()), "proof": "coupling_proof.txt",
              "historical_novelty_is_not_certified": True}
    (BASE/"coupling-results/coupling_verification.json").write_text(json.dumps(result, indent=2)+"\n")
    print(f"Independent coupling audit: {sum(checks.values())}/{len(checks)} gates; "
          f"tensor coefficients={compared}, exact local degree={degree}")
    assert result["all_passed"]


if __name__ == "__main__":
    main()

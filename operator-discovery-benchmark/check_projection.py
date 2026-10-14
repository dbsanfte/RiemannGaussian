#!/usr/bin/env python3
"""Independent factorial, inverse, triangular and symbolic verification.

Imports neither the detector nor its arithmetic implementation. The mask
comes from integer multinomial parity, and arithmetic EXP/LOG use triangular
Euler-derivative recurrences rather than production power series.
"""

from __future__ import annotations

from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import json
import random

import sympy as sp


def factor(n):
    output = {}
    d = 2
    while d*d <= n:
        while n % d == 0:
            output[d] = output.get(d, 0)+1
            n //= d
        d += 1
    if n > 1:
        output[n] = output.get(n, 0)+1
    return output


def multinomial(factors):
    denominator = 1
    for exponent in factors.values():
        denominator *= factorial(exponent)
    return factorial(sum(factors.values()))//denominator


def kernel(left, right, kind):
    if kind == "D":
        return 1
    if kind == "G":
        return comb(sum(left.values())+sum(right.values()), sum(left.values())) % 2
    if kind == "A":
        value = 1
        for p in left.keys() | right.keys():
            value *= comb(left.get(p, 0)+right.get(p, 0), left.get(p, 0)) % 2
        return value
    raise ValueError(kind)


def divisors(n):
    result = []
    for d in range(1, int(n**0.5)+1):
        if n % d == 0:
            result.append(d)
            if n//d != d:
                result.append(n//d)
    return sorted(result)


def triangular(values, kind, operation):
    cutoff = len(values)-1
    factors = [{}]+[factor(n) for n in range(1, cutoff+1)]
    degree = [sum(x.values()) for x in factors]
    output = [Q(0)]*(cutoff+1)
    output[1] = Q(1) if operation == "exp" else Q(0)
    assert values[1] == (0 if operation == "exp" else 1)
    for n in range(2, cutoff+1):
        correction = Q(0)
        for d in divisors(n)[1:-1]:
            weight = kernel(factors[d], factors[n//d], kind)
            if operation == "exp":
                correction += weight*degree[d]*values[d]*output[n//d]
            else:
                correction += weight*degree[d]*output[d]*values[n//d]
        output[n] = values[n]+correction/degree[n] if operation == "exp" else values[n]-correction/degree[n]
    return output


def convolution(left, right, kind="D"):
    cutoff = len(left)-1
    factors = [{}]+[factor(n) for n in range(1, cutoff+1)]
    output = [Q(0)]*(cutoff+1)
    for n in range(1, cutoff+1):
        output[n] = sum((kernel(factors[d], factors[n//d], kind)*left[d]*right[n//d]
                         for d in divisors(n)), Q(0))
    return output


def diagonal(values):
    return [Q(0)]+[x*(multinomial(factor(n)) % 2) for n, x in enumerate(values[1:], 1)]


def transfer(values, kind):
    return triangular(triangular(values, "D", "log"), kind, "exp")


def projection(values):
    return triangular(diagonal(triangular(values, "D", "log")), "D", "exp")


def verify_generic_laws(source):
    rng = random.Random(2026100618)
    witnesses = []
    for record in source["formal_checks"]["records"]:
        cutoff = record["cutoff"]
        a, b = [[Q(0), Q(1)]+[Q(rng.randint(-3, 3), rng.randint(1, 5)) for _ in range(cutoff-1)]
                for _ in range(2)]
        pa = projection(a)
        h = triangular(a, "D", "log")
        allowed = triangular(diagonal(h), "D", "exp")
        discarded = triangular([x-y for x, y in zip(h, diagonal(h))], "D", "exp")
        expected_unit = [Q(0), Q(1)]+[Q(0)]*(cutoff-1)
        laws = {
            "linear_mask_intertwines_products": diagonal(convolution(a, b, "A")) == convolution(diagonal(a), diagonal(b), "G"),
            "linear_mask_idempotence": diagonal(diagonal(a)) == diagonal(a),
            "logarithmic_projection_idempotence": projection(pa) == pa,
            "ordinary_unit_group_projection": projection(convolution(a, b)) == convolution(pa, projection(b)),
            "universal_transfer_factorization": diagonal(transfer(a, "A")) == transfer(pa, "G"),
            "unique_ordinary_product_decomposition": convolution(allowed, discarded) == a,
            "discarded_component_projects_to_unit": projection(discarded) == expected_unit,
        }
        witnesses.append({"cutoff": cutoff, "laws": laws, "production_records_agree": laws == record["laws"]})
    return witnesses


def symbolically_verify_commutator():
    indices = ((0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (2, 1))
    a, b, c, d, e = sp.symbols("a b c d e")
    values = dict(zip(indices, (1, a, b, c, d, e)))
    def product(left, right, kind):
        output = {i: sp.S.Zero for i in indices}
        for i, x in left.items():
            for j, y in right.items():
                n = (i[0]+j[0], i[1]+j[1])
                if n not in output:
                    continue
                weight = 1 if kind == "D" else (int(not ((i[0]&j[0]) or (i[1]&j[1]))) if kind == "A"
                                                else int(not ((sum(i)) & (sum(j)))))
                output[n] += weight*x*y
        return {n: sp.expand(x) for n, x in output.items()}
    def power_series(f, kind, operation):
        one = {i: sp.Integer(i == (0, 0)) for i in indices}
        h = dict(f)
        if operation == "log":
            h[(0, 0)] -= 1
        term = one
        out = dict(one) if operation == "exp" else {i: sp.S.Zero for i in indices}
        for k in range(1, 4):
            term = product(term, h, kind)
            coefficient = sp.Rational(1, factorial(k)) if operation == "exp" else sp.Rational((-1)**(k+1), k)
            out = {n: sp.expand(out[n]+coefficient*term[n]) for n in indices}
        return out
    def t(f, kind):
        return power_series(power_series(f, "D", "log"), kind, "exp")
    ts, st = t(t(values, "G"), "A"), t(t(values, "A"), "G")
    difference = {n: sp.expand(ts[n]-st[n]) for n in indices}
    passed = difference[(2, 1)] == a*a*b and all(x == 0 for n, x in difference.items() if n != (2, 1))
    return {"T_S_coefficient_p_squared_q": str(ts[(2, 1)]), "S_T_coefficient_p_squared_q": str(st[(2, 1)]),
            "symbolic_difference": str(difference[(2, 1)]), "all_other_divisor_coefficients_cancel": passed,
            "all_passed": passed}


def feature(n, name, factors):
    exponents = list(factors[n].values())
    degree = sum(exponents)
    if name == "1": return 1
    if name == "Omega": return degree
    if name == "omega": return len(exponents)
    prefix, base_text = name.rsplit("_", 1)
    base = int(base_text)
    def ds(value):
        digits = 0
        while value:
            value, remainder = divmod(value, base)
            digits += remainder
        return digits
    def vf(value):
        value = factorial(value)
        exponent = 0
        while value % base == 0:
            value //= base
            exponent += 1
        return exponent
    if prefix == "digits_total": return ds(degree)
    if prefix == "sum_digits_exponents": return sum(ds(x) for x in exponents)
    if prefix == "factorial_total": return vf(degree)
    if prefix == "sum_factorial_exponents": return sum(vf(x) for x in exponents)
    raise ValueError(name)


def main():
    destination = Path(__file__).resolve().parent/"projection-results"
    source = json.loads((destination/"projection_search.json").read_text())
    search = source["search"]
    cutoff = search["validation_cutoff"]
    factors = [{}]+[factor(n) for n in range(1, cutoff+1)]
    counts = [0]+[multinomial(factors[n]) for n in range(1, cutoff+1)]
    expected_mask = [value % 2 for value in counts]
    inverse = [0, 1]+[0]*(cutoff-1)
    for n in range(2, cutoff+1):
        inverse[n] = -sum(inverse[n//p] for p in factors[n])
    inverse_formula = all(inverse[n] == (-1)**sum(factors[n].values())*counts[n] for n in range(1, cutoff+1))
    layers = [0, 1]+[0]*(cutoff-1)
    exponent = 1
    while 2**exponent <= cutoff:
        added = list(layers)
        for p in range(2, cutoff+1):
            if factors[p] != {p: 1} or p**exponent > cutoff:
                continue
            power = p**exponent
            for n in range(1, cutoff//power+1):
                added[n*power] += layers[n]
        layers = added
        exponent *= 2
    basis_count, basis_passed = 0, True
    for i in range(1, cutoff+1):
        for j in range(1, cutoff//i+1):
            basis_count += 1
            basis_passed &= expected_mask[i*j]*kernel(factors[i], factors[j], "A") == expected_mask[i]*expected_mask[j]*kernel(factors[i], factors[j], "G")
    fits_agree = True
    for model in search["training_fits"]:
        a, b = model["coefficients"]
        values = [0]
        for n in range(1, cutoff+1):
            expression = a*feature(n, model["features"][0], factors)+b*feature(n, model["features"][1], factors)+model["offset"]
            values.append(int(expression == 0 if model["relation"] == "eq" else expression <= 0))
        failure = next((n for n in range(1, cutoff+1) if (n == 1 or len(factors[n]) == 1) and values[n] != 1), None)
        witness = {"kind": "prime_power_normalization", "n": failure} if failure is not None else None
        if witness is None:
            for i in range(1, cutoff+1):
                for j in range(1, cutoff//i+1):
                    left = values[i*j]*kernel(factors[i], factors[j], "A")
                    right = values[i]*values[j]*kernel(factors[i], factors[j], "G")
                    if left != right:
                        witness = {"kind": "basis_intertwining", "indices": [i, j], "output_n": i*j,
                                   "left": left, "right": right}
                        break
                if witness is not None: break
        fits_agree &= witness == model["first_counterexample"] and (witness is None) == model["held_out_passed"]
        if witness is None:
            fits_agree &= values == expected_mask
    hierarchy = []
    combined = [0]+[1]*cutoff
    for base in source["prime_projection_hierarchy"]["prime_bases"]:
        combined = [0]+[combined[n]*int(counts[n] % base != 0) for n in range(1, cutoff+1)]
        extra = [n for n in range(2, cutoff+1) if combined[n] and len(factors[n]) > 1]
        hierarchy.append({"largest_tested_prime_base": base, "extra_non_prime_power_indices": len(extra),
                          "first_extra_index": extra[0] if extra else None})
    generic = verify_generic_laws(source)
    symbolic = symbolically_verify_commutator()
    checks = {
        "learned_mask_equals_integer_multinomial_parity": expected_mask == search["learned_mask_values"],
        "prime_indicator_inverse_formula_agrees": inverse_formula,
        "inverse_parity_equals_learned_mask": [value % 2 for value in inverse] == expected_mask,
        "independent_digit_layer_product_coefficients_agree": layers == expected_mask,
        "all_basis_identities_recomputed_using_binomial_parity": bool(basis_passed),
        "basis_pair_count_agrees": basis_count == search["validation_basis_pairs"],
        "all_mask_grammar_validation_decisions_and_witnesses_agree": bool(fits_agree),
        "independent_triangular_generic_projection_laws_pass": all(all(x["laws"].values()) and x["production_records_agree"] for x in generic),
        "prime_hierarchy_counts_and_first_counterexamples_agree": hierarchy == source["prime_projection_hierarchy"]["records"],
        "symbolic_cubic_commutator_identity_proved": symbolic["all_passed"],
        "all_measured_cubic_commutator_coefficients_agree": all(Q(x["commutator_coefficient"]) == Q(x["features"][0])**2*Q(x["features"][1]) for x in source["commutator_search"]["records"]),
    }
    result = {"checks": checks, "all_passed": all(checks.values()), "cutoff": cutoff,
              "basis_pairs_checked": basis_count, "generic_law_witnesses": generic,
              "symbolic_commutator": symbolic, "independent_prime_hierarchy": hierarchy,
              "proof": "projection_proof.txt", "historical_novelty_is_not_certified": True}
    (destination/"projection_verification.json").write_text(json.dumps(result, indent=2)+"\n")
    print(f"Independent projection, inverse-parity, digit-product and symbolic verification: {result['all_passed']}")
    assert result["all_passed"]


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Test a cross-prime carry product and its nonlinear zeta-root limit.

The new grammar applies a recovered digital defect to TOTAL prime degree
Omega(n), rather than to each prime exponent separately. Its algebraic
laws have proofs; historical originality is a separate, unresolved question.
"""

from __future__ import annotations

from functools import lru_cache
from fractions import Fraction as Q
from itertools import combinations, product
import json
from pathlib import Path
import random
import time

from exact_arithmetic import (convolve, factorization, factorial_valuation,
                              formal_log, normalized_power, sequence, unit)
from root_transfer_probe import algebra_exp, algebra_log
from transfer_analytic_probe import partition_coefficients


@lru_cache(maxsize=32)
def degrees(size):
    return (0,) + tuple(sum(factorization(n).values()) for n in range(1, size + 1))


def global_product(left, right):
    if len(left) != len(right):
        raise ValueError("Arithmetic cutoffs must agree")
    size = len(left) - 1
    omega = degrees(size)
    result = [Q(0)] * (size + 1)
    for i in range(1, size + 1):
        if not left[i]:
            continue
        for j in range(1, size // i + 1):
            if right[j] and not omega[i] & omega[j]:
                result[i*j] += left[i] * right[j]
    return result


def global_transfer(values):
    return algebra_exp(formal_log(values), global_product)


def inverse_transfer(values):
    return algebra_exp(algebra_log(values, global_product), convolve)


def bit_disjoint_mask(n):
    used = 0
    for exponent in factorization(n).values():
        if used & exponent:
            return 0
        used |= exponent
    return 1


def independent_coefficients(size):
    local = partition_coefficients(size.bit_length())
    result = [Q(0), Q(1)]
    for n in range(2, size + 1):
        value = Q(bit_disjoint_mask(n))
        for exponent in factorization(n).values():
            value *= local[exponent]
        result.append(value)
    return result


def exact_laws():
    rng = random.Random(2026100611)
    records = []
    for size in (32, 65, 128):
        a, b = [sequence([1] + [Q(rng.randint(-3, 3), rng.randint(1, 5))
                               for _ in range(size-1)]) for _ in range(2)]
        laws = {
            "product_transfer": global_transfer(convolve(a, b)) == global_product(global_transfer(a), global_transfer(b)),
            "inverse_transfer": inverse_transfer(global_transfer(a)) == a,
            "forward_transfer": global_transfer(inverse_transfer(a)) == a,
            "prefix_consistency": global_transfer(a)[:size//2+1] == global_transfer(a[:size//2+1]),
        }
        records.append({"cutoff": size, "laws": laws})
    impulse2 = unit(6)
    impulse2[1], impulse2[2] = Q(0), Q(1)
    impulse3 = unit(6)
    impulse3[1], impulse3[3] = Q(0), Q(1)
    return {"records": records,
            "coprime_impulses_annihilate": global_product(impulse2, impulse3)[6] == 0,
            "ordinary_coprime_product_survives": convolve(impulse2, impulse3)[6] == 1,
            "all_passed": all(all(x["laws"].values()) for x in records)}


def mask_search(values, reference, training_cutoff=64):
    bases = (2, 3, 5, 7)
    names = ["1", "Omega", "omega"]
    for base in bases:
        names += [f"digits_total_{base}", f"sum_digits_exponents_{base}",
                  f"factorial_total_{base}", f"sum_factorial_exponents_{base}"]

    def digit_sum(n, base):
        total = 0
        while n:
            n, r = divmod(n, base)
            total += r
        return total

    columns = [[] for _ in names]
    for n in range(1, len(values)):
        exponents = list(factorization(n).values())
        total = sum(exponents)
        features = [1, total, len(exponents)]
        for base in bases:
            features += [digit_sum(total, base), sum(digit_sum(e, base) for e in exponents),
                         factorial_valuation(total, base), sum(factorial_valuation(e, base) for e in exponents)]
        for column, feature in zip(columns, features):
            column.append(feature)
    target = [int(values[n] != 0) for n in range(1, len(values))]
    candidates = []
    checked = 0
    for i, j in combinations(range(len(names)), 2):
        for a, b in product((-2, -1, 1, 2), repeat=2):
            # Sign and common-scale duplicates are suppressed explicitly.
            if a < 0 or (abs(a) == abs(b) == 2):
                continue
            for offset in range(-2, 3):
                for relation in ("eq", "le"):
                    checked += 1
                    def matches(k):
                        expression = a * columns[i][k] + b * columns[j][k] + offset
                        mask = int(expression == 0 if relation == "eq" else expression <= 0)
                        return mask == target[k]
                    if not all(matches(k) for k in range(training_cutoff)):
                        continue
                    failure = next((k+1 for k in range(training_cutoff, len(target)) if not matches(k)), None)
                    candidates.append({"features": [names[i], names[j]], "coefficients": [a, b],
                                       "offset": offset, "relation_to_zero": relation,
                                       "held_out_passed": failure is None, "first_counterexample_n": failure})
    ratio_law = all(values[n] == target[n-1] * reference[n] for n in range(1, len(values)))
    return {"programs_checked": checked, "training_cutoff": training_cutoff,
            "validation_cutoff": len(values)-1, "feature_names": names,
            "training_matches": candidates, "held_out_survivors": sum(x["held_out_passed"] for x in candidates),
            "mask_times_local_transfer_law_passed": ratio_law,
            "interpreted_law": "sum_p binary_digit_sum(v_p(n)) = binary_digit_sum(Omega(n))",
            "proof": "global_carry_proof.txt section 3"}


def main():
    started = time.monotonic()
    destination = Path(__file__).resolve().parent / "global-results"
    destination.mkdir(exist_ok=True)
    checks = exact_laws()
    size = 4096
    print(f"Computing the global root-limit operator through n={size}", flush=True)
    actual = global_transfer(sequence([1] * size))
    expected = independent_coefficients(size)
    assert actual == expected
    local = partition_coefficients(size.bit_length())
    reference = [Q(0), Q(1)]
    for n in range(2, size + 1):
        value = Q(1)
        for exponent in factorization(n).values():
            value *= local[exponent]
        reference.append(value)
    search = mask_search(actual, reference)
    limit_samples = []
    for order in (2, 3, 4, 5, 6, 7, 16, 64):
        root = normalized_power(sequence([1] * 128), Q(1, order))
        folded = unit(128)
        for _ in range(order):
            folded = global_product(folded, root)
        limit_samples.append({"root_order": order, "coefficient_6": str(folded[6]),
                              "coefficient_6_equals_inverse_order": folded[6] == Q(1, order),
                              "coefficient_6_limit": "0",
                              "maximum_limit_coefficient_error_through_128": str(max(abs(x-y) for x,y in zip(folded, actual[:129])))})
    result = {"operator": "EXP_global_no_carry(LOG_Dirichlet(f))", "domain": "rational arithmetic functions f(1)=1",
              "kernel": "1[Omega(i) & Omega(j) == 0] for ij=n",
              "new_grammar_production": "digital factorial defect of total degree, coupling different primes",
              "source": "q->infinity limit of a root followed by q-fold global-carry convolution",
              "formal_checks": checks, "independent_bit_partition_and_mask_coefficients_agree": actual == expected,
              "mask_search": search, "root_limit_samples": limit_samples,
              "first_arithmetic_coefficients": [str(x) for x in actual[1:65]],
              "multiplicativity_negative_control": {"T_u_at_2": str(actual[2]), "T_u_at_3": str(actual[3]),
                                                     "T_u_at_6": str(actual[6]), "multiplicativity_rejected": actual[6] != actual[2]*actual[3]},
              "zeta_bridge": "F(s)=A(s)*log(zeta(s))+B(s), A and B holomorphic on Re(s)>1/2",
              "RH_criterion": "F(s)+A(s)*log(s-1) extends holomorphically and single-valuedly to Re(s)>1/2 iff RH",
              "proof": "global_carry_proof.txt", "historical_novelty": "unresolved; general convolution and formal unit-group frameworks are classical",
              "counts_as_verified_new_operator": False, "elapsed_seconds": time.monotonic()-started}
    (destination / "global_carry_probe.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"Independent coefficients agree; mask fits={len(search['training_matches'])}, survivors={search['held_out_survivors']}; elapsed={result['elapsed_seconds']:.1f}s")
    assert checks["all_passed"] and search["mask_times_local_transfer_law_passed"]
    assert result["multiplicativity_negative_control"]["multiplicativity_rejected"]
    assert all(x["coefficient_6_equals_inverse_order"] for x in limit_samples)


if __name__ == "__main__":
    main()

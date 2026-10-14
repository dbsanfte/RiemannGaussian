#!/usr/bin/env python3
"""Learn a diagonal arithmetic intertwiner and inspect transform interactions.

Acceptance uses a product identity on basis impulses, not target zeta mask
labels. Every prime-power impulse must be preserved. The formal proofs and
independent verifier are separate from this finite search.
"""

from __future__ import annotations

from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import json
import random
import time

from exact_arithmetic import (convolve, digit_sum, factorization, factorial_valuation,
                              formal_exp, formal_log, sequence, unit)
from global_carry_probe import global_product, global_transfer
from root_transfer_probe import no_carry_arithmetic_product, transfer


def mask(n, base=2):
    exponents = tuple(factorization(n).values())
    return int(sum(digit_sum(e, base) for e in exponents) == digit_sum(sum(exponents), base))


def apply_mask(values, base=2):
    return [Q(0)] + [value*mask(n, base) for n, value in enumerate(values[1:], 1)]


def logarithmic_projection(values, base=2):
    return formal_exp(apply_mask(formal_log(values), base))


def feature_table(cutoff):
    names = ["1", "Omega", "omega"]
    bases = (2, 3, 5, 7)
    for base in bases:
        names += [f"digits_total_{base}", f"sum_digits_exponents_{base}",
                  f"factorial_total_{base}", f"sum_factorial_exponents_{base}"]
    columns = [[] for _ in names]
    factors = [{}] + [factorization(n) for n in range(1, cutoff+1)]
    for n in range(1, cutoff+1):
        exponents = list(factors[n].values())
        degree = sum(exponents)
        features = [1, degree, len(exponents)]
        for base in bases:
            features += [digit_sum(degree, base), sum(digit_sum(e, base) for e in exponents),
                         factorial_valuation(degree, base), sum(factorial_valuation(e, base) for e in exponents)]
        for column, value in zip(columns, features):
            column.append(value)
    return names, columns, factors


def basis_pairs(factors, cutoff):
    records = []
    for i in range(1, cutoff+1):
        for j in range(1, cutoff//i+1):
            a, b = factors[i], factors[j]
            primewise = int(all(not (a.get(p, 0) & b.get(p, 0)) for p in a.keys() | b.keys()))
            total = int(not (sum(a.values()) & sum(b.values())))
            records.append((i, j, primewise, total))
    return records


def model_mask(model, names, columns, cutoff):
    i, j = (names.index(x) for x in model["features"])
    a, b = model["coefficients"]
    values = [0]
    for k in range(cutoff):
        expression = a*columns[i][k]+b*columns[j][k]+model["offset"]
        values.append(int(expression == 0 if model["relation"] == "eq" else expression <= 0))
    return values


def projection_search(training_cutoff=32, validation_cutoff=4096):
    names, columns, factors = feature_table(validation_cutoff)
    training_pairs = basis_pairs(factors, training_cutoff)
    validation_pairs = basis_pairs(factors, validation_cutoff)
    signatures = {}
    fits, checked = [], 0
    for i, j in combinations(range(len(names)), 2):
        for a, b in product((-2, -1, 1, 2), repeat=2):
            if a < 0 or (abs(a) == abs(b) == 2):
                continue
            for offset in range(-2, 3):
                for relation in ("eq", "le"):
                    checked += 1
                    model = {"features": [names[i], names[j]], "coefficients": [a, b],
                             "offset": offset, "relation": relation}
                    values = model_mask(model, names, columns, training_cutoff)
                    signature = tuple(values)
                    if signature not in signatures:
                        normalized = values[1] == 1 and all(values[n] == 1 for n in range(2, training_cutoff+1)
                                                           if len(factors[n]) == 1)
                        hom = normalized and all(values[i*j]*wa == values[i]*values[j]*wg
                                                 for i, j, wa, wg in training_pairs)
                        signatures[signature] = hom
                    if not signatures[signature]:
                        continue
                    full = model_mask(model, names, columns, validation_cutoff)
                    failure = next((n for n in range(1, validation_cutoff+1)
                                    if (n == 1 or len(factors[n]) == 1) and full[n] != 1), None)
                    witness = None
                    if failure is not None:
                        witness = {"kind": "prime_power_normalization", "n": failure}
                    else:
                        for ii, jj, wa, wg in validation_pairs:
                            left, right = full[ii*jj]*wa, full[ii]*full[jj]*wg
                            if left != right:
                                witness = {"kind": "basis_intertwining", "indices": [ii, jj],
                                           "output_n": ii*jj, "left": left, "right": right}
                                break
                    fits.append({**model, "training_passed": True, "held_out_passed": witness is None,
                                 "first_counterexample": witness})
    survivors = [x for x in fits if x["held_out_passed"]]
    assert survivors
    learned = model_mask(survivors[0], names, columns, validation_cutoff)
    assert learned == [0]+[mask(n) for n in range(1, validation_cutoff+1)]
    return {"programs_checked": checked, "unique_training_signatures": len(signatures),
            "training_cutoff": training_cutoff, "validation_cutoff": validation_cutoff,
            "training_basis_pairs": len(training_pairs), "validation_basis_pairs": len(validation_pairs),
            "feature_names": names, "acceptance_equation": "m(ij)*W_A(i,j)=m(i)*m(j)*W_G(i,j)",
            "normalization": "m(1)=m(p^e)=1 at every tested prime power",
            "no_target_mask_labels_supplied": True, "training_fits": fits, "survivors": survivors,
            "rejected_training_fits": [x for x in fits if not x["held_out_passed"]],
            "learned_mask_values": learned}


def projection_checks():
    rng = random.Random(2026100618)
    records = []
    for cutoff in (32, 65, 128):
        a, b = [sequence([1]+[Q(rng.randint(-3, 3), rng.randint(1, 5)) for _ in range(cutoff-1)])
                for _ in range(2)]
        pa = logarithmic_projection(a)
        h = formal_log(a)
        allowed = formal_exp(apply_mask(h))
        discarded = formal_exp([x-y for x, y in zip(h, apply_mask(h))])
        laws = {
            "linear_mask_intertwines_products": apply_mask(no_carry_arithmetic_product(a, b))
                                                == global_product(apply_mask(a), apply_mask(b)),
            "linear_mask_idempotence": apply_mask(apply_mask(a)) == apply_mask(a),
            "logarithmic_projection_idempotence": logarithmic_projection(pa) == pa,
            "ordinary_unit_group_projection": logarithmic_projection(convolve(a, b))
                                              == convolve(pa, logarithmic_projection(b)),
            "universal_transfer_factorization": apply_mask(transfer(a)) == global_transfer(pa),
            "unique_ordinary_product_decomposition": convolve(allowed, discarded) == a,
            "discarded_component_projects_to_unit": logarithmic_projection(discarded) == unit(cutoff),
        }
        records.append({"cutoff": cutoff, "laws": laws})
    allowed_source, forbidden_source = [[Q(0)]*65 for _ in range(2)]
    allowed_source[12], forbidden_source[6] = Q(1), Q(1)
    allowed, forbidden = formal_exp(allowed_source), formal_exp(forbidden_source)
    controls = {
        "nonmultiplicative_allowed_input_is_fixed": logarithmic_projection(allowed) == allowed,
        "allowed_input_is_not_multiplicative": allowed[12] != allowed[4]*allowed[3],
        "forbidden_input_is_removed": logarithmic_projection(forbidden) == unit(64),
        "unqualified_S_equals_M_T_rejected": global_transfer(forbidden) != apply_mask(transfer(forbidden)),
        "mask_is_not_G_endomorphism_rejected": mask(12) != mask(2)*mask(6),
    }
    return {"records": records, "scope_and_kernel_controls": controls,
            "all_passed": all(all(x["laws"].values()) for x in records) and all(controls.values())}


def prime_hierarchy_checks(cutoff=4096):
    primes = (2, 3, 5, 7, 11)
    masks = {base: [0]+[mask(n, base) for n in range(1, cutoff+1)] for base in primes}
    cumulative = [0]+[1]*cutoff
    records = []
    for base in primes:
        cumulative = [a*b for a, b in zip(cumulative, masks[base])]
        extra = [n for n in range(2, cutoff+1) if cumulative[n] and len(factorization(n)) > 1]
        records.append({"largest_tested_prime_base": base, "extra_non_prime_power_indices": len(extra),
                        "first_extra_index": extra[0] if extra else None})
    expected = [0]+[int(n == 1 or len(factorization(n)) == 1) for n in range(1, cutoff+1)]
    assert cumulative == expected
    source = [Q(0)]*(cutoff+1)
    source[3072] = Q(1)
    f = formal_exp(source)
    small_source = list(source)
    for base in primes[:-1]:
        small_source = apply_mask(small_source, base)
    after_small = formal_exp(small_source)
    after_11 = logarithmic_projection(after_small, 11)
    return {"prime_bases": list(primes), "cutoff": cutoff, "records": records,
            "finite_hierarchy_equals_prime_power_mask_through_cutoff": cumulative == expected,
            "finite_bases_2_3_5_7_false_global_completion_control": {
                "logarithmic_input_impulse_n": 3072, "factorization": "2^10*3",
                "multinomial_value": "11", "small_base_projections_leave_input": after_small == f,
                "prime_base_11_removes_input": after_11 == unit(cutoff),
                "rejected_finite_hierarchy_claim": after_small != after_11},
            "universal_limit": "All prime-base logarithmic projections converge coefficientwise to f -> product_p f(p^v_p(n))"}


def commutator_search():
    rng = random.Random(2026100619)
    data = []
    pairs = [(2, 3)]*8+[(2, 5), (3, 2), (3, 5), (5, 2), (5, 3), (7, 2), (7, 3), (7, 5)]
    for k, (p, q) in enumerate(pairs):
        cutoff = 256
        f = sequence([1]*cutoff) if k == 0 else sequence(
            [1]+[Q(rng.randint(-3, 3), rng.randint(1, 5)) for _ in range(cutoff-1)])
        ts, st = transfer(global_transfer(f)), global_transfer(transfer(f))
        features = [f[p], f[q], f[p*p], f[p*q], f[p*p*q], f[q*q]]
        target = ts[p*p*q]-st[p*p*q]
        vanishing = all(ts[n] == st[n] for n in range(1, cutoff+1)
                        if n == 1 or len(factorization(n)) == 1 or all(e == 1 for e in factorization(n).values()))
        data.append({"p": p, "q": q, "features": [str(x) for x in features],
                     "commutator_coefficient": str(target), "vanishes_on_squarefree_and_prime_power_indices": vanishing})
    monomials = [()] + [term for degree in range(1, 4)
                         for term in combinations_with_replacement(range(6), degree)]
    fits = []
    for term in monomials:
        def prediction(record):
            value = Q(1)
            for feature in term:
                value *= Q(record["features"][feature])
            return value
        if not all(prediction(record) == Q(record["commutator_coefficient"]) for record in data[:8]):
            continue
        failure = next((k for k, record in enumerate(data[8:], 8)
                        if prediction(record) != Q(record["commutator_coefficient"])), None)
        fits.append({"feature_indices": list(term), "coefficient": "1", "held_out_passed": failure is None,
                     "first_counterexample_record": failure})
    assert [x["feature_indices"] for x in fits if x["held_out_passed"]] == [[0, 0, 1]]
    u = sequence([1]*512)
    ts, st = transfer(global_transfer(u)), global_transfer(transfer(u))
    differences = [{"n": n, "T_S_u": str(ts[n]), "S_T_u": str(st[n]), "difference": str(ts[n]-st[n])}
                   for n in range(1, 513) if ts[n] != st[n]]
    return {"word_grammar": "T(S(f)) versus S(T(f))", "polynomial_grammar": "single monomial of degree 0..3 in six measured input coefficients",
            "feature_names": ["f(p)", "f(q)", "f(p^2)", "f(p*q)", "f(p^2*q)", "f(q^2)"],
            "monomials_scored": len(monomials), "training_records": 8, "held_out_records": len(data)-8,
            "records": data, "training_fits": fits, "learned_law": "(T S f-S T f)(p^2*q)=f(p)^2*f(q), distinct primes p,q",
            "universal_support_law": "The commutator vanishes on prime powers and squarefree indices for all normalized inputs",
            "first_zeta_commutator_difference": differences[0], "first_zeta_differences": differences[:16],
            "all_finite_support_checks_passed": all(x["vanishes_on_squarefree_and_prime_power_indices"] for x in data),
            "analytic_bridge_for_full_commutator_Re_s_gt_half": "not established; not promoted as an RH-domain operator"}


def main():
    started = time.monotonic()
    output = Path(__file__).resolve().parent/"projection-results"
    output.mkdir(exist_ok=True)
    print("Learning a diagonal intertwiner from basis identities, without zeta mask labels", flush=True)
    search = projection_search()
    print(f"Programs={search['programs_checked']}; training fits={len(search['training_fits'])}; survivors={len(search['survivors'])}", flush=True)
    checks = projection_checks()
    hierarchy = prime_hierarchy_checks()
    commutator = commutator_search()
    assert checks["all_passed"] and commutator["all_finite_support_checks_passed"]
    result = {"operator": "M(f)(n)=1[sum_p s_2(v_p(n))=s_2(Omega(n))]*f(n)",
              "domain": "all rational arithmetic functions; logarithmic projection requires f(1)=1",
              "canonical_characterization": "unique diagonal A-to-G algebra homomorphism preserving every prime-power impulse",
              "search": search, "formal_checks": checks, "prime_projection_hierarchy": hierarchy,
              "commutator_search": commutator,
              "zeta_action": "M(u)=chi; F_chi(s)=product_{j>=0}(1+P(2^j*s)), initially Re(s)>1",
              "analytic_representation": "F_chi=C(s)*log(zeta(s))+C(s)*(1-Q(s)), with C=product_{j>=1}(1+P(2^j*s)) and Q=sum_{k>=2}P(k*s)/k holomorphic on Re(s)>1/2",
              "zero_preserving_claim": "not made; C may vanish, and a logarithmic RH criterion differs from preserving zeta zeros",
              "proof": "projection_proof.txt", "historical_novelty": "unresolved; multinomial parity, monomial quotients and formal logarithms are known frameworks",
              "counts_as_verified_new_operator": False, "elapsed_seconds": time.monotonic()-started}
    (output/"projection_search.json").write_text(json.dumps(result, indent=2)+"\n")
    print(f"Projection laws passed={checks['all_passed']}; commutator cubic law recovered; elapsed={result['elapsed_seconds']:.1f}s")


if __name__ == "__main__":
    main()

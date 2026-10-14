#!/usr/bin/env python3
"""Search entire cross-prime interaction profiles, not only a cubic term.

The labelled tensor grammar retains one prime exponent and a count of
distinct other primes. Binomial factors count assignments of those labels;
it does not silently replace missing large integer indices by zero.
"""

from fractions import Fraction as Q
from contextlib import contextmanager
from itertools import product
from math import comb, factorial
from pathlib import Path
import json
import random
import time

import flint

from exact_arithmetic import factorization, normalized_power, sequence
from global_carry_probe import global_transfer
from root_transfer_probe import transfer


BASE = Path(__file__).resolve().parent


@contextmanager
def series_capacity(capacity):
    previous = flint.ctx.cap
    flint.ctx.cap = capacity
    try:
        yield
    finally:
        flint.ctx.cap = previous


def tensor_zero(e_max, k_max):
    return [[Q(0)]*(k_max+1) for _ in range(e_max+1)]


def tensor_product(left, right, kind):
    e_max, k_max = len(left)-1, len(left[0])-1
    result = tensor_zero(e_max, k_max)
    for e in range(e_max+1):
        for k in range(k_max+1):
            for i in range(e+1):
                for j in range(k+1):
                    if kind == "A" and i & (e-i):
                        continue
                    if kind == "G" and (i+j) & (e-i+k-j):
                        continue
                    if left[i][j] and right[e-i][k-j]:
                        result[e][k] += comb(k, j)*left[i][j]*right[e-i][k-j]
    return result


def tensor_series(values, kind, operation):
    e_max, k_max = len(values)-1, len(values[0])-1
    unit = tensor_zero(e_max, k_max)
    unit[0][0] = Q(1)
    source = [row[:] for row in values]
    if operation == "LOG":
        assert source[0][0] == 1
        source[0][0] -= 1
        output = tensor_zero(e_max, k_max)
    else:
        assert source[0][0] == 0
        output = [row[:] for row in unit]
    term, coefficient = unit, Q(1)
    for order in range(1, e_max+k_max+1):
        term = tensor_product(term, source, kind)
        if not any(any(row) for row in term):
            break
        coefficient = Q((-1)**(order+1), order) if operation == "LOG" else coefficient/order
        for e in range(e_max+1):
            for k in range(k_max+1):
                output[e][k] += coefficient*term[e][k]
    return output


def tensor_transfer(values, kind):
    return tensor_series(tensor_series(values, "D", "LOG"), kind, "EXP")


def tensor_zeta_power(alpha, e_max=6, k_max=16):
    u = [[Q(1)]*(k_max+1) for _ in range(e_max+1)]
    h = tensor_series(u, "D", "LOG")
    return tensor_series([[Q(alpha)*value for value in row] for row in h], "D", "EXP")


def model_value(model, k, alpha):
    value = Q(factorial(k+model["factorial_shift"]))**model["factorial_power"]
    value *= Q(k)**model["k_power"]
    value *= (-1)**(model["alternating"]*k)
    value *= Q(alpha)**(model["alpha_k_multiplier"]*k+model["alpha_offset"])
    return Q(model["scale"])*value


def factorial_grammar(profiles):
    fits, scored = [], 0
    for shift, power, k_power, alternating, a, b in product(
            (-1, 0, 1, 2), (-1, 0, 1, 2), (-1, 0, 1, 2), (0, 1), range(3), range(5)):
        model = {"factorial_shift": shift, "factorial_power": power, "k_power": k_power,
                 "alternating": alternating, "alpha_k_multiplier": a, "alpha_offset": b, "scale": "1"}
        scored += 1
        model["scale"] = str(Q(profiles["1"][2][2])/model_value(model, 2, Q(1)))
        if not all(model_value(model, k, Q(1)) == Q(profiles["1"][2][k]) for k in range(2, 6)):
            continue
        witness = None
        for alpha, table in profiles.items():
            for k in range(2, 17):
                if alpha == "1" and k < 6:
                    continue
                predicted, observed = model_value(model, k, Q(alpha)), Q(table[2][k])
                if predicted != observed:
                    witness = {"alpha": alpha, "other_distinct_primes": k,
                               "predicted": str(predicted), "observed": str(observed)}
                    break
            if witness:
                break
        fits.append({**model, "training_passed": True, "held_out_passed": witness is None,
                     "first_counterexample": witness})
    survivors = [x for x in fits if x["held_out_passed"]]
    assert survivors
    return {"programs_scored": scored, "training_alpha": "1", "training_k": [2, 3, 4, 5],
            "held_out_k_cutoff": 16, "fresh_alpha": [x for x in profiles if x != "1"],
            "training_fits": fits, "survivors": survivors,
            "interpretation": "(-1)^(k+1)*k!/2*alpha^(k+2), k>=2; the k=1 cubic has an extra factor two",
            "same_formula_arity_one_negative_control_rejected": model_value(survivors[0], 1, Q(1)) != Q(profiles["1"][2][1]),
            "survivor_count_is_not_operator_count": True}


def proper_submasks(e):
    j = (e-1) & e
    while True:
        yield j
        if j == 0:
            return
        j = (j-1) & e


def local_profile(degree=256, alpha=Q(1)):
    """Exact local first-other-prime commutator via rational formal series."""
    alpha = flint.fmpq(Q(alpha).numerator, Q(alpha).denominator)
    h = [flint.fmpq(1)]
    for e in range(1, degree+1):
        h.append(alpha*sum((h[j] for j in proper_submasks(e)), flint.fmpq(0))/e)
    with series_capacity(degree+1):
        hs = flint.fmpq_series(h, prec=degree+1)
        log_series = hs.log()
        assert log_series.prec >= degree+1
        logarithm = list(log_series.coeffs())
    logarithm += [flint.fmpq(0)]*(degree+1-len(logarithm))
    t2 = [flint.fmpq(1)]
    for e in range(1, degree+1):
        t2.append(sum(((e-j)*logarithm[e-j]*t2[j] for j in proper_submasks(e)), flint.fmpq(0))/e)
    with series_capacity(degree+1):
        even = flint.fmpq_series([value if e % 2 == 0 else 0 for e, value in enumerate(h)], prec=degree+1)
        ratio = even/hs
        assert ratio.prec >= degree+1
        g = list(ratio.coeffs())
    g += [flint.fmpq(0)]*(degree+1-len(g))
    mixed = []
    for e in range(degree+1):
        total = t2[e]*g[0]
        if e:
            total += sum((t2[j]*g[e-j] for j in proper_submasks(e)), flint.fmpq(0))
        mixed.append(alpha*(total-(t2[e] if e % 2 == 0 else 0)))
    return {"H": h, "LOG_H": logarithm, "T_H": t2, "H_even_over_H": g, "commutator": mixed}


def local_norm_certificate(profile, degree=128, radius=Q(39, 50)):
    h = [Q(str(x)) for x in profile["H"]]
    head = sum((abs(h[e]-h[e-1])*radius**e for e in range(1, degree+1)), Q(0))
    tail = radius**(degree+1)/(1-radius)  # 0<=h_e<=1, hence |h_e-h_(e-1)|<=1.
    correction = head+tail
    assert correction < 1
    k_bound = 1/((1-radius)*(1-correction))
    commutator_bound = k_bound*(k_bound+1)
    return {"radius": str(radius), "degree": degree, "R_head_norm": str(head),
            "R_infinite_tail_norm": str(tail), "R_total_norm_bound": str(correction),
            "R_total_decimal": float(correction), "local_H_zero_free_disk_passed": correction < 1,
            "T_H_and_H_even_over_H_norm_bound": str(k_bound),
            "first_other_prime_commutator_weighted_norm_bound": str(commutator_bound),
            "half_plane_bridge": "A(s)=sum_p d(p^-s), B(s)=sum_p d(p^-s)*p^-s are holomorphic on Re(s)>1/2",
            "full_commutator_bridge_not_implied": True}


def dense_integer_checks(profiles):
    records = []
    for alpha in (Q(1, 2), Q(1), Q(3, 2)):
        cutoff = 512
        f = normalized_power(sequence([1]*cutoff), alpha)
        ts, st = transfer(global_transfer(f)), global_transfer(transfer(f))
        local = local_profile(9, alpha)
        checked, passed = 0, True
        for n in range(2, cutoff+1):
            factors = factorization(n)
            repeated = [(p, e) for p, e in factors.items() if e > 1]
            if len(repeated) != 1:
                continue
            e = repeated[0][1]
            k = len(factors)-1
            if k == 1:
                expected = Q(str(local["commutator"][e]))
            elif e == 2:
                expected = Q(profiles[str(alpha)][e][k])
            else:
                continue
            checked += 1
            passed &= ts[n]-st[n] == expected
        records.append({"alpha": str(alpha), "actual_integer_cutoff": cutoff,
                        "generic_full_arithmetic_TS_ST_coefficients_checked": checked, "all_passed": passed})
    return records


def suspension_kernel_search():
    fits = []
    for a, b in product(range(8), repeat=2):
        if not all(int(not (i+a) & (j+b)) == int(not i & (j+1)) for i in range(4) for j in range(4)):
            continue
        failure = next(((i, j) for i in range(64) for j in range(64)
                        if int(not (i+a) & (j+b)) != int(not i & (j+1))), None)
        fits.append({"first_offset": a, "second_offset": b, "held_out_passed": failure is None,
                     "first_counterexample": list(failure) if failure else None})
    return {"models_scored": 64, "training_exponents": [0, 3], "held_out_exponents": [0, 63],
            "training_fits": fits, "survivors": [x for x in fits if x["held_out_passed"]],
            "law": "B(t,k)_e=sum_(a+b=e) 1[a&(b+1)=0]*t_a*k_b = coefficient_(e+1)(t A (x*k))"}


def first_other_prime_module_checks():
    rng = random.Random(2026100620)
    records = []
    for degree in (12, 17, 24):
        f0 = [Q(1)]+[Q(rng.randint(-3, 3), rng.randint(1, 5)) for _ in range(degree)]
        f1 = [Q(rng.randint(-3, 3), rng.randint(1, 5)) for _ in range(degree+1)]
        with series_capacity(degree+1):
            s0 = flint.fmpq_series([flint.fmpq(x.numerator, x.denominator) for x in f0], prec=degree+1)
            s1 = flint.fmpq_series([flint.fmpq(x.numerator, x.denominator) for x in f1], prec=degree+1)
            logs, ratio = s0.log(), s1/s0
            assert logs.prec >= degree+1 and ratio.prec >= degree+1
            h, k = list(logs.coeffs()), list(ratio.coeffs())
        h += [flint.fmpq(0)]*(degree+1-len(h))
        k += [flint.fmpq(0)]*(degree+1-len(k))
        t = [flint.fmpq(1)]
        for e in range(1, degree+1):
            t.append(sum(((e-j)*h[e-j]*t[j] for j in proper_submasks(e)), flint.fmpq(0))/e)
        predictions = {kind: [] for kind in ("A", "G")}
        for e in range(degree+1):
            predictions["A"].append(sum((t[a]*k[e-a] for a in range(e+1) if not a & (e-a)), flint.fmpq(0)))
            predictions["G"].append(sum((t[a]*k[e-a] for a in range(e+1) if not a & (e-a+1)), flint.fmpq(0)))
        source = [[a, b] for a, b in zip(f0, f1)]
        actual = {kind: tensor_transfer(source, kind) for kind in ("A", "G")}
        laws = {"prime_power_rows_agree": all(actual[kind][e][0] == Q(str(t[e])) for kind in actual for e in range(degree+1)),
                "T_first_other_prime_action": all(actual["A"][e][1] == Q(str(predictions["A"][e])) for e in range(degree+1)),
                "S_first_other_prime_action": all(actual["G"][e][1] == Q(str(predictions["G"][e])) for e in range(degree+1))}
        records.append({"degree": degree, "f0": [str(x) for x in f0], "f1": [str(x) for x in f1], "laws": laws})
    basis = all(int(not a & b)*int(not (a+b) & (c+1))
                == int(not b & (c+1))*int(not a & (b+c+1))
                for a, b, c in product(range(16), repeat=3))
    return {"records": records, "module_associativity_basis_triples": 16**3,
            "module_associativity_basis_passed": basis,
            "not_commutative_binary_product_control": int(not 0 & (1+1)) != int(not 1 & (0+1)),
            "all_passed": basis and all(all(x["laws"].values()) for x in records)}


def main():
    started = time.monotonic()
    output = BASE/"coupling-results"
    output.mkdir(exist_ok=True)
    profiles, inputs = {}, {}
    for alpha in (Q(1), Q(-1, 2), Q(2, 3), Q(3, 2), Q(5, 7), Q(0), Q(1, 2)):
        f = tensor_zeta_power(alpha)
        ts, st = tensor_transfer(tensor_transfer(f, "G"), "A"), tensor_transfer(tensor_transfer(f, "A"), "G")
        profiles[str(alpha)] = [[str(a-b) for a, b in zip(row_a, row_b)] for row_a, row_b in zip(ts, st)]
        inputs[str(alpha)] = [[str(x) for x in row] for row in f]
    grammar = factorial_grammar(profiles)
    profile = local_profile()
    certificate = local_norm_certificate(profile)
    dense = dense_integer_checks(profiles)
    module = first_other_prime_module_checks()
    assert all(x["all_passed"] for x in dense)
    assert module["all_passed"]
    result = {"operator_word": "T S-S T", "inputs": "ordinary arithmetic powers u^{*alpha}, with series zeta(s)^alpha",
              "tensor_semantics": "Each (e,k) is one prime to exponent e and k labelled distinct other primes to exponent 1; binomial coefficients enumerate label subsets",
              "declared_tensor_cutoffs": {"one_prime_exponent": 6, "other_distinct_prime_count": 16},
              "large_integer_lookahead_is_symbolic_not_zero_padded": True,
              "rational_series_context_capacity_and_output_precision_asserted": True,
              "input_tensor_profiles": inputs, "commutator_tensor_profiles": profiles,
              "factorial_grammar": grammar, "suspension_kernel_grammar": suspension_kernel_search(),
              "generic_first_other_prime_module_checks": module,
              "first_other_prime_local_profile": {key: [str(x) for x in values] for key, values in profile.items()},
              "local_norm_certificate": certificate, "dense_integer_validation": dense,
              "full_commutator_Re_s_gt_half_analytic_bridge": "not established; factorial multi-prime sector prevents extrapolation from the first-other-prime sector",
              "RH_scope": "A proved half-plane bridge for one selected interaction sector is not a bridge or estimate for the full commutator",
              "historical_novelty": "unresolved; known formal algebra and labelled combinatorics are not themselves new",
              "counts_as_separate_verified_new_operator": False,
              "proof": "coupling_proof.txt", "elapsed_seconds": time.monotonic()-started}
    (output/"coupling_search.json").write_text(json.dumps(result, indent=2)+"\n")
    print(f"Coupling programs={grammar['programs_scored']}; fits={len(grammar['training_fits'])}; "
          f"equivalent survivors={len(grammar['survivors'])}; dense checks passed; elapsed={result['elapsed_seconds']:.2f}s")


if __name__ == "__main__":
    main()

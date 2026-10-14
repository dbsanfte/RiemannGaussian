#!/usr/bin/env python3
"""Search arithmetic kernels using actual integer order, addition and residues.

Only selected surviving kernels receive universal proofs. A finite
associativity match is explicitly retained as a candidate, not a theorem.
The logarithmic-height product distinguishes actual prime labels.
"""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import gcd, isqrt
from pathlib import Path
import hashlib
import json
import random
import time

from exact_arithmetic import convolve, factorization, formal_log, normalized_power, sequence, unit, weighted_convolution
from root_transfer_probe import algebra_exp, algebra_log


BASE = Path(__file__).resolve().parent


def floor_log(n, base):
    if base == 2:
        return n.bit_length()-1
    exponent, power = 0, base
    while power <= n:
        exponent += 1
        power *= base
    return exponent


def integer_root(n, degree):
    if degree == 2:
        return isqrt(n)
    low, high = 0, 1 << ((n.bit_length()+degree-1)//degree)
    while low < high:
        middle = (low+high+1)//2
        if middle**degree <= n:
            low = middle
        else:
            high = middle-1
    return low


@lru_cache(maxsize=250000)
def feature(n, kind, parameter):
    if kind in ("floor_log", "ceil_log", "nearest_log"):
        h = floor_log(n, parameter)
        if kind == "ceil_log":
            h += parameter**h != n
        elif kind == "nearest_log":
            h += n*n >= parameter**(2*h+1)
        return h
    if kind == "floor_quotient":
        return n//parameter-1//parameter
    if kind == "remainder":
        return n % parameter-1 % parameter
    if kind == "digit_sum":
        total, m = 0, n
        while m:
            total += m % parameter
            m //= parameter
        return total-1
    if kind == "floor_root":
        return integer_root(n, parameter)-1
    if kind == "nonunit_modulus":
        return -int(gcd(n, parameter) > 1)
    if kind == "omega":
        return sum(factorization(n).values())
    if kind == "v2":
        return (n & -n).bit_length()-1
    if kind == "mixed_logs":
        return floor_log(n, 2)+parameter*floor_log(n, 3)
    raise ValueError(kind)


def kernel(model, a, b):
    if model["family"] == "direct":
        name, m = model["predicate"], model["parameter"]
        if name == "coprime_sum_product":
            return int(gcd(a+b, a*b) == 1)
        if a == 1 or b == 1:
            return 1
        if name == "shifted_coprimality":
            return int(gcd(a-1, b-1) == 1)
        if name == "additive_residue_carry":
            return int(a % m+b % m < m)
        raise ValueError(name)
    kind, p = model["feature"], model["parameter"]
    c = feature(a*b, kind, p)-feature(a, kind, p)-feature(b, kind, p)
    return int({"zero": c == 0, "nonnegative": c >= 0, "nonpositive": c <= 0,
                "even": c % 2 == 0, "absolute_at_most_one": abs(c) <= 1}[model["predicate"]])


def grammar():
    specs = [(kind, base) for kind in ("floor_log", "ceil_log", "nearest_log", "digit_sum") for base in range(2, 10)]
    specs += [(kind, m) for kind in ("floor_quotient", "remainder", "nonunit_modulus") for m in range(2, 17)]
    specs += [("floor_quotient", 1), ("floor_root", 2), ("floor_root", 3), ("omega", 0), ("v2", 0)]
    specs += [("mixed_logs", m) for m in (-2, -1, 1, 2)]
    for name, p in specs:
        for predicate in ("zero", "nonnegative", "nonpositive", "even", "absolute_at_most_one"):
            yield {"family": "degree_defect", "feature": name, "parameter": p, "predicate": predicate}
    yield {"family": "direct", "predicate": "coprime_sum_product", "parameter": 0}
    yield {"family": "direct", "predicate": "shifted_coprimality", "parameter": 0}
    for m in range(2, 17):
        yield {"family": "direct", "predicate": "additive_residue_carry", "parameter": m}


def associator_failure(model, triples):
    for a, b, c in triples:
        left = kernel(model, a, b)*kernel(model, a*b, c)
        right = kernel(model, b, c)*kernel(model, a, b*c)
        if left != right:
            return {"a": str(a), "b": str(b), "c": str(c), "left": left, "right": right}
    return None


def kernel_search():
    records = []
    boundary = [(2**k-1, 2**k+1, 3**j) for k, j in ((10, 7), (31, 17), (64, 41), (128, 79))]
    boundary += [(a, b, c) for a, b, c in boundary for a, b, c in ((a,b,c), (a,c,b), (b,c,a))]
    for model in grammar():
        training = associator_failure(model, product(range(1, 5), repeat=3))
        if training:
            records.append({**model, "training_passed": False, "first_counterexample": training})
            continue
        failure = associator_failure(model, product(range(1, 25), repeat=3))
        # Omega is a calibration with a known additive law. Factoring an
        # unknown 128-bit boundary integer by trial division is unnecessary.
        boundary_checked = model.get("feature") != "omega"
        if failure is None and boundary_checked:
            failure = associator_failure(model, boundary)
        fingerprint = None
        if failure is None:
            fingerprint = hashlib.sha256(bytes(kernel(model, a, b) for a in range(1, 129)
                                              for b in range(1, 1024//a+1))).hexdigest()
        records.append({**model, "training_passed": True, "held_out_passed": failure is None,
                        "first_counterexample": failure, "finite_basis_fingerprint": fingerprint,
                        "large_boundary_stress_performed": boundary_checked,
                        "finite_match_is_not_universal_proof": True})
    survivors = [x for x in records if x.get("held_out_passed")]
    return {"programs_scored": len(records), "training_triplet_range": [1, 4],
            "held_out_triplet_range": [1, 24], "exact_large_power_boundary_stresses": [[str(x) for x in t] for t in boundary],
            "records": records, "training_fits": sum(x["training_passed"] for x in records),
            "held_out_survivors": len(survivors),
            "distinct_finite_basis_fingerprints": len({x["finite_basis_fingerprint"] for x in survivors}),
            "finite_fingerprint_classes_are_not_verified_operator_count": True,
            "selected_survivor_universal_certificates": ["floor_log_no_carry", "ceil_log_no_carry"],
            "all_other_finite_survivors_require_separate_proof": True}


def upper_log(n,base):
    h=floor_log(n,base)
    return h+int(base**h!=n)


def carry(a, b, base=2, orientation="floor"):
    if orientation=="floor":
        return floor_log(a*b, base)-floor_log(a, base)-floor_log(b, base)
    return upper_log(a,base)+upper_log(b,base)-upper_log(a*b,base)


def size_product(a, b, base=2, parameter=Q(0), orientation="floor"):
    parameter = Q(parameter)
    return weighted_convolution(a, b, lambda i,j: parameter if carry(i,j,base,orientation) else Q(1))


def size_transfer(f, base=2, orientation="floor"):
    return algebra_exp(formal_log(f), lambda a,b: size_product(a,b,base,orientation=orientation))


def root_lift(f, q, base=2, orientation="floor"):
    root = normalized_power(f, Q(1,q))
    result = unit(len(f)-1)
    factor, m = root, q
    while m:
        if m & 1:
            result = size_product(result, factor, base,orientation=orientation)
        m >>= 1
        if m:
            factor = size_product(factor, factor, base,orientation=orientation)
    return result


def exact_operator_checks():
    rng, records = random.Random(2026100621), []
    for cutoff in (32, 65, 128):
        a,b = [sequence([1]+[Q(rng.randint(-3,3),rng.randint(1,5)) for _ in range(cutoff-1)]) for _ in range(2)]
        for base,orientation in product((2,3,6),("floor","ceil")):
            prod = lambda x,y: size_product(x,y,base,orientation=orientation)
            ua,ub = size_transfer(a,base,orientation),size_transfer(b,base,orientation)
            inverse = lambda x: algebra_exp(algebra_log(x,prod),convolve)
            ordinary = convolve(a,b)
            left_height = convolve([v*floor_log(i,base) if i else Q(0) for i,v in enumerate(a)],b)
            right_height = convolve(a,[v*floor_log(i,base) if i else Q(0) for i,v in enumerate(b)])
            coboundary = [ordinary[n]+left_height[n]+right_height[n]-floor_log(n,base)*ordinary[n]
                          if n else Q(0) for n in range(cutoff+1)]
            if orientation=="ceil":
                left_height=convolve([v*upper_log(i,base) if i else Q(0) for i,v in enumerate(a)],b)
                right_height=convolve(a,[v*upper_log(i,base) if i else Q(0) for i,v in enumerate(b)])
                coboundary=[ordinary[n]-left_height[n]-right_height[n]+upper_log(n,base)*ordinary[n]
                            if n else Q(0) for n in range(cutoff+1)]
            laws = {"unit_group_transfer": size_transfer(convolve(a,b),base,orientation) == prod(ua,ub),
                    "inverse_transfer": inverse(ua) == a,
                    "forward_inverse_transfer": size_transfer(inverse(a),base,orientation) == a,
                    "prefix_consistency": ua[:cutoff//2+1] == size_transfer(a[:cutoff//2+1],base,orientation),
                    "bilinear_coboundary_formula": prod(a,b) == coboundary}
            records.append({"cutoff": cutoff, "base": base,"orientation":orientation,"input_a": [str(x) for x in a],
                            "input_b": [str(x) for x in b], "output_a": [str(x) for x in ua], "laws": laws})
    compatible = []
    for base,orientation in product((2,3,6),("floor","ceil")):
        for t in (Q(-2), Q(-1,3), Q(0), Q(1), Q(5,2)):
            passed = all((t if carry(a,b,base,orientation) else 1)*(t if carry(a*b,c,base,orientation) else 1)
                         == (t if carry(b,c,base,orientation) else 1)*(t if carry(a,b*c,base,orientation) else 1)
                         for a,b,c in product(range(1,17), repeat=3))
            compatible.append({"base": base,"orientation":orientation,"parameter": str(t), "passed": passed})
    return {"records": records, "compatible_product_parameter_checks": compatible,
            "all_passed": all(all(x["laws"].values()) for x in records) and all(x["passed"] for x in compatible)}


def probability_profile(factors, base=2, alpha=Q(1)):
    # Sparse divisor-poset EXP using the additive Euler degree Omega.
    # This is different from the dense finite-power production evaluator.
    divisors = [(1, 0)]
    for p,e in factors.items():
        divisors = [(n*p**j, grade+j) for n,grade in divisors for j in range(e+1)]
    values = {1:Q(1)}
    for n,grade in sorted(divisors):
        if n == 1:
            continue
        total = Q(0)
        for p,e in factors.items():
            power = p
            for j in range(1,e+1):
                if n % power:
                    break
                if not carry(power,n//power,base):
                    total += values[n//power]
                power *= p
        values[n] = Q(alpha)*total/grade
    n = max(values)
    return {"factorization": [[p,e] for p,e in factors.items()], "n": str(n),
            "divisor_lookahead_explicit": len(values), "alpha": str(alpha), "base": base,
            "coefficient": str(values[n])}


def zeta_profiles(cutoff=512):
    u=sequence([1]*cutoff)
    records=[]
    for base,orientation in product((2,3,6),("floor","ceil")):
        limit=size_transfer(u,base,orientation)
        roots=[]
        for q in (2,3,4,8,16,64):
            values=root_lift(u,q,base,orientation)
            roots.append({"order":q, "coefficients":[str(x) for x in values],
                          "all_coefficients_in_unit_interval":all(0<=x<=1 for x in values),
                          "maximum_difference_from_limit":str(max(abs(x-y) for x,y in zip(values,limit)))})
        records.append({"base":base,"orientation":orientation,"cutoff":cutoff,"limit_coefficients":[str(x) for x in limit],
                        "all_limit_coefficients_in_unit_interval":all(0<=x<=1 for x in limit),"root_lifts":roots})
    collapsed=[]
    for m in (1,2,3,5,8,16):
        h=lambda n:n//m-1//m
        prod=lambda a,b:weighted_convolution(a,b,lambda i,j:int(h(i*j)==h(i)+h(j)))
        output=algebra_exp(formal_log(u),prod)
        log_u=formal_log(u)
        collapsed.append({"quotient_modulus":m,"proved_terminal_cutoff":2*m+2,
                          "tail_agrees_with_classical_LOG_u":all(output[n]==log_u[n] for n in range(2*m+3,cutoff+1))})
    return records,collapsed


def resonance_projection(f,base):
    out=[Q(0)]*len(f)
    n=1
    while n<len(f):
        out[n]=f[n]
        n*=base
    return out


def paired_root_checks(cutoff=512):
    u=sequence([1]*cutoff)
    records=[]
    for base,beta in product((2,6,12),(Q(1,2),Q(1,4),Q(1,8),Q(1))):
        root=normalized_power(u,beta)
        ordinary=convolve(root,root)
        lower=size_product(root,root,base,orientation="floor")
        upper=size_product(root,root,base,orientation="ceil")
        resonant_ordinary=resonance_projection(ordinary,base)
        paired=[(a+b-c+d)/2 for a,b,c,d in zip(lower,upper,ordinary,resonant_ordinary)]
        target=convolve(root,resonance_projection(root,base))
        records.append({"base":base,"beta":str(beta),"cutoff":cutoff,
                        "lower_square_coefficients":[str(x) for x in lower],
                        "upper_square_coefficients":[str(x) for x in upper],
                        "paired_coefficients":[str(x) for x in paired],
                        "paired_root_times_resonance_identity_passed":paired==target})
    return {"definition":"B_(b,beta)(f)=1/2*(f^beta K_floor f^beta+f^beta K_ceil f^beta-f^(2beta)+R_b(f^(2beta)))",
            "universal_law":"B_(b,beta)(f)=f^beta * R_b(f^beta); R_b keeps only indices b^k",
            "zeta_bridge":"B_(b,beta)(u)(s)=zeta(s)^beta*R_(b,beta)(s)",
            "correction_domain":"R_(b,beta) holomorphic and nonzero on Re(s)>0 for all integer b>=2 and beta in [0,1]",
            "all_dyadic_root_criterion":"RH iff every pole-cancelled B_(b,1/2^k)(u) has single-valued holomorphic continuation to Re(s)>1/2",
            "irrational_parameter_corollary":"Any one fixed irrational beta in (0,1) gives the same RH-equivalent continuation criterion; numerical scalar grammar uses rational parameters only",
            "resonance_projection_is_ordinary_algebra_homomorphism_iff":"base b is prime",
            "single_square_root_condition_is_insufficient":True,
            "counts_as_extra_primitive_operator":False,
            "records":records,"all_passed":all(x['paired_root_times_resonance_identity_passed'] for x in records)}


def main():
    started=time.monotonic()
    output=BASE/"size-results"
    output.mkdir(exist_ok=True)
    search=kernel_search()
    print(f"Kernel grammar: {search['programs_scored']} programs; training fits={search['training_fits']}; fresh survivors={search['held_out_survivors']}",flush=True)
    exact=exact_operator_checks()
    profiles,collapsed=zeta_profiles()
    paired=paired_root_checks()
    sparse=[probability_profile(f,base,alpha) for f in ({2:8,3:6,5:4},{3:9,7:5},{2:12,11:6})
            for base in (2,3,6) for alpha in (Q(1),Q(1,2),Q(3,2))]
    unitary=all(kernel({"family":"direct","predicate":"coprime_sum_product","parameter":0},a,b)==int(gcd(a,b)==1)
                for a,b in product(range(1,129),repeat=2))
    assert exact['all_passed'] and paired['all_passed'] and all(x['tail_agrees_with_classical_LOG_u'] for x in collapsed)
    assert all(x['all_limit_coefficients_in_unit_interval'] and all(y['all_coefficients_in_unit_interval'] for y in x['root_lifts']) for x in profiles)
    result={"kernel_grammar":search,"exact_operator_checks":exact,"zeta_profiles":profiles,
            "paired_root_identity":paired,
            "large_integer_sparse_divisor_profiles":sparse,"floor_quotient_collapse_controls":collapsed,
            "known_unitary_convolution_calibration_passed":unitary,
            "selected_candidate":{"height":"h_b(n)=floor(log_b(n)), computed by exact integer comparisons",
                "kernel":"K_floor: equal floor heights; K_ceil: equal ceiling heights",
                "transfer":"U_(b,orientation)(f)=EXP_K(LOG_D(f))",
                "ordinary_product_splitting":"Dirichlet=no_carry+carry_only; both pieces associative, carry_only has no unit",
                "compatible_family":"K_t has weight t^c, with c=h(ab)-h(a)-h(b) for floor and c=H(a)+H(b)-H(ab) for ceiling; every t gives an associative unital product",
                "nonzero_t_status":"classical scalar-weight transport; zero t is a degenerate product",
                "root_limit":"q-fold K_0 power of ordinary qth root converges coefficientwise and locally uniformly on Re(s)>1 for the zeta input",
                "all_q_zeta_coefficients_between_zero_and_one_proved":True,
                "actual_prime_relabeling_invariance_rejected":{"pair_2_3":carry(2,3)==0,"pair_5_7":carry(5,7)==0},
                "size_dependence_scope":"Depends on assigned multiplicative sizes; also definable on normed free multiplicative monoids",
                "full_half_plane_bridge_Re_s_gt_half":"Finite-power holomorphic pole cancellation is ruled out by size_resonance_proof.txt; other continuation unestablished",
                "historical_novelty":"unresolved; general weighted/degenerate convolution frameworks are classical",
                "counts_as_verified_historically_new":False},
            "proof":"size_carry_proof.txt","elapsed_seconds":time.monotonic()-started}
    (output/"size_carry_search.json").write_text(json.dumps(result,indent=2)+"\n")
    print(f"Exact transfer and root-lift checks passed; elapsed={result['elapsed_seconds']:.2f}s")


if __name__=="__main__":
    main()

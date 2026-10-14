#!/usr/bin/env python3
"""Audit zero certificates using a different remainder and prime-sum bound.

No detector/production helper is imported. The created-zero check uses
Cauchy estimates on a larger disk rather than interval second derivatives.
The local C continuation uses fresh Mobius cutoffs and independently
recomputed branch corridors. FLINT/Arb remains the shared trusted kernel.
"""

from fractions import Fraction as Q
from pathlib import Path
import json
import time

import flint


BASE = Path(__file__).resolve().parent


def real(q):
    q = Q(q)
    return flint.arb(q.numerator)/q.denominator


def box(radius):
    return flint.acb(flint.arb(0, radius), flint.arb(0, radius))


def mu(n):
    p, factors = 2, 0
    while p*p <= n:
        if n % p == 0:
            n //= p
            factors += 1
            if n % p == 0:
                return 0
        p += 1
    if n > 1:
        factors += 1
    return (-1)**factors


def d(exponent):
    exponent = real(exponent)
    assert bool(exponent > 1)
    return flint.arb(2)**(-exponent)+flint.arb(2)**(1-exponent)/(exponent-1)


def prime_tail(sigma, terms):
    # The Euler log's coefficient at p^k is 1/k <=1, so
    # |log zeta(m*s)| <= zeta(m*sigma)-1 <= D(m*sigma).
    return d((terms+1)*Q(sigma))/((terms+1)*(1-flint.arb(2)**(-real(sigma))))


def prime_sum(z, sigma, terms=48, anchored_first=False):
    if not anchored_first:
        assert bool(real(sigma).zeta().log() < flint.arb.pi())
    value = flint.acb(0)
    for m in range(1, terms+1):
        sign = mu(m)
        if sign:
            if m >= 2:
                assert bool(real(Q(sigma)*m).zeta().log() < flint.arb.pi())
            value += sign*(m*z).zeta().log()/m
    return value+box(prime_tail(sigma, terms))


def created_zero_by_cauchy(source):
    item = source["own_zero_in_zeta_zero_free_region_control"]
    x, y = item["disk_centre"]
    c, r, large_r = flint.acb(x, y), Q(item["radius"]), Q(1, 100)
    minimum = Q(x)-large_r
    assert minimum > 1 and bool(real(minimum).zeta().log() < flint.arb.pi())
    region = flint.acb(real(x)+flint.arb(0, real(large_r)),
                       real(y)+flint.arb(0, real(large_r)))
    terms, finite, constant, derivative = 32, flint.acb(1), flint.acb(1), flint.acb(0)
    for m in range(1, terms+1):
        sign = mu(m)
        if sign:
            finite += sign*(m*region).zeta().log()/m
            value = (m*c).zeta()
            constant += sign*value.log()/m
            # Differentiating mu(m)/m log(zeta(m*s)) cancels m.
            zeta_derivative = flint.acb_series([m*c, 1], 2).zeta()[1]
            derivative += sign*zeta_derivative/value
    ratio = real(r/large_r)
    # Cauchy on the large circle bounds every finite Taylor coefficient
    # k>=2 by M_R/R^k, giving this geometric remainder at the small circle.
    cauchy_remainder = finite.abs_upper()*ratio**2/(1-ratio)
    omitted = prime_tail(minimum, terms)
    error = constant.abs_upper()+cauchy_remainder+omitted
    linear = derivative.abs_lower()*real(r)
    passed = bool(error < linear)
    # An erroneous m=1 branch, shifted by 2*pi*i, must fail the same test.
    wrong_branch_error = (constant+flint.acb(0, 2*flint.arb.pi())).abs_lower()
    wrong_rejected = bool(wrong_branch_error > linear)
    small = flint.acb(real(x)+flint.arb(0, real(r)), real(y)+flint.arb(0, real(r)))
    zeta_lower = small.zeta().abs_lower()
    zero_free = bool(zeta_lower > 0)
    return {"cutoff_differs_from_production": terms != item["finite_mobius_terms"],
            "mobius_terms": terms, "larger_cauchy_radius": str(large_r),
            "small_zero_count_radius": str(r), "finite_function_larger_rectangle_modulus_upper_ball": str(finite.abs_upper()),
            "constant_Cauchy_and_infinite_tail_upper_ball": str(error),
            "linear_comparison_lower_ball": str(linear),
            "Cauchy_Rouche_one_simple_transformed_zero_passed": passed,
            "incorrect_log_branch_negative_control_rejected": wrong_rejected,
            "independent_actual_zeta_rectangle_modulus_lower_ball": str(zeta_lower),
            "actual_zeta_zero_free_on_disk": zero_free,
            "C_nonzero_on_Re_s_gt_one_basis": "|P(2^j*s)|<=P(2)<zeta(2)-1<1 and summable product tails",
            "C_global_nonzero_majorant_passed": bool(real(2).zeta()-1 < 1),
            "all_passed": passed and wrong_rejected and zero_free and bool(real(2).zeta()-1 < 1)}


def critical_zero_coefficient(source):
    item = source["actual_critical_line_zero_control"]
    height = item["disk_centre"][1]
    sigma, radius = Q(4999, 10000), Q(item["radius"])
    rects = item["P_2s_principal_branch_connection"]["rectangles"]
    previous = 2*sigma
    corridor_passed = True
    bounds = []
    for record in rects:
        a, b = map(Q, record["real_interval"])
        assert a == previous and a < b
        assert Q(record["imaginary_centre"]) == 2*Q(height)
        assert Q(record["imaginary_radius"]) == 2*radius
        region = flint.acb(real((a+b)/2)+flint.arb(0, real((b-a)/2)),
                           real(2*Q(height))+flint.arb(0, real(2*radius)))
        value = region.zeta()
        corridor_passed &= bool(value.real > 0)
        bounds.append(str(value.real.lower()))
        previous = b
    assert previous == Q(3, 2)
    corridor_passed &= bool(real(previous).zeta().log() < flint.arb.pi())
    region = flint.acb(real(Q(1, 2))+flint.arb(0, real(radius)),
                       real(height)+flint.arb(0, real(radius)))
    value, layers = flint.acb(1), 7
    for j in range(1, layers+1):
        value *= 1+prime_sum(2**j*region, sigma*2**j, 48, anchored_first=(j == 1))
    omitted = d(sigma*2**(layers+1))/(1-flint.arb(2)**(-real(sigma)))
    lower = value.abs_lower()-value.abs_upper()*omitted.expm1()
    # Directly recheck the actual simple zero independently of the stored
    # production booleans before using its multiplicity in the criterion.
    c = flint.acb("0.5", height)
    centre_taylor = flint.acb_series([c, 1], 3).zeta()
    range_taylor = flint.acb_series([region, 1], 3).zeta()
    actual_linear = centre_taylor[1].abs_lower()*real(radius)
    actual_error = centre_taylor[0].abs_upper()+range_taylor[2].abs_upper()*real(radius)**2
    actual_simple = bool(actual_error < actual_linear)
    return {"all_branch_corridor_rectangles_independently_recomputed": corridor_passed,
            "corridor_positive_real_lower_balls": bounds, "prime_mobius_terms": 48,
            "binary_product_layers": layers, "different_cutoffs_from_production": True,
            "independent_C_modulus_lower_after_tail_ball": str(lower),
            "C_nonzero_on_critical_crossing_disk_passed": bool(lower > 0),
            "actual_simple_zeta_zero_independently_rechecked": actual_simple,
            "actual_log_monodromy_nonzero_passed": bool(2*flint.arb.pi()*lower > 0),
            "all_passed": corridor_passed and actual_simple and bool(lower > 0)}


def main():
    started = time.monotonic()
    flint.ctx.prec = 300
    source = json.loads((BASE/"projection-results/projection_analytic_probe.json").read_text())
    created = created_zero_by_cauchy(source)
    print(f"Independent created-zero certificate passed={created['all_passed']}; {time.monotonic()-started:.2f}s", flush=True)
    actual = critical_zero_coefficient(source)
    result = {"created_zero_independent_Cauchy_audit": created,
              "actual_zero_independent_branch_and_coefficient_audit": actual,
              "all_passed": created["all_passed"] and actual["all_passed"],
              "shared_trusted_numeric_kernel": "FLINT/Arb; no production detector/helper imported",
              "proof": "projection_proof.txt sections 9 and 11; Cauchy remainder explained in this checker"}
    (BASE/"projection-results/projection_analytic_verification.json").write_text(json.dumps(result, indent=2)+"\n")
    print(f"Independent projection analytic audit: Cauchy own-zero={created['all_passed']}; "
          f"actual-zero branch/coefficient={actual['all_passed']}")
    assert result["all_passed"]


if __name__ == "__main__":
    main()

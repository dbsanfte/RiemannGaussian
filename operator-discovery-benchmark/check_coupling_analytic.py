#!/usr/bin/env python3
"""Independent analytic audit of the selected commutator sector.

No production helper is imported. A separate exact verifier supplies
bit-partition coefficients. This audit uses different truncations,
an elementary Euler-log tail, eight fresh branch rectangles, and a
Cauchy remainder for the actual zeta zero. Arb is the shared kernel.
"""

from fractions import Fraction as Q
from pathlib import Path
import json
import math

import flint

from check_coupling import independent_local


BASE = Path(__file__).resolve().parent


def real(q):
    q = Q(q)
    return flint.arb(q.numerator)/q.denominator


def box(r):
    return flint.acb(flint.arb(0, r), flint.arb(0, r))


def mu(n):
    p, count = 2, 0
    while p*p <= n:
        if n % p == 0:
            n //= p
            count += 1
            if n % p == 0:
                return 0
        p += 1
    return (-1)**(count+(n > 1))


def d(a):
    a = real(a)
    assert bool(a > 1)
    return flint.arb(2)**(-a)+flint.arb(2)**(1-a)/(a-1)


def prime_sum(z, sigma, anchored_first=False):
    sigma = Q(sigma)
    terms = max(1, min(40, math.ceil(80/float(sigma))))
    if not anchored_first:
        assert sigma > 1 and bool(real(sigma).zeta().log() < flint.arb.pi())
    value = flint.acb(0)
    for m in range(1, terms+1):
        sign = mu(m)
        if sign:
            if m >= 2:
                assert bool(real(m*sigma).zeta().log() < flint.arb.pi())
            value += sign*(m*z).zeta().log()/m
    # |log zeta(m*z)|<=zeta(m*sigma)-1<=D(m*sigma).
    # D((M+1+j)*sigma)<=2^(-j*sigma)*D((M+1)*sigma).
    tail = d((terms+1)*sigma)/((terms+1)*(1-flint.arb(2)**(-real(sigma))))
    return value+box(tail)


def factors(n):
    p, out = 2, []
    while p*p <= n:
        count = 0
        while n % p == 0:
            n //= p
            count += 1
        if count:
            out.append(count)
        p += 1
    if n > 1:
        out.append(1)
    return out


def affine(s, sigma, coefficients, radius, norm, degree, anchored=False):
    primes = {e: prime_sum(e*s, e*sigma, anchored_first=anchored and e == 2)
              for e in range(2, degree+2)}
    a = sum((real(coefficients[e])*primes[e] for e in range(2, degree+1)), flint.acb(0))
    b = sum((real(coefficients[e])*primes[e+1] for e in range(2, degree+1)), flint.acb(0))
    a_tail = real(norm/radius**(degree+1))*d((degree+1)*sigma)
    b_tail = real(norm/radius**(degree+1))*d((degree+2)*sigma)
    return a, b, a_tail, b_tail


def point_checks(source, coefficients, radius, norm):
    degree, cutoff = 48, 8192
    absolute = sum((real(abs(coefficients[e]))*prime_sum(flint.acb(2*e), 2*e).real
                    for e in range(2, 25)), flint.arb(0))
    absolute += real(norm/radius**25)*d(50)
    absolute *= prime_sum(flint.acb(2), 2).real
    terms = []
    for n in range(2, cutoff+1):
        fs = factors(n)
        if len(fs) == 2 and min(fs) == 1 and max(fs) >= 2:
            terms.append((n, coefficients[max(fs)]))
    records = []
    for item in source["actual_zeta_ball_checks"]:
        sigma, height = Q(item["s"][0]), item["s"][1]
        s = flint.acb(real(sigma), height)
        finite = sum((real(value)*(-s*flint.arb(n).log()).exp() for n, value in terms), flint.acb(0))
        a, b, a_tail, b_tail = affine(s, sigma, coefficients, radius, norm, degree)
        p = prime_sum(s, sigma)
        reference = a*p-b
        allowed = flint.arb(cutoff)**(2-real(sigma))*absolute+a_tail*p.abs_upper()+b_tail
        error = (finite-reference).abs_upper()
        bad = (finite+real(Q(1, 11))*(-s*flint.arb(12).log()).exp()-reference).abs_lower()
        records.append({"s": item["s"], "new_arithmetic_cutoff": cutoff,
                        "new_local_degree": degree, "error_upper_ball": str(error),
                        "tail_bound_ball": str(allowed), "within_bound": bool(error < allowed),
                        "different_coefficient_error_rejected": bool(bad > allowed),
                        "all_passed": bool(error < allowed) and bool(bad > allowed)})
    return records


def zero_control(source, coefficients, radius, norm):
    item = source["actual_critical_line_zero_control"]
    height = Q(item["disk_centre"][1])
    r, large_r = Q(item["radius"]), Q(1, 100)
    sigma = Q(1, 2)-r
    rectangles, corridor_passed = [], True
    left, right = 2*sigma, Q(3, 2)
    for j in range(8):
        a, b = left+(right-left)*Q(j, 8), left+(right-left)*Q(j+1, 8)
        z = flint.acb(real((a+b)/2)+flint.arb(0, real((b-a)/2)),
                      real(2*height)+flint.arb(0, real(2*r)))
        value = z.zeta()
        rectangles.append(str(value.real.lower()))
        corridor_passed &= bool(value.real > 0)
    corridor_passed &= bool(real(right).zeta().log() < flint.arb.pi())
    assert corridor_passed
    region = flint.acb(real(Q(1, 2))+flint.arb(0, real(r)), real(height)+flint.arb(0, real(r)))
    degree = 224
    a, b, a_tail, b_tail = affine(region, sigma, coefficients, radius, norm, degree, anchored=True)
    a_lower = a.abs_lower()-a_tail
    c = flint.acb(real(Q(1, 2)), real(height))
    t = flint.acb_series([c, 1], 2).zeta()
    large = flint.acb(real(Q(1, 2))+flint.arb(0, real(large_r)),
                       real(height)+flint.arb(0, real(large_r)))
    ratio = real(r/large_r)
    cauchy = large.zeta().abs_upper()*ratio**2/(1-ratio)
    error = t[0].abs_upper()+cauchy
    linear = t[1].abs_lower()*real(r)
    simple = bool(error < linear)
    return {"independent_branch_rectangle_count": 8, "rectangle_positive_real_lower_balls": rectangles,
            "normalized_branch_connection_recomputed": corridor_passed,
            "local_degree": degree, "different_local_and_Mobius_cutoffs": True,
            "A_modulus_lower_with_infinite_tails_ball": str(a_lower),
            "A_nonzero_on_entire_actual_zero_disk": bool(a_lower > 0),
            "Cauchy_larger_radius": str(large_r), "Cauchy_Rouche_error_upper_ball": str(error),
            "linear_comparison_lower_ball": str(linear),
            "actual_simple_zeta_zero_independently_certified_by_Cauchy": simple,
            "actual_zero_monodromy_lower_ball": str(2*flint.arb.pi()*a_lower),
            "all_passed": corridor_passed and bool(a_lower > 0) and simple}


def main():
    flint.ctx.prec = 256
    formal = json.loads((BASE/"coupling-results/coupling_search.json").read_text())
    source = json.loads((BASE/"coupling-results/coupling_analytic_probe.json").read_text())
    audit = json.loads((BASE/"coupling-results/coupling_verification.json").read_text())
    assert audit["all_passed"]
    coefficients = [Q(x) for x in formal["first_other_prime_local_profile"]["commutator"]]
    local = independent_local(128)
    radius = Q(39, 50)
    correction = sum((abs(local["H"][e]-local["H"][e-1])*radius**e for e in range(1, 129)), Q(0))
    correction += radius**129/(1-radius)
    k_bound = 1/((1-radius)*(1-correction))
    norm = k_bound*(k_bound+1)
    exact_passed = (correction < 1 and coefficients[:129] == local["commutator"]
                    and norm == Q(formal["local_norm_certificate"]["first_other_prime_commutator_weighted_norm_bound"]))
    points = point_checks(source, coefficients, radius, norm)
    zero = zero_control(source, coefficients, radius, norm)
    result = {"exact_bit_partition_coefficients_and_infinite_norm_recomputed": exact_passed,
              "local_degrees_129_through_256_source": "separate independent exact audit, degree 256",
              "actual_zeta_ball_checks": points, "actual_zero_control": zero,
              "all_passed": exact_passed and all(x["all_passed"] for x in points) and zero["all_passed"],
              "proof": "coupling_proof.txt", "shared_trusted_kernel": "FLINT/Arb"}
    (BASE/"coupling-results/coupling_analytic_verification.json").write_text(json.dumps(result, indent=2)+"\n")
    print(f"Independent sector analytic audit: points={sum(x['all_passed'] for x in points)}/{len(points)}, "
          f"Cauchy actual-zero certificate={zero['all_passed']}, all={result['all_passed']}")
    assert result["all_passed"]


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Certify a selected TS-ST interaction against actual zeta values.

This selects indices p^e*q, e>=2, with distinct primes p,q. Its bridge
does not assert continuation of the full commutator. Infinite local,
prime-inversion, and Dirichlet tails remain explicit.
"""

from fractions import Fraction as Q
from pathlib import Path
import json
import math
import time

import flint

from exact_arithmetic import factorization
from global_analytic_probe import ball, error_box, prime_zeta_ball
from projection_analytic_probe import anchored_branch_certificate, prime_zeta_on_anchored_patch


BASE = Path(__file__).resolve().parent


def integer_bound(a):
    a = ball(a)
    assert bool(a > 1)
    return flint.arb(2)**(-a)+flint.arb(2)**(1-a)/(a-1)


def prime_sum(s, sigma):
    # Adapt the finite Mobius sum to the exponent. The bound inside
    # prime_zeta_ball certifies the omitted terms for each actual cutoff.
    terms = max(1, min(48, math.ceil(96/float(sigma))))
    return prime_zeta_ball(s, sigma, terms)


def load_profile():
    source = json.loads((BASE/"coupling-results/coupling_search.json").read_text())
    checked = json.loads((BASE/"coupling-results/coupling_verification.json").read_text())
    assert checked["all_passed"]
    profile = [Q(x) for x in source["first_other_prime_local_profile"]["commutator"]]
    cert = source["local_norm_certificate"]
    r, norm = Q(cert["radius"]), Q(cert["first_other_prime_commutator_weighted_norm_bound"])
    return source, profile, r, norm


def affine_components(s, sigma, d, radius, norm, degree=64, first_prime_sum=None):
    """A=sum d_e P(es), B=sum d_e P((e+1)s), with uniform tails."""
    assert degree < len(d) and Q(sigma)*(degree+1) > 1
    assert bool(flint.arb(2)**(-ball(sigma)) < ball(radius))
    a, b = flint.acb(0), flint.acb(0)
    cache = {}
    for e in range(2, degree+2):
        cache[e] = (first_prime_sum if e == 2 and first_prime_sum is not None
                    else prime_sum(e*s, e*Q(sigma)))
    for e in range(2, degree+1):
        a += ball(d[e])*cache[e]
        b += ball(d[e])*cache[e+1]
    # sum |d_e| r^e<=norm and p^-sigma/r<1 imply these tails,
    # after summing the resulting geometric-free bound over all primes.
    a_tail = ball(norm/radius**(degree+1))*integer_bound((degree+1)*Q(sigma))
    b_tail = ball(norm/radius**(degree+1))*integer_bound((degree+2)*Q(sigma))
    return a, b, a_tail, b_tail


def absolute_norm_at_two(d, radius, norm, degree=32):
    finite = sum((ball(abs(d[e]))*prime_sum(flint.acb(2*e), 2*e).real
                  for e in range(2, degree+1)), flint.arb(0))
    tail = ball(norm/radius**(degree+1))*integer_bound(2*(degree+1))
    # Drop the q!=p restriction to obtain a valid positive majorant.
    return prime_sum(flint.acb(2), 2).real*(finite+tail)


def actual_zeta_checks(d, radius, norm, cutoff=4096, degree=64):
    coefficients = []
    for n in range(2, cutoff+1):
        f = factorization(n)
        repeated = [e for e in f.values() if e >= 2]
        if len(f) == 2 and len(repeated) == 1 and 1 in f.values():
            coefficients.append((n, d[repeated[0]]))
    norm_at_two = absolute_norm_at_two(d, radius, norm)
    records = []
    for sigma, height in ((3, "61.19"), (3, "-67.43"), (4, "139.71"),
                          (4, "-151.23"), (6, "257.89"), (6, "-269.31")):
        s = flint.acb(sigma, height)
        finite = sum((ball(c)*(-s*flint.arb(n).log()).exp() for n, c in coefficients), flint.acb(0))
        a, b, a_tail, b_tail = affine_components(s, sigma, d, radius, norm, degree)
        p = prime_sum(s, sigma)
        reference = a*p-b
        allowed = (flint.arb(cutoff)**(2-sigma)*norm_at_two
                   +a_tail*p.abs_upper()+b_tail)
        error = (finite-reference).abs_upper()
        # Actual coefficient 12 is d_2=1. One incorrect rational coefficient
        # must be rejected despite all three infinite tails.
        corrupted = finite+ball(Q(1, 7))*(-s*flint.arb(12).log()).exp()
        bad = (corrupted-reference).abs_lower()
        records.append({"s": [str(sigma), height], "arithmetic_cutoff": cutoff,
                        "local_degree": degree, "selected_integer_coefficients": len(coefficients),
                        "absolute_Dirichlet_norm_at_sigma_two_upper_ball": str(norm_at_two.upper()),
                        "difference_upper_ball": str(error), "combined_infinite_tail_bound_ball": str(allowed),
                        "within_proved_bound": bool(error < allowed), "perturbed_coefficient_12": "1/7",
                        "perturbed_difference_lower_ball": str(bad), "perturbation_rejected": bool(bad > allowed),
                        "all_passed": bool(error < allowed) and bool(bad > allowed)})
    return records


def actual_zero_control(d, radius, norm):
    height, doubled = "14.13472514173469379046", "28.26945028346938758092"
    centre, zero_radius, sigma = flint.acb("0.5", height), Q(1, 10000), Q(4999, 10000)
    region = flint.acb(flint.arb("0.5 +/- 0.0001"), flint.arb(height+" +/- 0.0001"))
    central = flint.acb_series([centre, 1], 3).zeta()
    ranged = flint.acb_series([region, 1], 3).zeta()
    linear = central[1].abs_lower()*ball(zero_radius)
    error = central[0].abs_upper()+ranged[2].abs_upper()*ball(zero_radius)**2
    simple = bool(error < linear)
    corridor = anchored_branch_certificate(doubled)
    p2 = prime_zeta_on_anchored_patch(2*region, 2*sigma, corridor, terms=64)
    a, b, a_tail, b_tail = affine_components(region, sigma, d, radius, norm, 256, first_prime_sum=p2)
    lower = a.abs_lower()-a_tail
    jump = 2*flint.arb.pi()*lower
    return {"disk_centre": ["1/2", height], "radius": str(zero_radius),
            "actual_zeta_value_at_centre_ball": str(central[0]),
            "actual_zeta_derivative_at_centre_ball": str(central[1]),
            "constant_plus_Taylor_remainder_upper_ball": str(error), "linear_lower_ball": str(linear),
            "one_simple_actual_zeta_zero_certified": simple,
            "P_2s_normalized_branch_corridor": corridor,
            "local_degree": 256, "A_rectangle_ball_before_local_tail": str(a),
            "A_infinite_local_tail_ball": str(a_tail), "B_infinite_local_tail_ball": str(b_tail),
            "A_modulus_lower_after_infinite_tails_ball": str(lower),
            "A_locally_holomorphic_and_nonzero_on_entire_crossing_disk": bool(lower > 0),
            "actual_zero_monodromy_modulus_lower_ball": str(jump),
            "actual_zero_obstruction_certified": bool(jump > 0),
            "all_passed": simple and corridor["all_passed"] and bool(lower > 0),
            "scope": "Selected first-other-prime sector only. The disk crosses the critical line; its zero is compatible with RH."}


def main():
    started = time.monotonic()
    flint.ctx.prec = 256
    source, d, r, norm = load_profile()
    checks = actual_zeta_checks(d, r, norm)
    print(f"Actual zeta comparisons: {sum(x['all_passed'] for x in checks)}/{len(checks)}", flush=True)
    control = actual_zero_control(d, r, norm)
    result = {"definition": "C_1(s)=sum_(p!=q,e>=2) d_e*(p^e*q)^(-s)",
              "d_definition": "d_e=(T S u-S T u)(p^e*q), distinct primes p,q",
              "proved_initial_bridge": "C_1=A*P-B=A*log(zeta)-A*Q-B, Re(s)>1",
              "A_B_Q_holomorphic_domain": "Re(s)>1/2",
              "pole_cancelled_criterion": "RH iff C_1+A*log(s-1) admits single-valued holomorphic continuation to Re(s)>1/2",
              "full_commutator_half_plane_continuation_proved": False,
              "new_RH_estimate_proved": False,
              "generic_prime_relabeling_control": "All exact coefficient laws survive arbitrary relabeling of a free prime monoid",
              "scalar_collapse_control": "This selected sector reduces to A*P-B; it supplies no new bound for log((s-1)*zeta(s))",
              "actual_zeta_ball_checks": checks, "actual_critical_line_zero_control": control,
              "all_passed": all(x["all_passed"] for x in checks) and control["all_passed"],
              "proof": "coupling_proof.txt", "elapsed_seconds": time.monotonic()-started}
    (BASE/"coupling-results/coupling_analytic_probe.json").write_text(json.dumps(result, indent=2)+"\n")
    print(f"Actual-zero sector obstruction: {control['all_passed']}; elapsed={result['elapsed_seconds']:.2f}s")
    assert result["all_passed"]


if __name__ == "__main__":
    main()

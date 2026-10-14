#!/usr/bin/env python3
"""Verify the learned diagonal projection on actual zeta, including a zero.

The arithmetic route uses the searched mask, certified independently by
integer multinomial parity. The analytic route uses Arb zeta values and
Möbius inversion. Explicit infinite tails are retained in every comparison.
"""

from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import json

import flint
import mpmath as mp
import numpy as np

from global_analytic_probe import ball, error_box, mobius, prime_zeta_ball


BASE = Path(__file__).resolve().parent


def integer_sum_bound(exponent):
    exponent = ball(exponent)
    if not bool(exponent > 1):
        raise ValueError("The tail requires an exponent greater than one")
    return flint.arb(2)**(-exponent)+flint.arb(2)**(1-exponent)/(exponent-1)


def layer_tail(sigma, layers):
    """Bound sum_{j>layers} P(2^j*s) for 2^(layers+1)*sigma>1."""
    return (integer_sum_bound(Q(sigma)*2**(layers+1))
            /(1-flint.arb(2)**(-ball(sigma))))


def binary_product(s, sigma, layers=8, first_prime_zeta=None):
    c = flint.acb(1)
    for j in range(1, layers+1):
        p = (first_prime_zeta if j == 1 and first_prime_zeta is not None
             else prime_zeta_ball(2**j*s, Q(sigma)*2**j))
        c *= 1+p
    # Multiplying the omitted factors changes the product by at most
    # exp(sum |P|)-1; this also works on the certified patch below sigma=1/2.
    error = c.abs_upper()*layer_tail(sigma, layers).expm1()
    return c, error


def affine_q(s, sigma, terms=64):
    q = sum((prime_zeta_ball(k*s, Q(sigma)*k)/k for k in range(2, terms+1)),
            flint.acb(0))
    tail = (integer_sum_bound(Q(sigma)*(terms+1))
            /((terms+1)*(1-flint.arb(2)**(-ball(sigma)))))
    return q, tail


def actual_zeta_checks(cutoff=512, layers=8, q_terms=64):
    search = json.loads((BASE/"projection-results/projection_search.json").read_text())
    independent = json.loads((BASE/"projection-results/projection_verification.json").read_text())
    assert independent["all_passed"]
    coefficients = search["search"]["learned_mask_values"]
    records = []
    for sigma, height in ((3, "13.67"), (3, "53.81"), (4, "127.43"),
                          (4, "-117.59"), (6, "241.07"), (6, "-223.13")):
        s = flint.acb(sigma, height)
        finite = sum((coefficients[n]*(-s*flint.arb(n).log()).exp()
                      for n in range(1, cutoff+1)), flint.acb(0))
        p = prime_zeta_ball(s, sigma)
        c, c_error = binary_product(s, sigma, layers)
        q, q_error = affine_q(s, sigma, q_terms)
        log_zeta = s.zeta().log()
        product_value = (1+p)*c
        affine_value = c*(log_zeta+1-q)
        product_error = (1+p).abs_upper()*c_error
        affine_error = (c.abs_upper()*q_error
                        +c_error*((log_zeta+1-q).abs_upper()+q_error))
        series_tail = ball(cutoff)**(1-sigma)/(sigma-1)
        corrupted = finite+ball(Q(1, 7))*(-s*flint.arb(6).log()).exp()
        checks = []
        for name, reference, analytic_tail in (("binary_layer_product", product_value, product_error),
                                               ("affine_zeta_log", affine_value, affine_error)):
            allowed = series_tail+analytic_tail
            error = (finite-reference).abs_upper()
            bad_lower = (corrupted-reference).abs_lower()
            checks.append({"representation": name, "difference_upper_ball": str(error),
                           "proved_combined_tail_bound_ball": str(allowed),
                           "within_proved_bound": bool(error < allowed),
                           "perturbed_difference_lower_ball": str(bad_lower),
                           "perturbation_rejected": bool(bad_lower > allowed)})
        records.append({"s": [str(sigma), height], "arithmetic_cutoff": cutoff,
                        "binary_layers_in_C": layers, "Q_terms": q_terms,
                        "coefficient_route": "learned diagonal mask, independently verified as integer multinomial parity",
                        "coefficient_6_perturbation": "1/7", "comparisons": checks,
                        "all_passed": all(x["within_proved_bound"] and x["perturbation_rejected"] for x in checks)})
    return records


def anchored_branch_certificate(height):
    """Connect 2s near the critical-line zero to Re(2s)=3/2.

    Each Arb image stays in Re(zeta)>0. Thus the principal logarithm on
    the whole patch is connected to the normalized Euler branch at the
    right edge. This avoids assuming a principal branch at Re(2s) near 1.
    """
    left, right = Q(4999, 5000), Q(3, 2)
    imaginary = flint.arb(height+" +/- 0.0002")
    records = []
    for k in range(10):
        a = left+(right-left)*Q(k, 10)
        b = left+(right-left)*Q(k+1, 10)
        centre, radius = (a+b)/2, (b-a)/2
        region = flint.acb(ball(centre)+flint.arb(0, ball(radius)), imaginary)
        value = region.zeta()
        records.append({"real_interval": [str(a), str(b)],
                        "imaginary_centre": height, "imaginary_radius": "1/5000",
                        "zeta_rectangle_ball": str(value),
                        "zeta_real_part_lower_ball": str(value.real.lower()),
                        "positive_real_part_certified": bool(value.real > 0)})
    anchor_bound = ball(right).zeta().log()
    anchor_passed = bool(anchor_bound < flint.arb.pi())
    return {"rectangles": records, "anchor_real_part": str(right),
            "anchor_normalized_log_modulus_bound_ball": str(anchor_bound),
            "anchor_principal_log_equals_normalized_Euler_log_proved": anchor_passed,
            "all_passed": anchor_passed and all(x["positive_real_part_certified"] for x in records)}


def prime_zeta_on_anchored_patch(z, sigma, branch_certificate, terms=64):
    """Local continuation of P(z) with an explicitly connected log branch."""
    assert branch_certificate["all_passed"]
    sigma = Q(sigma)
    assert terms >= 1 and (terms+1)*sigma > 1
    result = z.zeta().log()  # m=1: branch fixed by the certified corridor.
    for m in range(2, terms+1):
        mu = mobius(m)
        if mu:
            assert bool(ball(m*sigma).zeta().log() < flint.arb.pi())
            result += mu*(m*z).zeta().log()/m
    a, sig, two = terms+1, ball(sigma), flint.arb(2)
    tail = ((1+2/(a*sig-1))*two**(-a*sig)
            /(a*(1-two**(-a*sig))*(1-two**(-sig))))
    return result+error_box(tail)


def actual_zero_control():
    """The logarithmic criterion must detect an actual simple zeta zero."""
    height, double_height = "14.13472514173469379046", "28.26945028346938758092"
    centre = flint.acb("0.5", height)
    radius, sigma = Q(1, 10000), Q(4999, 10000)
    region = flint.acb(flint.arb("0.5 +/- 0.0001"), flint.arb(height+" +/- 0.0001"))
    point_taylor = flint.acb_series([centre, 1], 3).zeta()
    region_taylor = flint.acb_series([region, 1], 3).zeta()
    linear_lower = point_taylor[1].abs_lower()*ball(radius)
    remainder_upper = point_taylor[0].abs_upper()+region_taylor[2].abs_upper()*ball(radius)**2
    simple_zero = bool(remainder_upper < linear_lower)
    branch = anchored_branch_certificate(double_height)
    p2 = prime_zeta_on_anchored_patch(2*region, 2*sigma, branch)
    c, c_error = binary_product(region, sigma, 8, first_prime_zeta=p2)
    c_lower = c.abs_lower()-c_error
    c_nonzero = bool(c_lower > 0)
    # C is now certified holomorphic/nonzero on the entire disk, although
    # its general guaranteed domain is only Re(s)>1/2.
    mp.mp.dps = 80
    phases = []
    numerical_centre = mp.mpc("0.5", height)
    for j in range(129):
        s = numerical_centre+mp.mpf("0.0001")*mp.exp(2j*mp.pi*mp.mpf(j)/128)
        phases.append(float(mp.arg((s-1)*mp.zeta(s))))
    unwrapped = np.unwrap(np.asarray(phases))
    winding = int(round((unwrapped[-1]-unwrapped[0])/(2*np.pi)))
    monodromy_lower = 2*flint.arb.pi()*c_lower
    return {"disk_centre": ["1/2", height], "radius": str(radius),
            "actual_zeta_value_at_centre_ball": str(point_taylor[0]),
            "actual_zeta_derivative_at_centre_ball": str(point_taylor[1]),
            "actual_zeta_second_derivative_over_two_on_rectangle_ball": str(region_taylor[2]),
            "linear_comparison_modulus_lower_on_circle_ball": str(linear_lower),
            "proved_constant_plus_Taylor_remainder_upper_ball": str(remainder_upper),
            "exactly_one_simple_actual_zeta_zero_in_disk_certified": simple_zero,
            "critical_line_location_basis": "Reflection s->1-conjugate(s) preserves the disk; uniqueness forces its zero onto Re(s)=1/2",
            "P_2s_principal_branch_connection": branch,
            "C_rectangle_ball_before_layer_tail": str(c), "C_omitted_layer_error_ball": str(c_error),
            "C_modulus_lower_after_infinite_tail_ball": str(c_lower),
            "C_locally_continues_holomorphically_and_nonzero_on_entire_disk_certified": c_nonzero,
            "criterion_actual_zero_monodromy": "2*pi*i*C(basepoint)",
            "criterion_monodromy_modulus_lower_ball": str(monodromy_lower),
            "criterion_actual_zero_obstruction_certified": bool(monodromy_lower > 0),
            "sampled_actual_Z_winding": winding, "phase_samples_radians": phases,
            "sampling_is_diagnostic": True,
            "all_passed": simple_zero and branch["all_passed"] and c_nonzero and winding == 1,
            "scope": "The circle crosses Re(s)=1/2; detection is compatible with RH and does not settle off-line zeros",
            "proof": "projection_proof.txt sections 7 through 9"}


def own_zero_control():
    """Prove that the projection creates a zero where actual zeta is nonzero.

    The centre was found by a diagnostic height scan and Newton iteration.
    The zero count here uses a fresh Arb/Taylor/Rouche certificate with
    the infinite Mobius tail, not the numerical residual or phase mesh.
    """
    real, height = "1.153396876020314", "14.016611700317199"
    radius, terms = Q(1, 1000000), 64
    sigma = Q(real)-radius
    centre = flint.acb(real, height)
    region = flint.acb(flint.arb(real+" +/- 0.000001"),
                       flint.arb(height+" +/- 0.000001"))
    branch_bound = ball(sigma).zeta().log()
    branch_proved = bool(branch_bound < flint.arb.pi())
    assert branch_proved and sigma > 1

    def finite_taylor(z):
        result = flint.acb_series([1], 3)
        variable = flint.acb_series([z, 1], 3)
        for m in range(1, terms+1):
            mu = mobius(m)
            if mu:
                result += mu*(m*variable).zeta().log()/m
        return result

    point, rectangle = finite_taylor(centre), finite_taylor(region)
    a, sig, two = terms+1, ball(sigma), flint.arb(2)
    tail = ((1+2/(a*sig-1))*two**(-a*sig)
            /(a*(1-two**(-a*sig))*(1-two**(-sig))))
    linear_lower = point[1].abs_lower()*ball(radius)
    remainder_upper = point[0].abs_upper()+rectangle[2].abs_upper()*ball(radius)**2+tail
    one_zero = bool(remainder_upper < linear_lower)
    zeta_region = region.zeta()
    zeta_zero_free = bool(zeta_region.abs_lower() > 0)
    c, c_error = binary_product(region, sigma)
    c_lower = c.abs_lower()-c_error
    c_nonzero = bool(c_lower > 0)
    return {"disk_centre": [real, height], "radius": str(radius),
            "initial_diagnostic_source": "own_zero_scout.json and own_zero_newton_diagnostics.json",
            "certified_function": "1+P(s), with F_chi(s)=C(s)*(1+P(s))",
            "finite_mobius_terms": terms,
            "normalized_log_modulus_bound_ball": str(branch_bound),
            "all_principal_log_branches_certified": branch_proved,
            "finite_function_value_at_centre_ball": str(point[0]),
            "finite_derivative_at_centre_ball": str(point[1]),
            "finite_second_derivative_over_two_on_rectangle_ball": str(rectangle[2]),
            "infinite_mobius_tail_bound_ball": str(tail),
            "linear_comparison_modulus_lower_on_circle_ball": str(linear_lower),
            "proved_constant_Taylor_and_infinite_tail_upper_ball": str(remainder_upper),
            "exactly_one_simple_zero_of_1_plus_prime_zeta_certified": one_zero,
            "actual_zeta_rectangle_ball": str(zeta_region),
            "actual_zeta_modulus_lower_on_rectangle_ball": str(zeta_region.abs_lower()),
            "actual_zeta_nonzero_on_entire_disk_certified": zeta_zero_free,
            "C_modulus_lower_after_infinite_layer_tail_ball": str(c_lower),
            "C_nonzero_on_entire_disk_certified": c_nonzero,
            "exactly_one_simple_transformed_F_chi_zero_in_zeta_zero_free_disk_certified": one_zero and c_nonzero and zeta_zero_free,
            "automatic_zero_preservation_rejected": one_zero and c_nonzero and zeta_zero_free,
            "all_passed": branch_proved and one_zero and c_nonzero and zeta_zero_free,
            "scope": "A zero created by the arithmetic projection in Re(s)>1; it is not a zeta zero or an RH counterexample",
            "proof": "projection_proof.txt section 11"}


def main():
    flint.ctx.prec = 350
    checks = actual_zeta_checks()
    control = actual_zero_control()
    own_zero = own_zero_control()
    result = {"representation": "F_chi=(1+P(s))*C(s)=C(s)*log(zeta(s))+C(s)*(1-Q(s))",
              "C": "product_{j>=1}(1+P(2^j*s))", "Q": "sum_{k>=2}P(k*s)/k",
              "actual_zeta_ball_checks": checks, "actual_critical_line_zero_control": control,
              "own_zero_in_zeta_zero_free_region_control": own_zero,
              "all_passed": all(x["all_passed"] for x in checks) and control["all_passed"] and own_zero["all_passed"],
              "proof": "projection_proof.txt", "historical_novelty_is_not_certified": True}
    output = BASE/"projection-results/projection_analytic_probe.json"
    output.write_text(json.dumps(result, indent=2)+"\n")
    print(f"Projection actual-zeta points: {sum(x['all_passed'] for x in checks)}/6; "
          f"two independent analytic representations per point; actual-zero criterion passed={control['all_passed']}; "
          f"created zero in zeta-zero-free disk certified={own_zero['all_passed']}")
    assert result["all_passed"]


if __name__ == "__main__":
    main()

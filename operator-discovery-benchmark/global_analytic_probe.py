#!/usr/bin/env python3
"""Certify the cross-prime transfer's affine zeta-log representation.

Graded no-carry series, independently evaluated actual zeta values, and
explicit Banach-algebra tails establish the numerical comparisons. A
controlled extra zero challenges the resulting RH holomorphy criterion.
"""

from __future__ import annotations

from fractions import Fraction as Q
import json
from pathlib import Path

import flint
import mpmath as mp
import numpy as np

from exact_arithmetic import factorization, sequence
from global_carry_probe import global_transfer


def ball(value):
    value = Q(value)
    return flint.arb(value.numerator) / value.denominator


def error_box(radius):
    return flint.acb(flint.arb(0, radius), flint.arb(0, radius))


def mobius(n):
    exponents = list(factorization(n).values())
    return 0 if any(e > 1 for e in exponents) else (-1)**len(exponents)


def prime_zeta_ball(z, sigma, terms=32):
    """Möbius inversion of the absolutely convergent Euler logarithm.

    The tested domain has log(zeta(sigma))<pi, so Arb's principal complex
    logarithm equals the analytic branch normalized at +infinity.
    """
    sigma = ball(sigma)
    if not bool(sigma > 1) or not bool(sigma.zeta().log() < flint.arb.pi()):
        raise ValueError("The numerical branch/domain certificate failed")
    result = flint.acb(0)
    for m in range(1, terms + 1):
        mu = mobius(m)
        if mu:
            result += mu * (m*z).zeta().log() / m
    a = terms + 1
    tail = ((1 + 2/(a*sigma-1)) * flint.arb(2)**(-a*sigma)
            / (a*(1-flint.arb(2)**(-a*sigma))*(1-flint.arb(2)**(-sigma))))
    return result + error_box(tail)


def graded_product(left, right):
    result = [flint.acb(0) for _ in left]
    for n in range(len(left)):
        for i in range(n + 1):
            if not i & (n-i):
                result[n] += left[i] * right[n-i]
    return result


def graded_exp(values):
    result = [flint.acb(1)] + [flint.acb(0) for _ in values[1:]]
    term = list(result)
    for k in range(1, max(n.bit_count() for n in range(len(values))) + 1):
        term = [x/k for x in graded_product(term, values)]
        result = [x+y for x,y in zip(result, term)]
    return result


def affine_components(s, sigma, degree=64):
    sigma = Q(sigma)
    k = [flint.acb(0), flint.acb(0)]
    for exponent in range(2, degree + 1):
        k.append(prime_zeta_ball(exponent*s, exponent*sigma) / exponent)
    exponential = graded_exp(k)
    a = sum(exponential[::2], flint.acb(0))
    d = sum(exponential[1::2], flint.acb(0))
    q = sum(k, flint.acb(0))
    b = a * (1-q) + d
    sig = ball(sigma)
    two = flint.arb(2)
    rho = two ** (sig/2)
    c = (rho*rho/(2*(1-rho*two**(-sig)))
         * (two**(-2*sig)+two**(1-2*sig)/(2*sig-1)))
    exp_tail = c.exp() * rho**(-degree-1)
    t = degree + 1
    k_tail = (1+2/(t*sig-1))*two**(-t*sig)/(t*(1-two**(-sig)))
    return {"A_head": a, "D_head": d, "Q_head": q, "B_head": b,
            "weighted_K_norm_bound": c, "exp_grade_tail": exp_tail,
            "K_grade_tail": k_tail}


def actual_zeta_checks():
    cutoff, degree = 512, 64
    coefficients = global_transfer(sequence([1] * cutoff))
    records = []
    for sigma, height in ((3, "0"), (3, "43.79"), (4, "101.37"),
                          (4, "-89.13"), (6, "217.09"), (6, "-197.31")):
        s = flint.acb(sigma, height)
        components = affine_components(s, sigma, degree)
        log_zeta = s.zeta().log()
        reference = components["A_head"]*log_zeta + components["B_head"]
        finite = flint.acb(0)
        for n in range(1, cutoff + 1):
            finite += ball(coefficients[n]) * (-s*flint.arb(n).log()).exp()
        representation_error = (components["exp_grade_tail"]
                                * (2 + log_zeta.abs_upper() + components["weighted_K_norm_bound"])
                                + components["A_head"].abs_upper()*components["K_grade_tail"])
        series_tail = flint.arb(cutoff)**(1-sigma)/(sigma-1)
        allowed = series_tail + representation_error
        error = (finite-reference).abs_upper()
        perturbed = finite + ball(Q(1,7)) * (-s*flint.arb(6).log()).exp()
        rejected = bool((perturbed-reference).abs_lower() > allowed)
        records.append({"s": [str(sigma), height], "arithmetic_cutoff": cutoff,
                        "graded_cutoff": degree, "difference_upper_ball": str(error),
                        "proved_combined_tail_bound_ball": str(allowed),
                        "within_proved_bound": bool(error < allowed),
                        "coefficient_6_perturbation": "1/7", "perturbation_rejected": rejected})
    return records


def zero_sensitivity_control():
    # The rectangle includes the whole test disk and excludes s=1. Arb
    # certifies that the ACTUAL zeta has no zero there, independently of RH.
    region = flint.acb(flint.arb("0.75 +/- 0.01"), flint.arb("1 +/- 0.01"))
    zeta_region = region.zeta()
    region_passed = bool(zeta_region.abs_lower() > 0)
    base = flint.acb("0.755", "1")
    components = affine_components(base, Q(151,200), degree=128)
    a_lower = components["A_head"].abs_lower() - components["exp_grade_tail"]
    coefficient_nonzero = bool(a_lower > 0)
    # This challenges the PROVED logarithmic extension criterion, keeping
    # its zeta-specific A,B. It is not a claim that the operator formula
    # for a different input is obtained by replacing zeta with any function.
    mp.mp.dps = 80
    centre, radius = mp.mpc("0.75", "1"), mp.mpf("0.005")
    actual, extra_zero = [], []
    for j in range(129):
        s = centre + radius * mp.exp(2j*mp.pi*mp.mpf(j)/128)
        z = (s-1)*mp.zeta(s)
        actual.append(float(mp.arg(z)))
        extra_zero.append(float(mp.arg((s-centre)*z)))
    winds = [int(round((np.unwrap(np.array(phase))[-1]-phase[0])/(2*np.pi)))
             for phase in (actual, extra_zero)]
    return {"disk_centre": ["0.75", "1"], "radius": "1/200",
            "actual_zeta_on_enclosing_rectangle_ball": str(zeta_region),
            "actual_zeta_modulus_lower_on_rectangle_ball": str(zeta_region.abs_lower()),
            "actual_zeta_rectangle_component_endpoints": {
                "real": [str(zeta_region.real.lower()), str(zeta_region.real.upper())],
                "imaginary": [str(zeta_region.imag.lower()), str(zeta_region.imag.upper())]},
            "actual_zeta_nonzero_on_whole_rectangle_certified": region_passed,
            "actual_Z_definition": "Z(s)=(s-1)*zeta(s)",
            "extra_zero_model_definition": "(s-(3/4+i))*Z(s)",
            "expected_winding_numbers": [0,1], "sampled_winding_numbers": winds,
            "phase_samples_radians": {"actual_Z": actual, "extra_zero_model": extra_zero},
            "sampling_is_diagnostic": True,
            "winding_basis": "Actual Z nonzero on disk by the Arb enclosure; the test factor has exactly one simple zero",
            "A_at_basepoint_modulus_lower_ball_after_tail": str(a_lower),
            "A_at_basepoint_certified_nonzero": coefficient_nonzero,
            "actual_criterion_log_monodromy": "0",
            "extra_zero_criterion_log_monodromy": "2*pi*i*A(basepoint), certified nonzero",
            "all_passed": region_passed and coefficient_nonzero and winds == [0,1],
            "scope": "Control for the derived holomorphy criterion; no conclusion about off-line zeros elsewhere"}


def main():
    flint.ctx.prec = 350
    checks = actual_zeta_checks()
    control = zero_sensitivity_control()
    result = {"representation": "F(s)=A(s)*log(zeta(s))+B(s)",
              "actual_zeta_ball_checks": checks, "zero_sensitivity_control": control,
              "all_passed": all(x["within_proved_bound"] and x["perturbation_rejected"] for x in checks) and control["all_passed"],
              "proof": "global_carry_proof.txt sections 4 through 7",
              "historical_novelty_is_not_certified": True}
    output = Path(__file__).resolve().parent / "global-results" / "global_analytic_probe.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Cross-prime zeta bridge: {sum(x['within_proved_bound'] for x in checks)}/6; perturbations rejected: {sum(x['perturbation_rejected'] for x in checks)}/6; zero sensitivity passed={control['all_passed']}")
    assert result["all_passed"]


if __name__ == "__main__":
    main()

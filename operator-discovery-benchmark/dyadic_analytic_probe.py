#!/usr/bin/env python3
"""Fresh Arb checks of fractional transfers and a multiplicity control.

The added-zero models challenge the proved continuation criterion. They
are not asserted to be arithmetic transfers of modified zeta inputs.
"""

from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import json

import flint
import mpmath as mp
import numpy as np

from check_dyadic_roots import (evaluate, independent_corrections,
                               independent_local_polynomial)
from dyadic_root_search import direct_parameter_transfer
from exact_arithmetic import factorization, integer_power, sequence


def ball(value):
    value = Q(value)
    return flint.arb(value.numerator)/value.denominator


def actual_zeta_checks(cutoff=512, prime_cutoff=257, local_degree=48):
    local_polynomials = [independent_local_polynomial(e) for e in range(local_degree+1)]
    corrections = independent_corrections(local_polynomials, local_degree)
    primes = [p for p in range(2, prime_cutoff+1) if factorization(p) == {p: 1}]
    records, coefficient_checks = [], []
    for beta in (Q(1, 2), Q(1, 4), Q(1, 8)):
        direct = direct_parameter_transfer(sequence([1]*cutoff), beta)
        local = [evaluate(poly, beta) for poly in local_polynomials]
        predicted = [Q(0), Q(1)]
        for n in range(2, cutoff+1):
            coefficient = Q(1)
            for exponent in factorization(n).values():
                coefficient *= local[exponent]
            predicted.append(coefficient)
        agree = direct == predicted
        coefficient_checks.append({"beta": str(beta), "integer_cutoff": cutoff,
                                   "generic_and_independent_coefficients_agree": agree})
        assert agree
        correction = [evaluate(poly, beta) for poly in corrections]
        for sigma, height in ((3, "0"), (3, "47.23"), (4, "113.41"), (6, "-103.27")):
            s = flint.acb(sigma, height)
            finite = sum((ball(direct[n])*(-s*flint.arb(n).log()).exp()
                          for n in range(1, cutoff+1)), flint.acb(0))
            product = flint.acb(1)
            for prime in primes:
                x = (-s*flint.arb(prime).log()).exp()
                factor = flint.acb(0)
                for coefficient in reversed(correction):
                    factor = factor*x+ball(coefficient)
                product *= factor
            zeta = s.zeta()
            normalized_log_upper = flint.arb(sigma).zeta().log()
            branch_proved = bool(normalized_log_upper < flint.arb.pi())
            assert branch_proved
            root = (ball(beta)*zeta.log()).exp()
            two = flint.arb(2)
            series_tail = flint.arb(cutoff)**(1-sigma)/(sigma-1)
            multiplier = 2/(1-two**(-sigma))
            exponent = 2*sigma
            majorant = (multiplier*(two**(-exponent)
                                    + two**(1-exponent)/(exponent-1))).exp()
            prime_tail = multiplier*flint.arb(prime_cutoff)**(1-exponent)/(exponent-1)
            local_exponent = sigma*(local_degree+1)
            local_tail = multiplier*(two**(-local_exponent)
                                      + two**(1-local_exponent)/(local_exponent-1))
            euler_error = majorant*(prime_tail.expm1()+local_tail)
            allowed = series_tail+root.abs_upper()*euler_error
            error = (finite-root*product).abs_upper()
            corrupted = finite+ball(Q(1, 7))*(-s*flint.arb(4).log()).exp()
            control_lower = (corrupted-root*product).abs_lower()
            records.append({"beta": str(beta), "s": [str(sigma), height],
                            "coefficient_cutoff": cutoff, "prime_cutoff": prime_cutoff,
                            "local_degree": local_degree,
                            "normalized_log_modulus_bound_ball": str(normalized_log_upper),
                            "principal_branch_equals_normalized_branch_proved": branch_proved,
                            "difference_upper_ball": str(error),
                            "proved_combined_tail_bound_ball": str(allowed),
                            "within_proved_bound": bool(error < allowed),
                            "coefficient_4_perturbation": "1/7",
                            "perturbed_difference_lower_ball": str(control_lower),
                            "perturbation_rejected": bool(control_lower > allowed)})
    return coefficient_checks, records


def multiplicity_control():
    region = flint.acb(flint.arb("0.75 +/- 0.01"), flint.arb("1 +/- 0.01"))
    enclosure = region.zeta()
    zero_free = bool(enclosure.abs_lower() > 0)
    source = json.loads((Path(__file__).resolve().parent/
                         "dyadic-results/dyadic_root_search.json").read_text())
    cert = source["uniform_real_parameter_certificate"]
    correction_nonzero = (Q(cert["total_bound"]) < 1 and Q(cert["radius"])**2 > Q(1, 2))
    mp.mp.dps = 80
    centre, radius = mp.mpc("0.75", "1"), mp.mpf("0.005")
    phase = {m: [] for m in (0, 1, 2, 4, 8)}
    for j in range(129):
        s = centre+radius*mp.exp(2j*mp.pi*mp.mpf(j)/128)
        z = (s-1)*mp.zeta(s)
        for m in phase:
            phase[m].append(float(mp.arg(z*(s-centre)**m)))
    records = []
    winding = {}
    for m, values in phase.items():
        unwrapped = np.unwrap(np.asarray(values))
        change = unwrapped[-1]-unwrapped[0]
        winding[m] = int(round(change/(2*np.pi)))
        for k in range(1, 5):
            order = 2**k
            beta = Q(1, order)
            diagnostic_jump = float(abs(np.exp(1j*float(beta)*change)-1))
            detected = diagnostic_jump > 1e-9
            exact_obstruction = m % order != 0
            if exact_obstruction:
                jump = flint.acb(0, 2*flint.arb.pi()*ball(Q(m, order))).exp()-1
                jump_lower = jump.abs_lower()
                jump_certified = bool(jump_lower > 0)
            else:
                jump_lower = flint.arb(0)
                jump_certified = True  # exp(2*pi*i*integer)=1 exactly.
            records.append({"added_zero_multiplicity": m, "extraction_iterations": k,
                            "root_order": order, "beta": str(beta),
                            "multiplicity_divisible_by_root_order": m % order == 0,
                            "root_monodromy_obstruction_proved": exact_obstruction,
                            "sampled_endpoint_jump_factor_modulus": diagnostic_jump,
                            "root_of_unity_jump_lower_ball": str(jump_lower),
                            "exact_jump_decision_certified": jump_certified,
                            "diagnostic_matches_proved_obstruction": detected == exact_obstruction})
    passed = (zero_free and correction_nonzero and all(winding[m] == m for m in winding)
              and all(x["exact_jump_decision_certified"]
                      and x["diagnostic_matches_proved_obstruction"] for x in records))
    return {"disk_centre": ["3/4", "1"], "radius": "1/200",
            "actual_Z": "(s-1)*zeta(s)",
            "model": "(s-(3/4+i))^m*actual_Z(s), m=0,1,2,4,8",
            "actual_zeta_enclosing_rectangle_ball": str(enclosure),
            "actual_zeta_modulus_lower_ball": str(enclosure.abs_lower()),
            "actual_Z_nonzero_on_entire_disk_certified": zero_free,
            "all_beta_corrections_nonzero_on_Re_s_gt_half_proved": correction_nonzero,
            "sampled_winding_numbers": winding,
            "phase_samples_radians": phase, "sampling_is_diagnostic": True,
            "records": records, "all_passed": passed,
            "scope": "Multiplicity control for the proved root-continuation criterion; no claim about actual off-line zeros outside the disk or transfer of the artificial models"}


def actual_zero_control():
    """Rouche isolates one actual simple zero; no RH assumption is used."""
    height = "14.13472514173469379046"
    centre = flint.acb("0.5", height)
    radius = Q(1, 10000)
    region = flint.acb(flint.arb("0.5 +/- 0.0001"),
                       flint.arb(height+" +/- 0.0001"))
    point_taylor = flint.acb_series([centre, 1], 3).zeta()
    region_taylor = flint.acb_series([region, 1], 3).zeta()
    linear_lower = point_taylor[1].abs_lower()*ball(radius)
    remainder_upper = point_taylor[0].abs_upper()+region_taylor[2].abs_upper()*ball(radius)**2
    one_simple_zero = bool(remainder_upper < linear_lower)
    double_zeta_enclosure = (2*region).zeta()
    double_zeta_nonzero = bool(double_zeta_enclosure.abs_lower() > 0)
    minimum_sigma = Q(4999, 10000)
    local_disk_condition = bool(flint.arb(2)**(-ball(minimum_sigma)) < ball(Q(71, 100)))
    evidence_dir = Path(__file__).resolve().parent/"dyadic-results"
    source = json.loads((evidence_dir/"dyadic_root_search.json").read_text())
    verification = json.loads((evidence_dir/"dyadic_root_verification.json").read_text())
    local_nonzero_witness = (verification["all_passed"]
                             and Q(source["uniform_real_parameter_certificate"]["total_bound"]) < 1)
    # Section 8 of the proof factors the quadratic correction through
    # zeta(2s)^(-beta^2/2); the remaining product converges for sigma>1/3.
    correction_extends_nonzero = double_zeta_nonzero and local_disk_condition and local_nonzero_witness
    mp.mp.dps = 80
    numerical_centre = mp.mpc("0.5", height)
    phases = []
    for j in range(129):
        s = numerical_centre+mp.mpf("0.0001")*mp.exp(2j*mp.pi*mp.mpf(j)/128)
        phases.append(float(mp.arg((s-1)*mp.zeta(s))))
    unwrapped = np.unwrap(np.asarray(phases))
    change = unwrapped[-1]-unwrapped[0]
    winding = int(round(change/(2*np.pi)))
    records = []
    for k in range(1, 5):
        order = 2**k
        jump = flint.acb(0, 2*flint.arb.pi()/order).exp()-1
        diagnostic = float(abs(np.exp(1j*change/order)-1))
        records.append({"root_order": order, "actual_root_jump_lower_ball": str(jump.abs_lower()),
                        "actual_branch_obstruction_certified": bool(jump.abs_lower() > 0),
                        "sampled_endpoint_jump_factor_modulus": diagnostic,
                        "diagnostic_obstruction_detected": diagnostic > 1e-9})
    # These controls are actual transfers of known arithmetic inputs,
    # unlike the explicitly scoped added-zero models: the input series is
    # actual zeta^m, and T_beta(u^{*m})=T_(m beta)(u).
    u = sequence([1]*128)
    powers = {m: integer_power(u, m) for m in (1, 2, 4, 8)}
    transferred_u = {}
    power_cases = []
    for m, arithmetic_input in powers.items():
        wrapped = np.angle(np.exp(1j*m*unwrapped))
        power_unwrapped = np.unwrap(wrapped)
        power_change = power_unwrapped[-1]-power_unwrapped[0]
        for order in (2, 4, 8, 16):
            if m > order:
                continue  # The correction certificate covers m/order<=1.
            effective_beta = Q(m, order)
            if effective_beta not in transferred_u:
                transferred_u[effective_beta] = direct_parameter_transfer(u, effective_beta)
            direct = direct_parameter_transfer(arithmetic_input, Q(1, order))
            arithmetic_agreement = direct == transferred_u[effective_beta]
            obstructed = m % order != 0
            numerical_jump = float(abs(np.exp(1j*power_change/order)-1))
            if obstructed:
                power_jump = flint.acb(0, 2*flint.arb.pi()*ball(effective_beta)).exp()-1
                jump_proved = bool(power_jump.abs_lower() > 0)
            else:
                jump_proved = True  # Exact integer exponent, hence no jump.
            power_cases.append({"arithmetic_input": f"u^{{*{m}}}", "actual_input_series": f"zeta(s)^{m}",
                                "actual_zero_multiplicity": m, "root_order": order,
                                "effective_beta": str(effective_beta),
                                "generic_transfer_parameter_composition_agrees_through_128": arithmetic_agreement,
                                "root_monodromy_obstruction_proved": obstructed,
                                "root_of_unity_decision_certified": jump_proved,
                                "sampled_endpoint_jump_factor_modulus": numerical_jump,
                                "diagnostic_matches_proved_obstruction": (numerical_jump > 1e-9) == obstructed,
                                "sampled_actual_Z_power_winding": int(round(power_change/(2*np.pi)))})
    passed = (one_simple_zero and correction_extends_nonzero and winding == 1
              and all(x["actual_branch_obstruction_certified"] and x["diagnostic_obstruction_detected"]
                      for x in records)
              and all(x["generic_transfer_parameter_composition_agrees_through_128"]
                      and x["root_of_unity_decision_certified"]
                      and x["diagnostic_matches_proved_obstruction"]
                      and x["sampled_actual_Z_power_winding"] == x["actual_zero_multiplicity"]
                      for x in power_cases))
    return {"disk_centre": ["1/2", height], "radius": str(radius),
            "actual_zeta_value_at_centre_ball": str(point_taylor[0]),
            "actual_zeta_derivative_at_centre_ball": str(point_taylor[1]),
            "actual_zeta_second_derivative_over_two_on_rectangle_ball": str(region_taylor[2]),
            "linear_comparison_modulus_lower_on_circle_ball": str(linear_lower),
            "proved_constant_plus_Taylor_remainder_upper_ball": str(remainder_upper),
            "exactly_one_simple_actual_zeta_zero_in_disk_certified": one_simple_zero,
            "critical_line_location_basis": "The disk is invariant under s->1-conjugate(s); functional reflection and its unique simple zero force Re(rho)=1/2",
            "actual_zeta_2s_on_rectangle_ball": str(double_zeta_enclosure),
            "actual_zeta_2s_nonzero_certified": double_zeta_nonzero,
            "correction_local_radius_condition_certified": local_disk_condition,
            "independent_uniform_correction_certificate_passed": local_nonzero_witness,
            "all_real_beta_corrections_extend_nonzero_to_disk_proved": correction_extends_nonzero,
            "sampled_actual_Z_winding": winding, "phase_samples_radians": phases,
            "sampling_is_diagnostic": True, "root_orders": records,
            "actual_zeta_power_arithmetic_controls": power_cases, "all_passed": passed,
            "scope": "An actual critical-line zero tests the root diagnostic. The circle crosses Re(s)=1/2, so the observed branching is compatible with RH and says nothing about off-line zeros elsewhere",
            "proof": "dyadic_root_proof.txt section 8"}


def main():
    flint.ctx.prec = 350
    coefficients, checks = actual_zeta_checks()
    control = multiplicity_control()
    actual_zero = actual_zero_control()
    result = {"coefficient_route_checks": coefficients, "actual_zeta_ball_checks": checks,
              "multiplicity_and_branch_control": control,
              "actual_critical_line_zero_control": actual_zero,
              "all_passed": (all(x["within_proved_bound"] and x["perturbation_rejected"]
                                 and x["principal_branch_equals_normalized_branch_proved"]
                                 for x in checks) and control["all_passed"] and actual_zero["all_passed"]),
              "proof": "dyadic_root_proof.txt sections 4 through 8",
              "historical_novelty_is_not_certified": True}
    output = Path(__file__).resolve().parent/"dyadic-results/dyadic_analytic_probe.json"
    output.write_text(json.dumps(result, indent=2)+"\n")
    print(f"Actual zeta fractional transfers: {sum(x['within_proved_bound'] for x in checks)}/{len(checks)}; perturbations rejected: {sum(x['perturbation_rejected'] for x in checks)}/{len(checks)}; multiplicity controls: {control['all_passed']}; actual-zero control: {actual_zero['all_passed']}")
    assert result["all_passed"]


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Certified native-zeta coefficient input and mixed-index domain controls."""

from fractions import Fraction as Q
from pathlib import Path
import json
import time

import flint

from exact_arithmetic import formal_exp
from mixed_index_search import additive_log_exp, diagonal


BASE = Path(__file__).resolve().parent


def real(value):
    value = Q(value)
    return flint.arb(value.numerator) / value.denominator


def box(radius):
    return flint.acb(flint.arb(0, radius), flint.arb(0, radius))


def short(value):
    return value.str(18)


def decode_actual_log_zeta(height, cutoff=64, sigma=2048, precision=16384):
    flint.ctx.prec = precision
    s = flint.acb(sigma, height)
    residual = s.zeta().log()
    values, records = [Q(0), Q(0)], []
    for n in range(2, cutoff + 1):
        inverse_weight = (s * flint.arb(n).log()).exp()
        estimate = inverse_weight * residual
        tail = (flint.arb(n) / (n + 1)) ** sigma * (1 + flint.arb(n + 1) / (sigma - 1))
        # The calibration assumes only the established coefficient value
        # set of LOG(zeta), not which integers are prime powers.
        candidates = [Q(0)] + [Q(1, e) for e in range(1, n.bit_length())]
        possible = [q for q in candidates if not bool((estimate - real(q)).abs_lower() > tail)]
        assert len(possible) == 1, f'Coefficient {n} not uniquely separated'
        value = possible[0]
        distance = (estimate - real(value)).abs_upper()
        assert bool(distance < tail)
        values.append(value)
        residual -= real(value) * (-s * flint.arb(n).log()).exp()
        records.append({'n': n, 'recovered_exact_coefficient': str(value),
                        'candidate_distance_upper_ball': short(distance), 'proved_infinite_alias_tail_ball': short(tail),
                        'exact_value_uniquely_separated': True})
    return values, {'native_zeta_sample': [str(sigma), height], 'precision_bits': precision,
                    'coefficient_cutoff': cutoff, 'records': records,
                    'coefficient_type_prior': '0 or 1/e, 1<=e<=floor(log2 n); no prime-power locations supplied to the decoder',
                    'all_coefficients_uniquely_recovered': all(x['exact_value_uniquely_separated'] for x in records)}


def bell_tail(sigma, beta_bound, bit_cutoff, radius=Q(1)):
    r = real(radius)
    ratio = (1 + 1 / r) * flint.arb(2) ** (-real(sigma))
    assert bool(ratio < 1)
    constant = (real(beta_bound) * (r.exp() - 1)).exp()
    return constant / r * ratio ** bit_cutoff / (1 - ratio)


def reverse_reference(s, sigma, degree=48):
    exponent = sum(((s + k).zeta() - 1 for k in range(1, degree + 1)), flint.acb(0))
    tail = flint.arb(2) ** (-real(sigma) - degree) * (1 + 2 / (real(sigma) + degree))
    return (exponent + box(tail)).exp()


def evaluate(values, s):
    return sum((real(Q(coefficient)) * (-s * flint.arb(n).log()).exp()
                for n, coefficient in enumerate(values[1:], 1)), flint.acb(0))


def actual_zeta_checks(source):
    lookup = {Q(item['beta']): item for item in source['zeta_coefficient_profiles']}
    reverse_cutoff = 512
    h = [Q(0), Q(0)] + [Q(1, n - 1) for n in range(2, reverse_cutoff + 1)]
    reverse_coefficients = formal_exp(h)
    cases = ((Q(1), 3, '941.23'), (Q(1, 2), 3, '-967.41'),
             (Q(1, 4), 4, '1151.17'), (Q(2, 3), 4, '-1187.53'),
             (Q(1), 6, '1373.29'), (Q(1, 2), 6, '-1409.67'))
    records = []
    for beta, sigma, height in cases:
        observed_log, recovery = decode_actual_log_zeta(height)
        observed = diagonal(additive_log_exp([beta * x for x in observed_log], 'EXP', True))
        prefix = [Q(x) for x in lookup[beta]['coefficients'][:len(observed)]]
        prefix_agrees = observed == prefix
        flint.ctx.prec = 224
        s = flint.acb(sigma, height)
        full = evaluate(lookup[beta]['coefficients'], s)
        native_origin = evaluate(observed, s)
        permitted = bell_tail(sigma, beta, 6) + bell_tail(sigma, beta, 10)
        delta = real(Q(1, 7)) * (-s * flint.arb(2).log()).exp()
        difference = (full - native_origin).abs_upper()
        corrupted = (full + delta - native_origin).abs_lower()
        regularizer_passed = prefix_agrees and bool(difference < permitted) and bool(corrupted > permitted)
        finite_reverse = evaluate(reverse_coefficients, s)
        reference = reverse_reference(s, sigma)
        reverse_error = flint.arb(1).exp() * flint.arb(reverse_cutoff) ** (1 - sigma)
        reverse_difference = (finite_reverse - reference).abs_upper()
        reverse_bad = (finite_reverse + delta - reference).abs_lower()
        reverse_passed = bool(reverse_difference < reverse_error) and bool(reverse_bad > reverse_error)
        records.append({'beta': str(beta), 's': [str(sigma), height], 'native_zeta_coefficient_recovery': recovery,
                        'regularizer_comparison': {'arithmetic_cutoff': lookup[beta]['cutoff'], 'native_origin_cutoff': 64,
                            'exact_arithmetic_prefix_agrees': prefix_agrees, 'difference_upper_ball': short(difference),
                            'proved_combined_Bell_tail_ball': short(permitted), 'perturbed_difference_lower_ball': short(corrupted),
                            'all_passed': regularizer_passed,
                            'scope': 'Native LOG(zeta) determines exact input coefficients; this is a coefficient-origin bridge, not a claimed scalar formula for N(s)'},
                        'reverse_shifted_zeta_comparison': {'arithmetic_cutoff': reverse_cutoff, 'shift_degree': 48,
                            'difference_upper_ball': short(reverse_difference), 'proved_Rankin_tail_ball': short(reverse_error),
                            'perturbed_difference_lower_ball': short(reverse_bad), 'all_passed': reverse_passed},
                        'all_passed': regularizer_passed and reverse_passed})
        print(f'Mixed-index native zeta beta={beta}, s={sigma}+{height}i: {records[-1]["all_passed"]}', flush=True)
    return records


def actual_zero_controls():
    cases = []
    for filename, key in (('size-results/size_analytic_probe.json', 'actual_critical_line_zero_control'),
                          ('cancellation-results/cancellation_analytic.json', 'fresh_actual_critical_line_zero_control')):
        certificate = json.loads((BASE / filename).read_text())[key]
        assert certificate['all_passed']
        radius, height = Q(certificate['radius']), certificate['disk_centre'][1]
        sigma = Q(1, 2) - radius
        region = flint.acb(real(Q(1, 2)) + flint.arb(0, real(radius)),
                           flint.arb(height) + flint.arb(0, real(radius)))
        transformed = reverse_reference(region, sigma)
        r = real(Q(4))
        ratio = (1 + 1 / r) * flint.arb(2) ** (-real(sigma))
        passed = bool(transformed.abs_lower() > 0) and bool(ratio < 1)
        cases.append({'existing_actual_zero_certificate': filename, 'disk_centre': certificate['disk_centre'],
                      'radius': str(radius), 'reverse_transfer_modulus_lower_ball': short(transformed.abs_lower()),
                      'reverse_transfer_zero_preservation_rejected': bool(transformed.abs_lower() > 0),
                      'regularizer_uniform_Bell_ratio_at_radius_four_ball': short(ratio),
                      'regularizer_holomorphic_across_full_zero_disk_certified': bool(ratio < 1),
                      'fractional_zeta_root_nonzero_holomorphic_correction_across_disk_rejected': True,
                      'regularizer_point_value_on_zero_disk_claimed': False,
                      'all_passed': passed})
    return {'records': cases, 'all_passed': all(x['all_passed'] for x in cases),
            'scope': 'Existing simple-zero certificates are reused. The new tests evaluate V on the disks and certify N holomorphy; no finite N sum at the zero is called a converged value.'}


def main():
    started = time.monotonic()
    flint.ctx.prec = 224
    source = json.loads((BASE / 'mixed-index-results/mixed_index_search.json').read_text())
    points = actual_zeta_checks(source)
    flint.ctx.prec = 224
    zeros = actual_zero_controls()
    result = {'actual_zeta_ball_checks': points, 'existing_actual_zero_new_operator_controls': zeros,
              'regularizer_zeta_domain': 'Absolute convergence on Re(s)>0, jointly entire in beta by the universal Bell bound',
              'reverse_transfer_domain': 'Holomorphic and zero-free except essential singularities at 0,-1,-2,...; formula initially Re(s)>0',
              'forward_additive_transfer_has_no_convergent_Dirichlet_half_plane': True,
              'ordinary_RH_root_holomorphy_inference_rejected': True,
              'new_RH_estimate_proved': False, 'counts_as_verified_new_operator': False,
              'all_passed': all(x['all_passed'] for x in points) and zeros['all_passed'],
              'proof': 'mixed_index_proof.txt', 'elapsed_seconds': time.monotonic() - started}
    (BASE / 'mixed-index-results/mixed_index_analytic.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Mixed-index actual-zeta audit: all={result["all_passed"]}; elapsed={result["elapsed_seconds"]:.2f}s')
    assert result['all_passed']


if __name__ == '__main__':
    main()

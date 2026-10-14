#!/usr/bin/env python3
"""Native-zeta anchored bilinear correlation and one-sided root certificates."""

from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json
import time

import flint

from exact_arithmetic import formal_exp
from gap_search import couple, index
from pair_fibre_probe import prime_powers

BASE = Path(__file__).resolve().parent


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def short(x):
    return x.str(20)


def box(radius):
    return flint.acb(flint.arb(0, radius), flint.arb(0, radius))


@lru_cache(maxsize=None)
def pp(cutoff):
    return prime_powers(cutoff)


@lru_cache(maxsize=None)
def finite_encoded(cutoff=1024, r=3):
    terms = {}
    powers = pp(cutoff)
    for j, (a, _, e) in enumerate(powers):
        for b, _, f in powers[j + 1:]:
            n = index(a, b, r)
            terms[n] = terms.get(n, Q(0)) + Q(2, e * f)
    return terms


def encoded_value(s, cutoff=1024):
    return sum((real(v) * (-s * flint.arb(n).log()).exp()
                for n, v in finite_encoded(cutoff).items()), flint.acb(0))


def frame(s, sigma, cutoff, anchor=False):
    assert sigma > Q(1, 2)
    coefficients = [flint.acb(0)] * (cutoff + 1)
    q, first = flint.arb(0), flint.arb(0)
    for n, _, e in pp(cutoff):
        logn = flint.arb(n).log()
        coefficients[n] = (-s * logn).exp() / e
        damping = (-2 * real(sigma) * logn).exp()
        q += damping / e ** 2
        first += damping / e
    c = s.zeta().log() - sum(coefficients, flint.acb(0)) if anchor else flint.acb(0)
    coefficients[0] = c
    tail_square = (2 * real(sigma)).zeta().log() - first + c.abs_upper() ** 2
    norm_square = q + c.abs_upper() ** 2
    bound = 2 * (3 * real(sigma)).zeta()
    error = bound * (2 * norm_square.sqrt() * tail_square.sqrt() + tail_square)
    return coefficients, error, {'cutoff': cutoff, 'native_zeta_s_anchor': anchor,
                                 'anchor_modulus_upper_ball': short(c.abs_upper()),
                                 'native_LOG_zeta_2sigma_tail_square_ball': short(tail_square),
                                 'Toeplitz_infinite_error_ball': short(error)}


def spectral_value(s, sigma, cutoff=2048):
    ws, error, info = frame(s, sigma, cutoff, anchor=True)
    convolution = flint.acb_poly(ws) * flint.acb_poly(list(reversed(ws)))
    value = sum((2 * convolution[cutoff + d] * (-3 * s * flint.arb(d).log()).exp()
                 for d in range(1, cutoff + 1)), flint.acb(0))
    conjugated = [flint.acb(w.real, -w.imag) for w in reversed(ws)]
    wrong_convolution = flint.acb_poly(ws) * flint.acb_poly(conjugated)
    wrong = sum(((wrong_convolution[cutoff + d] + wrong_convolution[cutoff - d])
                 * (-3 * s * flint.arb(d).log()).exp()
                 for d in range(1, cutoff + 1)), flint.acb(0))
    return value, error, info, wrong, value + convolution[cutoff]


def actual_points():
    cases = ((Q(5, 3), '2.19'), (Q(2), '-4.43'), (Q(7, 3), '6.83'),
             (Q(5, 3), '-9.07'), (Q(2), '11.39'), (Q(7, 3), '-14.57'))
    rows = []
    for sigma, height in cases:
        s = flint.acb(real(sigma), height)
        finite = encoded_value(s)
        _, tail, left_info = frame(s, sigma, 1024)
        reference, error, info, wrong_hermitian, wrong_diagonal = spectral_value(s, sigma)
        allowed = tail + error
        distance = (finite - reference).abs_upper()
        changed = (finite + real(Q(1, 2)) * (-s * flint.arb(6).log()).exp() - reference).abs_lower()
        conjugacy = (finite - wrong_hermitian).abs_lower()
        diagonal = (finite - wrong_diagonal).abs_lower()
        passed = bool(distance < allowed) and bool(changed > allowed) and bool(conjugacy > allowed) and bool(diagonal > allowed)
        rows.append({'s': [str(sigma), height], 'r': 3, 'finite_encoded_input_cutoff': 1024,
                     'finite_encoded_terms': len(finite_encoded()), 'source_input_tail': left_info,
                     'native_bilinear_correlation_reference': info,
                     'difference_upper_ball': short(distance), 'combined_infinite_tail_ball': short(allowed),
                     'changed_coefficient_six_error': '1/2', 'changed_difference_lower_ball': short(changed),
                     'wrong_Hermitian_conjugation_difference_lower_ball': short(conjugacy),
                     'wrong_included_diagonal_difference_lower_ball': short(diagonal), 'all_passed': passed})
        print('Gap native-zeta bilinear correlation', sigma, height, passed, flush=True)
    return rows


def transformed_root_points():
    size, sigma, height = 1024, Q(2), '7.19'
    h = [Q(0)] * (size + 1)
    for n, _, e in pp(size):
        h[n] = Q(1, e)
    kappa = couple(h, h)
    s = flint.acb(real(sigma), height)
    reference, error, _, _, _ = spectral_value(s, sigma)
    gamma = reference + box(error)
    real_reference, real_error, _, _, _ = spectral_value(flint.acb(real(sigma)), sigma)
    real_gamma = real_reference.real + flint.arb(0, real_error)
    rows = []
    for beta, family in ((Q(1), 'input'), (Q(1, 2), 'input'), (Q(1, 2), 'output'),
                         (Q(1, 4), 'input'), (Q(1, 4), 'output')):
        amplitude = beta ** 2 if family == 'input' else beta
        coefficients = formal_exp([beta * v + amplitude * w for v, w in zip(h, kappa)])
        finite = sum((real(v) * (-s * flint.arb(n).log()).exp() for n, v in enumerate(coefficients) if v), flint.acb(0))
        value = (real(beta) * s.zeta().log() + real(amplitude) * gamma).exp()
        real_value = (real(beta) * real(sigma).zeta().log() + real(amplitude) * real_gamma).exp()
        real_prefix = sum((real(v) * flint.arb(n) ** (-real(sigma)) for n, v in enumerate(coefficients) if v), flint.arb(0))
        tail = (real_value - real_prefix).abs_upper()
        distance = (finite - value).abs_upper()
        changed = (finite + real(Q(1, 2)) * (-s * flint.arb(6).log()).exp() - value).abs_lower()
        passed = bool(distance < tail) and bool(changed > tail)
        rows.append({'s': [str(sigma), height], 'beta': str(beta), 'family': family,
                     'amplitude': str(amplitude), 'coefficient_cutoff': size,
                     'scalar_formula': 'zeta(s)^beta*EXP(amplitude*Gamma_gap_3(s))',
                     'difference_upper_ball': short(distance), 'positive_real_total_minus_prefix_tail_ball': short(tail),
                     'changed_difference_lower_ball': short(changed), 'all_passed': passed})
        print('Gap ordinary-root scalar', beta, family, passed, flush=True)
    return {'records': rows, 'all_passed': all(row['all_passed'] for row in rows)}


def actual_zero_controls():
    rows = []
    for filename, key in (('size-results/size_analytic_probe.json', 'actual_critical_line_zero_control'),
                          ('cancellation-results/cancellation_analytic.json', 'fresh_actual_critical_line_zero_control')):
        old = json.loads((BASE / filename).read_text())[key]
        assert old['all_passed']
        radius, height = Q(old['radius']), old['disk_centre'][1]
        centre = flint.acb(real(Q(1, 2)), height)
        for epsilon in (radius, radius / 2, radius / 4):
            sigma = Q(1, 2) + epsilon
            s = centre + real(epsilon)
            z = s.zeta()
            major = 2 * (3 * real(sigma)).zeta() * (2 * real(sigma)).zeta().log()
            finite = encoded_value(s)
            _, tail, info = frame(s, sigma, 1024)
            enclosure = finite + box(tail)
            factors = []
            for beta in (Q(1), Q(1, 2), Q(1, 4)):
                lower = (-real(beta ** 2) * major).exp()
                upper = (real(beta ** 2) * major).exp()
                factors.append({'beta': str(beta), 'input_root_correction_modulus_lower_ball': short(lower),
                                'input_root_correction_modulus_upper_ball': short(upper),
                                'strictly_positive_lower': bool(lower > 0)})
            passed = z.is_finite() and bool(z.abs_lower() > 0) and enclosure.is_finite() and all(v['strictly_positive_lower'] for v in factors)
            rows.append({'disk_centre': old['disk_centre'], 'reused_simple_zero_radius': old['radius'],
                         'epsilon': str(epsilon), 's_real_part': str(sigma),
                         'native_zeta_modulus_ball': short(abs(z)), 'native_zeta_modulus_over_epsilon_ball': short(abs(z) / real(epsilon)),
                         'Gamma_finite_plus_infinite_error_modulus_upper_ball': short(enclosure.abs_upper()),
                         'native_absolute_Gamma_majorant_ball': short(major), 'infinite_error_reference': info,
                         'factor_modulus_controls': factors, 'one_sided_right_halfplane_only': True,
                         'whole_zero_disk_correction_holomorphy_claimed': False,
                         'LOG_zeta_s_used_as_Gamma_anchor_below_Re_one': False,
                         'boundary_zero_limit_uses_the_proved_endpoint_convergence': True, 'all_passed': passed})
            print('Gap one-sided root control', epsilon, height, passed, flush=True)
    return {'records': rows, 'all_passed': all(row['all_passed'] for row in rows)}


def main():
    start = time.monotonic()
    flint.ctx.prec = 512
    source = json.loads((BASE / 'gap-results/gap_search.json').read_text())
    assert source['all_passed']
    points, roots, zeros = actual_points(), transformed_root_points(), actual_zero_controls()
    out = {'actual_zeta_ball_checks': points, 'transformed_ordinary_root_scalar_controls': roots,
           'one_sided_actual_zero_controls': zeros,
           'actual_reference': 'Nonconjugating additive correlation anchored by native LOG zeta(s) only when Re(s)>1; Toeplitz tails use native LOG zeta(2*sigma)',
           'encoded_absolute_abscissa': 'max(2/(r+2),1/2)', 'encoded_endpoint_convergence_iff': 'r=1 or r>=3',
           'selected_r_three_correction_holomorphic_Re_gt_half': True,
           'selected_r_three_correction_continuous_Re_ge_half': True,
           'whole_critical_zero_disk_holomorphy_established': False,
           'ordinary_transformed_Dirichlet_series_absolute_abscissa': '1',
           'classical_prime_pair_correlation_kernel_matched': True,
           'counts_as_new_primitive': False, 'historical_novelty_established': False, 'new_RH_estimate_proved': False,
           'all_passed': all(row['all_passed'] for row in points) and roots['all_passed'] and zeros['all_passed'],
           'seconds': time.monotonic() - start}
    (BASE / 'gap-results/gap_analytic.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Gap analytic source:', out['all_passed'], 'seconds', out['seconds'], flush=True)
    assert out['all_passed']


if __name__ == '__main__':
    main()

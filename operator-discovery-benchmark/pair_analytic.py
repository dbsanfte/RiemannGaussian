#!/usr/bin/env python3
"""Native zeta Mellin--Barnes checks and certified ordinary-zero controls."""

from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json
import time

import flint

from exact_arithmetic import formal_exp
from pair_search import couple
from pair_bridge_prototype import real, logarithmic_coefficient, native_pair, direct_pair

BASE = Path(__file__).resolve().parent


def short(x):
    return x.str(18)


def bound(sigma, r=3):
    return flint.arb(2) ** (-r * real(sigma)) * real((r + 2) * sigma / 2).zeta().log() ** 2


@lru_cache(maxsize=None)
def profile(beta, family):
    h = [Q(0), Q(0)] + [logarithmic_coefficient(n) for n in range(2, 4097)]
    extra = couple(h, h)
    c = beta ** 2 if family == 'input' else beta
    return formal_exp([beta * x + c * y for x, y in zip(h, extra)])


def evaluate(values, s):
    return sum((real(x) * (-s * flint.arb(n).log()).exp() for n, x in enumerate(values[1:], 1) if x), flint.acb(0))


def points():
    records = []
    cases = ((Q(1), 'input', Q(5, 3), '3.11'), (Q(1, 2), 'input', Q(2), '-5.07'),
             (Q(1, 4), 'output', Q(7, 3), '7.19'), (Q(2, 3), 'output', Q(5, 3), '-9.23'),
             (Q(1), 'output', Q(2), '11.37'), (Q(1, 2), 'output', Q(7, 3), '-13.41'))
    norm = bound(Q(1))
    for beta, family, sigma, height in cases:
        s = flint.acb(real(sigma), height)
        correction, info = native_pair(s, sigma, height)
        c = beta ** 2 if family == 'input' else beta
        reference = (real(beta) * s.zeta().log() + real(c) * correction).exp()
        finite = evaluate(profile(beta, family), s)
        allowed = (1 + 1 / (real(sigma) - 1)) * flint.arb(4096) ** (1 - real(sigma)) * (real(c) * norm).exp()
        corrupted = finite + real(Q(1, 2)) * (-s * flint.arb(2).log()).exp()
        distance, wrong = (finite - reference).abs_upper(), (corrupted - reference).abs_lower()
        direct, tail = direct_pair(s, sigma)
        direct_distance = (direct - correction).abs_upper()
        wrong_kernel = (direct + real(Q(1, 3)) * (-s * flint.arb(256).log()).exp() - correction).abs_lower()
        wrong_factor = (2 * correction - direct).abs_lower()
        passed = (bool(distance < allowed) and bool(wrong > allowed) and bool(direct_distance < tail)
                  and bool(wrong_kernel > tail) and bool(wrong_factor > tail))
        records.append({'beta': str(beta), 'family': family, 'correction_amplitude': str(c), 's': [str(sigma), height],
                        'arithmetic_cutoff': 4096, 'native_Mellin_Barnes_reference': info,
                        'difference_upper_ball': short(distance), 'proved_full_coefficient_tail_ball': short(allowed),
                        'perturbed_difference_lower_ball': short(wrong), 'direct_prime_power_cutoff': 64,
                        'direct_kernel_difference_upper_ball': short(direct_distance), 'direct_kernel_tail_ball': short(tail),
                        'perturbed_kernel_difference_lower_ball': short(wrong_kernel), 'wrong_integral_normalization_lower_ball': short(wrong_factor),
                        'all_passed': passed})
        print(f'Nonlinear pair zeta bridge beta={beta}, family={family}, s={sigma}+{height}i: {passed}', flush=True)
    return records


def root_controls():
    records = []
    for filename, key in (('size-results/size_analytic_probe.json', 'actual_critical_line_zero_control'),
                          ('cancellation-results/cancellation_analytic.json', 'fresh_actual_critical_line_zero_control')):
        old = json.loads((BASE / filename).read_text())[key]
        assert old['all_passed']
        radius, height = Q(old['radius']), old['disk_centre'][1]
        sigma = Q(1, 2) - radius
        centre = flint.acb(real(Q(1, 2)), height)
        value, info = native_pair(centre, Q(1, 2), height, margin=26, tolerance='1e-22')
        maximum, roots = bound(sigma), []
        for family in ('input', 'output'):
            for beta in (Q(1, 2), Q(1, 4), Q(1)):
                c = beta ** 2 if family == 'input' else beta
                lower = (-real(c) * maximum).exp()
                phase = (flint.acb(0, 2 * flint.arb.pi() * real(beta))).exp() - 1 if beta != 1 else flint.acb(0)
                jump = phase.abs_lower() * lower
                passed = bool(lower > 0) and (bool(jump > 0) if beta != 1 else jump.is_zero())
                roots.append({'beta': str(beta), 'family': family, 'correction_amplitude': str(c),
                              'whole_disk_correction_modulus_lower_ball': short(lower),
                              'monodromy_correction_factor_lower_ball': short(jump), 'all_passed': passed})
        records.append({'disk_centre': old['disk_centre'], 'radius': old['radius'],
                        'existing_simple_zero_certificate_reused': True, 'centre_native_correction_ball': short(value),
                        'centre_native_correction_components': [short(value.real), short(value.imag)],
                        'centre_native_reference': info, 'whole_disk_correction_absolute_norm_ball': short(maximum),
                        'correction_holomorphic_on_Re_s_gt': '2/5', 'records': roots,
                        'phase_bound_scope': 'Bound for |(exp(2*pi*i*beta)-1)*C|; full H jump additionally includes zeta^beta',
                        'all_passed': value.is_finite() and all(r['all_passed'] for r in roots)})
        print('Nonlinear pair critical-zero disk', height, records[-1]['all_passed'], flush=True)
    return {'records': records, 'all_passed': all(x['all_passed'] for x in records)}


def root_blind_negative_control():
    # At r=0 the correction is exp((LOG zeta)^2). A logarithm around
    # a simple zero changes by 2*pi*i, producing a nonconstant ratio.
    ell, shift = flint.acb(real(Q(1, 3)), real(Q(1, 7))), flint.acb(0, 2 * flint.arb.pi())
    ratio = (2 * shift * ell + shift ** 2).exp()
    return {'r': 0, 'known_correction': 'exp((LOG zeta)^2)',
            'nonconstant_monodromy_ratio': 'exp(4*pi*i*LOG zeta-4*pi^2)',
            'toy_local_logarithm': ['1/3', '1/7'], 'monodromy_ratio_ball': short(ratio),
            'single_valued_correction_rejected': bool((ratio - 1).abs_lower() > 0),
            'actual_zero_location_inferred_from_toy_model': False}


def main():
    start = time.monotonic()
    flint.ctx.prec = 256
    rows, zeros, negative = points(), root_controls(), root_blind_negative_control()
    passed = all(x['all_passed'] for x in rows) and zeros['all_passed'] and negative['single_valued_correction_rejected']
    result = {'actual_zeta_ball_checks': rows, 'existing_actual_zero_new_operator_controls': zeros,
              'root_blind_known_composite_negative_control': negative, 'all_passed': passed,
              'r_three_correction_halfplane': 'Re(s)>2/5', 'native_zeta_branch': 'Normalized Euler LOG; principal branch certified by log(zeta(Re argument))<pi',
              'ordinary_Dirichlet_series_correction_convergence_proved': True,
              'new_RH_estimate_proved': False, 'historical_novelty_established': False,
              'elapsed_seconds': time.monotonic() - start}
    (BASE / 'pair-results/pair_analytic.json').write_text(json.dumps(result, indent=2) + '\n')
    print('Nonlinear pair analytic checks:', passed, 'seconds', result['elapsed_seconds'], flush=True)
    assert passed


if __name__ == '__main__':
    main()

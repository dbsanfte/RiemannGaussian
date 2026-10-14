#!/usr/bin/env python3
"""Certified zeta bridge and restored logarithmic-zero obstruction after decoding."""

from fractions import Fraction as Q
from pathlib import Path
import json
import time

import flint

from exact_arithmetic import factorization

BASE = Path(__file__).resolve().parent


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def short(x):
    return x.str(18)


def box(radius):
    return flint.acb(flint.arb(0, radius), flint.arb(0, radius))


def mobius(n):
    factors = factorization(n)
    return 0 if any(e > 1 for e in factors.values()) else (-1) ** len(factors)


def local_square_coefficients(degree, r=3):
    h = [Q(0)] + [Q(1, e) if e % r else Q(0) for e in range(1, degree + 1)]
    return [sum((h[a] * h[k - a] for a in range(1, k)), Q(0)) for k in range(degree + 1)]


def native_prime_zeta(s, sigma, cutoff=24):
    value = sum((real(Q(mobius(m), m)) * (m * s).zeta().log()
                 for m in range(1, cutoff + 1) if mobius(m)), flint.acb(0))
    t = flint.arb(2) ** (-real(sigma))
    tail = t ** (cutoff + 1) / ((cutoff + 1) * (1 - t)) * (1 + 2 / ((cutoff + 1) * real(sigma) - 1))
    return value + box(tail), tail


def native_diagonal(s, sigma, degree=48):
    coefficients = local_square_coefficients(degree)
    out = flint.acb(0)
    prime_tail = flint.arb(0)
    for k in range(2, degree + 1):
        if coefficients[k]:
            prime, tail = native_prime_zeta(k * s, k * sigma)
            out += real(coefficients[k]) * prime
            prime_tail += abs(real(coefficients[k])) * tail
    t = flint.arb(2) ** (-real(sigma))
    coefficient_tail = (1 + 2 / ((degree + 1) * real(sigma) - 1)) * t ** (degree + 1)
    coefficient_tail *= (degree + 1) / (1 - t) + t / (1 - t) ** 2
    return out + box(coefficient_tail), {'prime_Mobius_cutoff': 24, 'local_square_degree': degree,
                                         'total_Mobius_tail_ball': short(prime_tail),
                                         'local_square_infinite_tail_ball': short(coefficient_tail)}


def actual_points(source):
    values = list(map(Q, source['zeta_decoded_profile']['decoded_coefficients']))[:4097]
    cases = ((Q(5, 3), '4.13'), (Q(2), '-6.53'), (Q(7, 3), '8.89'),
             (Q(5, 3), '-10.61'), (Q(2), '12.83'), (Q(7, 3), '-15.17'))
    records = []
    for sigma, height in cases:
        s = flint.acb(real(sigma), height)
        diagonal, info = native_diagonal(s, sigma)
        G = s.zeta().log() - (3 * s).zeta().log() / 3
        reference = G ** 2 - diagonal
        finite = sum((real(v) * (-s * flint.arb(n).log()).exp() for n, v in enumerate(values) if v), flint.acb(0))
        allowed = 2 * flint.arb(4096) ** (1 - real(sigma)) / (real(sigma) - 1)
        wrong = finite + real(Q(1, 2)) * (-s * flint.arb(6).log()).exp()
        distance, perturbed = (finite - reference).abs_upper(), (wrong - reference).abs_lower()
        passed = bool(distance < allowed) and bool(perturbed > allowed)
        records.append({'s': [str(sigma), height], 'decoded_coefficient_cutoff': 4096,
                        'scalar_formula': '(LOG zeta(s)-LOG zeta(3s)/3)^2-Q_3(s)', 'native_reference': info,
                        'difference_upper_ball': short(distance), 'proved_decoded_tail_ball': short(allowed),
                        'perturbed_difference_lower_ball': short(perturbed), 'all_passed': passed})
        print('Decoded native-zeta bridge', sigma, height, passed, flush=True)
    return records


def restored_zero_controls():
    records = []
    for filename, key in (('size-results/size_analytic_probe.json', 'actual_critical_line_zero_control'),
                          ('cancellation-results/cancellation_analytic.json', 'fresh_actual_critical_line_zero_control')):
        old = json.loads((BASE / filename).read_text())[key]
        assert old['all_passed']
        radius, height = Q(old['radius']), old['disk_centre'][1]
        centre = flint.acb(real(Q(1, 2)), height)
        base = centre + real(radius)
        region = centre + box(real(radius))
        z, z3 = base.zeta(), (3 * base).zeta()
        real_G = abs(z).log() - abs(z3).log() / 3
        # Every local log sheet has this same real part. The imaginary
        # component of the quadratic-log jump is 4*pi*Re(G), so its
        # lower bound is independent of the initial logarithm branch.
        jump_lower = 4 * flint.arb.pi() * real_G.abs_lower()
        second_nonzero = (2 * region).zeta().abs_lower()
        branch_correction_nonzero = (3 * region).zeta().abs_lower()
        passed = (bool(z.abs_lower() > 0) and bool(real_G < 0) and bool(jump_lower > 0)
                  and bool(second_nonzero > 0) and bool(branch_correction_nonzero > 0)
                  and Q(1, 2) - radius > Q(2, 5))
        records.append({'disk_centre': old['disk_centre'], 'radius': old['radius'],
                        'existing_simple_zero_certificate_reused': True,
                        'basepoint_real_part': str(Q(1, 2) + radius), 'basepoint_zeta_modulus_ball': short(abs(z)),
                        'branch_independent_Re_G_ball': short(real_G), 'decoded_log_monodromy_jump_lower_ball': short(jump_lower),
                        'whole_disk_zeta_2s_nonzero_lower_ball': short(second_nonzero),
                        'whole_disk_zeta_3s_nonzero_lower_ball': short(branch_correction_nonzero),
                        'diagonal_holomorphic_on_whole_disk': True,
                        'encoded_Gamma_holomorphic_on_whole_disk': True,
                        'decoded_Gamma_single_valued_holomorphy_rejected': passed,
                        'initial_Euler_sheet_of_basepoint_logarithm_asserted': False,
                        'all_passed': passed})
        print('Restored decoded zero obstruction', height, passed, flush=True)
    return {'records': records, 'all_passed': all(x['all_passed'] for x in records)}


def main():
    started = time.monotonic()
    flint.ctx.prec = 512
    source = json.loads((BASE / 'decode-results/decode_search.json').read_text())
    assert source['all_passed']
    rows, zeros = actual_points(source), restored_zero_controls()
    out = {'actual_zeta_ball_checks': rows, 'restored_actual_zero_obstruction_controls': zeros,
           'absolute_decoded_Dirichlet_abscissa': '1', 'diagonal_correction_Re_s_gt_half_proved': True,
           'local_diagonal_extension': 'Q_r=LOG zeta(2s)+B_r, B_r holomorphic on Re(s)>1/3',
           'encoded_correction_proved_absolute_halfplane': 'Re(s)>2/5',
           'decoder_preserves_same_analytic_halfplane_rejected': True,
           'new_RH_estimate_proved': False, 'historical_novelty_established': False,
           'all_passed': all(r['all_passed'] for r in rows) and zeros['all_passed'],
           'seconds': time.monotonic() - started}
    (BASE / 'decode-results/decode_analytic.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Decoder analytic source audit:', out['all_passed'], 'seconds', out['seconds'], flush=True)
    assert out['all_passed']


if __name__ == '__main__':
    main()

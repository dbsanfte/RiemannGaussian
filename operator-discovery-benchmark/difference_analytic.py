#!/usr/bin/env python3
"""Certified shifted-log-zeta bridge and ordinary-root zero controls."""

from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json
import time

import flint

from exact_arithmetic import factorization, formal_exp
from difference_search import difference, words


BASE = Path(__file__).resolve().parent


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def short(x):
    return x.str(18)


def box(radius):
    return flint.acb(flint.arb(0, radius), flint.arb(0, radius))


@lru_cache(maxsize=None)
def log_coefficient(n):
    factors = factorization(n)
    return Q(1, next(iter(factors.values()))) if len(factors) == 1 else Q(0)


def kernel(n, s, m, k):
    out = flint.acb(0)
    for word, weight, _ in words(m, k):
        image = n
        for a in word:
            image = image * image + a * image
        out += weight * (-s * flint.arb(image).log()).exp()
    return out


def native_coefficients(s, m, k, degree):
    flint.ctx.cap = degree + 1
    out = flint.acb_series([], degree + 1)
    for _, weight, polynomial in words(m, k):
        # A tuple is a scalar dyadic-ball encoding to FLINT, not a
        # coefficient sequence. Require an explicit list and its unit.
        h = flint.acb_series(list(polynomial[::-1]), degree + 1)
        assert h[0] == 1 and h[1] == polynomial[-2]
        out += weight * (-s * h.log()).exp()
    order = m * (2 ** k - 1)
    coefficients = [out[j] for j in range(degree + 1)]
    assert all(x.contains(0) for x in coefficients[:order])
    leading = flint.acb((-1) ** (m * k))
    for j in range(k):
        for ell in range(m):
            leading *= 2 ** j * s + m * (2 ** j - 1) + ell
    assert (coefficients[order] - leading).contains(0)
    coefficients[:order] = [flint.acb(0)] * order  # universal cancellation proof
    return coefficients


def coefficient_bound(s, m, k):
    return flint.arb(2) ** (m * k + s.abs_upper() * (2 ** k - 1))


def native_delta(s, sigma, m=2, k=2, degree=192):
    d, order = 2 ** k, m * (2 ** k - 1)
    prefix, radius = 4 * (m + 1), real(Q(1, 2 * (m + 1)))
    coefficients = native_coefficients(s, m, k, degree)
    out = sum((real(log_coefficient(n)) * kernel(n, s, m, k)
               for n in range(2, prefix + 1) if log_coefficient(n)), flint.acb(0))
    for j in range(order, degree + 1):
        z = d * s + j
        # All evaluated instances have Re(z)>=2 (or nearly 2 on the
        # trivial-zero disk); the native principal log is the normalized
        # Euler log there. The universal formula uses that Euler branch.
        remainder = z.zeta().log()
        remainder -= sum((real(log_coefficient(n)) * (-z * flint.arb(n).log()).exp()
                          for n in range(2, prefix + 1) if log_coefficient(n)), flint.acb(0))
        out += coefficients[j] * remainder
    ratio = 1 / (radius * (prefix + 1))
    tail = coefficient_bound(s, m, k) * flint.arb(prefix + 1) ** (-d * real(sigma))
    tail *= ratio ** (degree + 1) / (1 - ratio) * (1 + flint.arb(prefix + 1) / (d * real(sigma) + degree))
    return out + box(tail), {'series_degree': degree, 'finite_input_prefix': prefix,
                            'Cauchy_radius': str(Q(1, 2 * (m + 1))), 'infinite_shift_tail_ball': short(tail)}


@lru_cache(maxsize=None)
def arithmetic_profile(beta):
    h = [Q(0), Q(0)] + [log_coefficient(n) for n in range(2, 4097)]
    shifted = difference(h, 2, 2)
    return formal_exp([beta * (x + y) for x, y in zip(h, shifted)])


def evaluate(values, s):
    return sum((real(x) * (-s * flint.arb(n).log()).exp()
                for n, x in enumerate(values[1:], 1)), flint.acb(0))


def correction_absolute_norm():
    value = flint.arb(0)
    for n in range(2, 65):
        g = log_coefficient(n)
        if not g:
            continue
        for word, weight, _ in words(2, 2):
            image = n
            for a in word:
                image = image * (image + a)
            value += real(g) * abs(weight) / image
    return value + flint.arb(16) / (3 * 64 ** 3)


def actual_points():
    records = []
    cases = ((Q(1), Q(3, 2), '3.73'), (Q(1, 2), Q(7, 4), '-6.29'),
             (Q(1, 4), Q(2), '9.41'), (Q(2, 3), Q(3, 2), '-11.83'),
             (Q(1), Q(2), '15.79'), (Q(1, 2), Q(9, 4), '-18.97'))
    norm = correction_absolute_norm()
    for beta, sigma, height in cases:
        s = flint.acb(real(sigma), height)
        delta, tail_data = native_delta(s, sigma)
        reference = (real(beta) * (s.zeta().log() + delta)).exp()
        finite = evaluate(arithmetic_profile(beta), s)
        allowed = (1 + 1 / (real(sigma) - 1)) * flint.arb(4096) ** (1 - real(sigma)) * (real(beta) * norm).exp()
        perturbation = real(Q(1, 2)) * (-s * flint.arb(2).log()).exp()
        distance, corrupted = (finite - reference).abs_upper(), (finite + perturbation - reference).abs_lower()
        passed = bool(distance < allowed) and bool(corrupted > allowed)
        records.append({'beta': str(beta), 's': [str(sigma), height], 'm': 2, 'k': 2,
                        'arithmetic_cutoff': 4096, 'native_shifted_log_reference': tail_data,
                        'difference_upper_ball': short(distance), 'proved_full_coefficient_tail_ball': short(allowed),
                        'perturbed_difference_lower_ball': short(corrupted), 'all_passed': passed})
        print(f'Ordinary-root difference bridge beta={beta}, s={sigma}+{height}i: {passed}', flush=True)
    return records


def grouped_tail(s, sigma, cutoff, coefficients, degree=16):
    d, order = 4, 6
    tail = flint.arb(0)
    for j in range(order, degree + 1):
        exponent = d * real(sigma) + j
        assert bool(exponent > 1)
        tail += coefficients[j].abs_upper() * flint.arb(cutoff) ** (1 - exponent) / (exponent - 1)
    radius = real(Q(1, 6))
    remainder_exponent = d * real(sigma) + degree + 1
    return tail + coefficient_bound(s, 2, 2) / radius ** (degree + 1) / (1 - 1 / (radius * cutoff)) * (
        flint.arb(cutoff) ** (1 - remainder_exponent) / (remainder_exponent - 1))


def negative_domain_controls():
    records = []
    for sigma, height in ((Q(-1), '1.3'), (Q(-3, 4), '-2.4')):
        s = flint.acb(real(sigma), height)
        reference, metadata = native_delta(s, sigma)
        finite = sum((real(log_coefficient(n)) * kernel(n, s, 2, 2) for n in range(2, 513) if log_coefficient(n)), flint.acb(0))
        coefficients = native_coefficients(s, 2, 2, 16)
        tail = grouped_tail(s, sigma, 512, coefficients)
        distance = (finite - reference).abs_upper()
        corrupted = (finite + real(Q(1, 7)) * kernel(2, s, 2, 2) - reference).abs_lower()
        passed = bool(distance < tail) and bool(corrupted > tail)
        records.append({'s': [str(sigma), height], 'grouped_input_cutoff': 512, 'native_reference': metadata,
                        'difference_upper_ball': short(distance), 'grouped_infinite_tail_ball': short(tail),
                        'perturbed_grouped_difference_lower_ball': short(corrupted),
                        'ordinary_coefficient_series_convergence_claimed': False, 'all_passed': passed})
    return {'records': records, 'all_passed': all(x['all_passed'] for x in records)}


def root_records(delta, label):
    records = []
    for beta in (Q(1, 2), Q(1, 4), Q(1)):
        correction = (real(beta) * delta).exp()
        nonzero = bool(correction.abs_lower() > 0)
        phase = (flint.acb(0, 2 * flint.arb.pi() * real(beta))).exp() - 1 if beta.denominator != 1 else flint.acb(0)
        jump = phase.abs_lower() * correction.abs_lower()
        phase_passed = bool(jump > 0) if beta.denominator != 1 else jump.is_zero()
        records.append({'beta': str(beta), 'correction_modulus_lower_ball': short(correction.abs_lower()),
                        'root_monodromy_jump_lower_ball': short(jump), 'integer_parameter': beta.denominator == 1,
                        'all_passed': nonzero and phase_passed})
    return {'zero': label, 'records': records,
            'phase_bound_scope': 'Bound for |(exp(2*pi*i*beta)-1)*C_beta|; the full H jump additionally includes zeta^beta',
            'all_passed': all(x['all_passed'] for x in records)}


def actual_zero_controls():
    records = []
    for filename, key in (('size-results/size_analytic_probe.json', 'actual_critical_line_zero_control'),
                          ('cancellation-results/cancellation_analytic.json', 'fresh_actual_critical_line_zero_control')):
        old = json.loads((BASE / filename).read_text())[key]
        assert old['all_passed']
        radius, height = Q(old['radius']), old['disk_centre'][1]
        sigma = Q(1, 2) - radius
        centre = flint.acb(real(Q(1, 2)), height)
        delta, metadata = native_delta(centre, Q(1, 2))
        # Subtracting a prime-power prefix in a large s rectangle loses
        # dependencies. Enclose the whole disk from the centre and an
        # absolute derivative sum instead.
        t = 4 * real(sigma)
        flint.ctx.cap = 2
        jet = flint.acb_series([flint.acb(t), 1], 2).zeta()
        derivative_bound = 16 * (4 * (-jet[1] / jet[0]).real.abs_upper()
                                 + 3 * flint.arb(2).log() * jet[0].log().real.abs_upper())
        spread = derivative_bound * flint.arb(2).sqrt() * real(radius)
        delta += box(spread)
        metadata['whole_disk_method'] = 'Native centre plus absolute logarithmic derivative bound'
        metadata['whole_disk_derivative_bound_ball'] = short(derivative_bound)
        metadata['whole_disk_delta_spread_ball'] = short(spread)
        root = root_records(delta, old['disk_centre'])
        records.append({'existing_zero_certificate': filename, 'disk_centre': old['disk_centre'],
                        'radius': str(radius), 'native_correction_certificate': metadata, **root})
    return {'records': records, 'all_passed': all(x['all_passed'] for x in records)}


def trivial_zero_control():
    radius = Q(1, 10000)
    centre = flint.acb(-2)
    region = centre + box(real(radius))
    flint.ctx.cap = 3
    jet = flint.acb_series([centre, 1], 3).zeta()
    ranged = flint.acb_series([region, 1], 3).zeta()
    assert centre.zeta().is_zero()
    linear = jet[1].abs_lower() * real(radius)
    remainder = ranged[2].abs_upper() * real(radius) ** 2
    simple = bool(remainder < linear)
    rising = flint.acb(1)
    for j in range(6):
        rising *= region + j
    # Sixth forward difference annihilates Phi_a(n)^2 at s=-2.
    # The exact integral formula bounds the whole crossing disk without
    # catastrophic subtraction of large polynomial terms.
    z = 2 * (Q(-2) - radius) + 6
    bound = rising.abs_upper() * flint.acb(real(z)).zeta().log().real.abs_upper()
    delta = box(bound)
    roots = root_records(delta, ['-2', '0'])
    centre_delta, metadata = native_delta(centre, Q(-2), m=6, k=1)
    passed = simple and roots['all_passed'] and centre_delta.contains(0)
    return {'disk_centre': ['-2', '0'], 'radius': str(radius), 'm': 6, 'k': 1,
            'exact_trivial_zero_native_value': short(centre.zeta()), 'derivative_ball': short(jet[1]),
            'Rouche_linear_lower_ball': short(linear), 'Taylor_remainder_upper_ball': short(remainder),
            'one_simple_trivial_zeta_zero_certified': simple,
            'exact_correction_at_minus_two': '1 for every beta, by sixth-difference annihilation',
            'full_disk_delta_integral_bound_ball': short(bound), 'native_centre_delta': short(centre_delta),
            'native_centre_certificate': metadata, **roots, 'all_passed': passed}


def main():
    started = time.monotonic()
    flint.ctx.prec = 2048
    points = actual_points()
    negative = negative_domain_controls()
    zeros, trivial = actual_zero_controls(), trivial_zero_control()
    result = {'actual_zeta_ball_checks': points, 'negative_grouped_domain_controls': negative,
              'existing_actual_zero_new_operator_controls': zeros, 'actual_trivial_zero_control': trivial,
              'ordinary_D_roots_preserved': True, 'selected_correction_zero_free_Re_s_gt_minus_five_quarters': True,
              'negative_domain_claim_is_grouped_continuation': True, 'new_RH_estimate_proved': False,
              'counts_as_verified_new_operator': False, 'proof': 'difference_proof.txt',
              'all_passed': all(x['all_passed'] for x in points) and negative['all_passed'] and zeros['all_passed'] and trivial['all_passed'],
              'elapsed_seconds': time.monotonic() - started}
    (BASE / 'difference-results/difference_analytic.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Ordinary-root difference analytic audit: all={result["all_passed"]}; elapsed={result["elapsed_seconds"]:.2f}s')
    assert result['all_passed']


if __name__ == '__main__':
    main()

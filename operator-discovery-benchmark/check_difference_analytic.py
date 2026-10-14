#!/usr/bin/env python3
"""Independent grouped prime-power, tail and ordinary-root zero audit."""

from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import json
import time

import flint

from check_difference import arithmetic_profile, interpolated, word_value
from check_joint_size import factors


BASE = Path(__file__).resolve().parent


def real(x):
    x = Q(x)
    return flint.arb(x.numerator) / x.denominator


def short(x):
    return x.str(18)


def box(x):
    return flint.acb(flint.arb(0, x), flint.arb(0, x))


@lru_cache(maxsize=None)
def g(n):
    f = factors(n)
    return Q(1, next(iter(f.values()))) if len(f) == 1 else Q(0)


@lru_cache(maxsize=None)
def exact_logarithms(m, k, degree):
    records = []
    for word, weight, h in interpolated(m, k):
        log = [Q(0)]
        for n in range(1, degree + 1):
            value = h[n] if n < len(h) else Q(0)
            value -= sum((Q(j, n) * log[j] * h[n - j]
                          for j in range(1, n) if n - j < len(h)), Q(0))
            log.append(value)
        records.append((weight, log))
    return records


def coefficients(s, m=2, k=2, degree=18):
    out = [flint.acb(0)] * (degree + 1)
    for weight, log in exact_logarithms(m, k, degree):
        power = [flint.acb(1)]
        for n in range(1, degree + 1):
            power.append(-s * sum((j * real(log[j]) * power[n - j] for j in range(1, n + 1)), flint.acb(0)) / n)
        out = [x + weight * y for x, y in zip(out, power)]
    order = m * (2 ** k - 1)
    assert all(x.contains(0) for x in out[:order])
    leading = flint.acb((-1) ** (m * k))
    for j in range(k):
        for ell in range(m):
            leading *= 2 ** j * s + m * (2 ** j - 1) + ell
    assert (out[order] - leading).contains(0)
    out[:order] = [flint.acb(0)] * order
    return out


def cauchy_bound(s, m, k):
    radius = real(Q(1, 3 * (m + 1)))
    return flint.arb(2) ** (m * k) * (1 - m * radius) ** (-s.abs_upper() * (2 ** k - 1))


def recursive_kernel(n, s, m=2, k=2):
    if not k:
        return (-s * flint.arb(n).log()).exp()
    from math import comb
    return sum(((-1) ** (m - a) * comb(m, a) * recursive_kernel(n * (n + a), s, m, k - 1)
                for a in range(m + 1)), flint.acb(0))


def grouped_delta(s, sigma, cutoff=256):
    coeff = coefficients(s)
    tail = flint.arb(0)
    for j in range(6, 19):
        exponent = 4 * real(sigma) + j
        tail += coeff[j].abs_upper() * flint.arb(cutoff) ** (1 - exponent) / (exponent - 1)
    radius = real(Q(1, 9))
    exponent = 4 * real(sigma) + 19
    tail += cauchy_bound(s, 2, 2) / radius ** 19 / (1 - 1 / (radius * cutoff)) * flint.arb(cutoff) ** (1 - exponent) / (exponent - 1)
    finite = sum((real(g(n)) * recursive_kernel(n, s) for n in range(2, cutoff + 1) if g(n)), flint.acb(0))
    return finite, tail


def shifted_delta(s, sigma, degree=256):
    coeff = coefficients(s, degree=degree)
    prefix, radius = 15, real(Q(1, 9))
    out = sum((real(g(n)) * recursive_kernel(n, s) for n in range(2, prefix + 1) if g(n)), flint.acb(0))
    for j in range(6, degree + 1):
        z = 4 * s + j
        r = z.zeta().log() - sum((real(g(n)) * (-z * flint.arb(n).log()).exp()
                                for n in range(2, prefix + 1) if g(n)), flint.acb(0))
        out += coeff[j] * r
    ratio = 1 / (radius * (prefix + 1))
    tail = cauchy_bound(s, 2, 2) * flint.arb(prefix + 1) ** (-4 * real(sigma)) * ratio ** (degree + 1) / (1 - ratio)
    tail *= 1 + flint.arb(prefix + 1) / (4 * real(sigma) + degree)
    return out + box(tail)


@lru_cache(maxsize=None)
def profile(beta):
    return arithmetic_profile(beta, 6144)


def norm_bound():
    norm, prefix = flint.arb(0), 128
    for n in range(2, prefix + 1):
        if g(n):
            norm += real(g(n)) * sum((flint.arb(abs(weight)) / word_value(n, word)
                                     for word, weight, _ in interpolated(2, 2)), flint.arb(0))
    remainder = flint.acb(4).zeta().log().real
    remainder -= sum((real(g(n)) / n ** 4 for n in range(2, prefix + 1)), flint.arb(0))
    assert bool(remainder > 0)
    return norm + 16 * remainder


def actual_points(source):
    norm, records = norm_bound(), []
    for row in source['actual_zeta_ball_checks']:
        beta, sigma, height = Q(row['beta']), Q(row['s'][0]), row['s'][1]
        s = flint.acb(real(sigma), height)
        grouped, correction_tail = grouped_delta(s, sigma)
        reference = (real(beta) * (s.zeta().log() + grouped + box(correction_tail))).exp()
        finite = sum((real(x) * (-s * flint.arb(n).log()).exp() for n, x in enumerate(profile(beta)[1:], 1)), flint.acb(0))
        allowed = (1 + 1 / (real(sigma) - 1)) * flint.arb(6144) ** (1 - real(sigma)) * (real(beta) * norm).exp()
        perturbation = real(Q(1, 3)) * (-s * flint.arb(2).log()).exp()
        distance, corrupted = (finite - reference).abs_upper(), (finite + perturbation - reference).abs_lower()
        passed = bool(distance < allowed) and bool(corrupted > allowed)
        records.append({'beta': str(beta), 's': row['s'], 'arithmetic_cutoff': 6144,
                        'grouped_prime_power_reference_cutoff': 256, 'grouped_correction_tail_ball': short(correction_tail),
                        'difference_upper_ball': short(distance), 'independent_coefficient_tail_ball': short(allowed),
                        'smaller_perturbation_lower_ball': short(corrupted), 'all_passed': passed})
        print(f'Independent ordinary-root difference beta={beta}, s={row["s"]}: {passed}', flush=True)
    return records


def negative_checks(source):
    records = []
    for row in source['negative_grouped_domain_controls']['records']:
        sigma, height = Q(row['s'][0]), row['s'][1]
        s = flint.acb(real(sigma), height)
        reference = shifted_delta(s, sigma)
        finite, tail = grouped_delta(s, sigma, cutoff=768)
        distance = (finite - reference).abs_upper()
        corrupted = (finite + real(Q(1, 11)) * recursive_kernel(2, s) - reference).abs_lower()
        passed = bool(distance < tail) and bool(corrupted > tail)
        records.append({'s': row['s'], 'arithmetic_group_cutoff': 768, 'shift_degree': 256,
                        'prefix_removed': 15, 'difference_upper_ball': short(distance),
                        'independent_group_tail_ball': short(tail), 'smaller_perturbation_lower_ball': short(corrupted),
                        'ordinary_coefficient_series_claimed': False, 'all_passed': passed})
    return {'records': records, 'all_passed': all(x['all_passed'] for x in records)}


def roots(delta):
    records = []
    for beta, phase_size in ((Q(1, 2), flint.arb(2)), (Q(1, 4), flint.arb(2).sqrt()), (Q(1), flint.arb(0))):
        correction = (real(beta) * delta).exp()
        lower = correction.abs_lower()
        jump = phase_size * lower
        records.append({'beta': str(beta), 'nonzero_correction_lower_ball': short(lower),
                        'independent_monodromy_lower_ball': short(jump),
                        'all_passed': bool(lower > 0) and (bool(jump > 0) if beta != 1 else jump.is_zero())})
    return {'records': records,
            'phase_bound_scope': 'Bound for |(exp(2*pi*i*beta)-1)*C_beta|; the full H jump additionally includes zeta^beta',
            'all_passed': all(x['all_passed'] for x in records)}


def zero_checks(source):
    records = []
    for row in source['existing_actual_zero_new_operator_controls']['records']:
        radius, height = Q(row['radius']), row['disk_centre'][1]
        sigma = Q(1, 2) - radius
        region = flint.acb(real(Q(1, 2)) + flint.arb(0, real(radius)), flint.arb(height) + flint.arb(0, real(radius)))
        finite, tail = grouped_delta(region, sigma)
        checked = roots(finite + box(tail))
        records.append({'disk_centre': row['disk_centre'], 'grouped_correction_cutoff': 256,
                        'full_disk_grouped_infinite_tail_ball': short(tail), **checked})
    return {'records': records, 'all_passed': all(x['all_passed'] for x in records)}


def trivial_check(source):
    radius = Q(source['actual_trivial_zero_control']['radius'])
    large = Q(1, 8)
    region = flint.acb(-2 + flint.arb(0, real(large)), flint.arb(0, real(large)))
    maximum = region.zeta().abs_upper()
    ratio = real(radius / large)
    remainder = maximum * ratio ** 2 / (1 - ratio)
    slope = -flint.acb(3).zeta() / (4 * flint.arb.pi() ** 2)
    simple = bool(remainder < slope.abs_lower() * real(radius))
    distance = flint.arb(2).sqrt() * real(radius)
    rising = distance
    for j in (0, 1, 3, 4, 5):
        rising *= abs(j - 2) + distance
    bound = rising * (flint.acb(real(2 * (Q(-2) - radius) + 6)).zeta().real - 1)
    checked = roots(box(bound))
    from math import comb
    exact = all(sum((-1) ** (6 - a) * comb(6, a) * (n * (n + a)) ** 2 for a in range(7)) == 0 for n in range(2, 33))
    return {'disk_centre': ['-2', '0'], 'radius': str(radius), 'Cauchy_radius': str(large),
            'functional_equation_derivative_ball': short(slope), 'Cauchy_remainder_upper_ball': short(remainder),
            'simple_trivial_zero_independently_certified': simple, 'independent_integral_delta_bound_ball': short(bound),
            'exact_sixth_difference_negative_integer_annihilation': exact,
            **checked, 'all_passed': simple and exact and checked['all_passed']}


def native_tuple_negative_control():
    flint.ctx.cap = 7
    wrong = flint.acb_series([], 7)
    for _, weight, h in interpolated(2, 2):
        scalar_input = flint.acb_series(tuple(int(x) for x in h), 7)
        wrong += weight * (-scalar_input.log()).exp()
    return {'wrong_scalar_tuple_passes_vanished_terms_alone': all(wrong[j].contains(0) for j in range(6)),
            'correct_leading_coefficient_at_s_one': '40',
            'wrong_degree_six_coefficient': short(wrong[6]),
            'leading_coefficient_gate_rejects_scalar_tuple': not (wrong[6] - 40).contains(0)}


def main():
    started = time.monotonic()
    flint.ctx.prec = 2560
    source = json.loads((BASE / 'difference-results/difference_analytic.json').read_text())
    points, negative = actual_points(source), negative_checks(source)
    zeros, trivial = zero_checks(source), trivial_check(source)
    tuple_control = native_tuple_negative_control()
    checks = {'six_ordinary_root_bridges_and_smaller_perturbations': all(x['all_passed'] for x in points),
              'negative_grouped_domain_two_representations': negative['all_passed'],
              'both_actual_critical_zero_disks_keep_ordinary_root_monodromy': zeros['all_passed'],
              'actual_trivial_zero_and_sixth_difference_identity': trivial['all_passed'],
              'changed_cutoffs_and_independent_reference': all(x['arithmetic_cutoff'] != y['arithmetic_cutoff'] for x, y in zip(points, source['actual_zeta_ball_checks'])),
              'native_scalar_tuple_false_cancellation_rejected': tuple_control['wrong_scalar_tuple_passes_vanished_terms_alone'] and tuple_control['leading_coefficient_gate_rejects_scalar_tuple']}
    result = {'checks': checks, 'all_passed': all(checks.values()), 'actual_zeta_ball_checks': points,
              'negative_grouped_domain_controls': negative, 'existing_actual_zero_new_operator_controls': zeros,
              'actual_trivial_zero_control': trivial, 'no_production_imports': True, 'shared_trusted_kernel': 'FLINT/Arb',
              'native_tuple_negative_control': tuple_control,
              'proof': 'difference_proof.txt', 'elapsed_seconds': time.monotonic() - started}
    (BASE / 'difference-results/difference_analytic_verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Independent ordinary-root difference analytic audit: {sum(checks.values())}/{len(checks)}; elapsed={result["elapsed_seconds"]:.2f}s')
    assert result['all_passed']


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Independent joint-size audit: ordinary Fourier sums and divisor arithmetic.

No production helper is imported. Fejer weights are replaced by ordinary
partial sums, native hypergeometric resonances by elementary even-part
averaging, and arithmetic coefficients and all cutoffs are recomputed.
FLINT/Arb is the shared trusted numerical kernel.
"""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb, gcd
from pathlib import Path
import json
import time

import flint


BASE = Path(__file__).resolve().parent
FOURIER_DEGREE = 32
RESONANCE_CUTOFF = 40
ARITHMETIC_CUTOFF = 768


def real(value):
    value = Q(value)
    return flint.arb(value.numerator) / value.denominator


@lru_cache(maxsize=None)
def factors(n):
    result = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        result[n] = 1
    return result


def height(n, base):
    result = 0
    while n >= base:
        result += 1
        n //= base
    return result


@lru_cache(maxsize=None)
def divisors(n):
    result = [1]
    for p, e in factors(n).items():
        result = [d * p ** j for d in result for j in range(e + 1)]
    return sorted(result)


def root_coefficient(n):
    result = Q(1)
    for e in factors(n).values():
        result *= Q(comb(2 * e, e), 4 ** e)
    return result


def arithmetic_coefficients(b, c):
    g = [Q(0)] + [root_coefficient(n) for n in range(1, ARITHMETIC_CUTOFF + 1)]
    result = [Q(0)] * len(g)
    for n in range(1, len(g)):
        result[n] = sum((g[d] * g[n // d] for d in divisors(n)
                         if all(height(n, base) == height(d, base) + height(n // d, base)
                                for base in (b, c))), Q(0))
    return result


def ordinary_weights():
    result = {0: flint.acb(real(Q(1, 2)))}
    for m in range(1, FOURIER_DEGREE + 1):
        value = 1 / (2 * flint.arb.pi() * m)
        # These weights use PLUS vertical shifts, unlike the source evaluator.
        result[m] = flint.acb(0, -value)
        result[-m] = flint.acb(0, value)
    return result


def theta_partial(n, base):
    if n == base ** height(n, base):
        return flint.arb(0)
    angle = 2 * flint.arb.pi() * flint.arb(n).log() / flint.arb(base).log()
    return real(Q(1, 2)) - sum(((m * angle).sin() / m
                               for m in range(1, FOURIER_DEGREE + 1)), flint.arb(0)) / flint.arb.pi()


def resonance(s, base, doubled=False):
    if doubled:
        return 1 / (1 - (-s * flint.arb(base).log()).exp())
    data = factors(base)
    assert len(data) == 1
    p, exponent = next(iter(data.items()))
    z = (-s * flint.arb(p).log()).exp()
    if exponent == 1:
        return 1 / (1 - z).sqrt()
    assert exponent == 2, "This independent evaluator only needs prime and squared-prime bases"
    return (1 / (1 - z).sqrt() + 1 / (1 + z).sqrt()) / 2


def common_base(b, c):
    p, e = next(iter(factors(b).items()))
    r, f = next(iter(factors(c).items()))
    return p ** (e * f // gcd(e, f)) if p == r else None


def filtered_resonance(s, base, other):
    p, e = next(iter(factors(base).items()))
    coefficients = []
    for k in range(RESONANCE_CUTOFF + 1):
        degree = e * k
        coefficients.append(sum((real(Q(comb(2 * j, j) * comb(2 * (degree - j), degree - j), 4 ** degree))
                                 * theta_partial(p ** (degree - j), other)
                                 for j in range(degree + 1)), flint.arb(0)))
    z = (-s * flint.arb(base).log()).exp()
    value = flint.acb(0)
    for coefficient in reversed(coefficients):
        value = value * z + coefficient
    norm = real(Q(1, 2)) + real(sum((Q(1, m) for m in range(1, FOURIER_DEGREE + 1)), Q(0))) / flint.arb.pi()
    tail = norm * z.abs_upper() ** (RESONANCE_CUTOFF + 1) / (1 - z.abs_upper())
    return value, tail


def one_base_error(sigma, base):
    b = flint.arb(base)
    return b.sqrt() * b.log() / (2 * flint.arb.pi() * (FOURIER_DEGREE + 1)) * (
        real(sigma - 1).zeta() - 1 / (1 - b ** (1 - real(sigma))))


def ordinary_reference(s, sigma, b, c):
    assert bool(real(sigma).zeta().log() < flint.arb.pi())
    weights = ordinary_weights()
    tb, tc = (2 * flint.arb.pi() / flint.arb(base).log() for base in (b, c))
    grid = {(m, n): (s + flint.acb(0, m * tb + n * tc)).zeta().sqrt()
            for m, n in product(weights, repeat=2)}
    f = grid[0, 0]
    # Form diagonal multiplier operations directly, with midpoint corrections.
    projections_b = {n: resonance(s + flint.acb(0, n * tc), b) for n in weights}
    projections_c = {m: resonance(s + flint.acb(0, m * tb), c) for m in weights}
    ag = sum((v * grid[m, 0] for m, v in weights.items()), flint.acb(0)) - projections_b[0] / 2
    bg = sum((v * grid[0, n] for n, v in weights.items()), flint.acb(0)) - projections_c[0] / 2
    ap = sum((v * grid[m, 0] ** 2 for m, v in weights.items()), flint.acb(0)) - resonance(s, b, True) / 2
    bp = sum((v * grid[0, n] ** 2 for n, v in weights.items()), flint.acb(0)) - resonance(s, c, True) / 2
    common = common_base(b, c)
    rbc = resonance(s, common) if common else flint.acb(1)
    rbc2 = resonance(s, common, True) if common else flint.acb(1)
    cg = sum((v * z * grid[m, n] for m, v in weights.items() for n, z in weights.items()), flint.acb(0))
    cg -= sum((v * projections_c[m] for m, v in weights.items()), flint.acb(0)) / 2
    cg -= sum((v * projections_b[n] for n, v in weights.items()), flint.acb(0)) / 2
    cg += rbc / 4
    cp = sum((v * z * grid[m, n] ** 2 for m, v in weights.items() for n, z in weights.items()), flint.acb(0))
    cp -= sum((v * resonance(s + flint.acb(0, m * tb), c, True) for m, v in weights.items()), flint.acb(0)) / 2
    cp -= sum((v * resonance(s + flint.acb(0, n * tc), b, True) for n, v in weights.items()), flint.acb(0)) / 2
    cp += rbc2 / 4
    rb_h, tail_b = filtered_resonance(s, b, c)
    rc_h, tail_c = filtered_resonance(s, c, b)
    outer_a = sum((v * grid[m, 0] * (sum((z * grid[m, n] for n, z in weights.items()), flint.acb(0))
                                   - projections_c[m] / 2) for m, v in weights.items()), flint.acb(0)) - rb_h / 2
    outer_b = sum((v * grid[0, n] * (sum((z * grid[m, n] for m, z in weights.items()), flint.acb(0))
                                   - projections_b[n] / 2) for n, v in weights.items()), flint.acb(0)) - rc_h / 2
    value = f ** 2 - 2 * f * (ag + bg) + ap + bp + 2 * f * cg + 2 * ag * bg - 2 * outer_a - 2 * outer_b + cp
    norm = real(Q(1, 2)) + real(sum((Q(1, m) for m in range(1, FOURIER_DEGREE + 1)), Q(0))) / flint.arb.pi()
    kernel_norm = 1 + 3 * norm
    eb, ec = one_base_error(sigma, b), one_base_error(sigma, c)
    error = (2 * real(sigma).zeta().sqrt() + 1) * min(eb + kernel_norm * ec, ec + kernel_norm * eb)
    return value, error + tail_b + tail_c


def point_checks(source, arithmetic_source):
    profiles = {tuple(item['bases']): item for item in arithmetic_source['zeta_profiles']}
    records = []
    for item in source['actual_zeta_ball_checks']:
        b, c = item['bases']
        sigma, t = Q(item['s'][0]), item['s'][1]
        s = flint.acb(real(sigma), t)
        coefficients = arithmetic_coefficients(b, c)
        original = next(v['coefficients'] for v in profiles[b, c]['root_lifts'] if v['q'] == 2)
        prefix_equal = all(Q(v) == coefficients[n] for n, v in enumerate(original))
        finite = sum((real(v) * (-s * flint.arb(n).log()).exp()
                      for n, v in enumerate(coefficients[1:], 1)), flint.acb(0))
        reference, error = ordinary_reference(s, sigma, b, c)
        error += flint.arb(ARITHMETIC_CUTOFF) ** (1 - real(sigma)) / (real(sigma) - 1)
        difference = (finite - reference).abs_upper()
        # Use a smaller independent perturbation than the source (+1 versus +2).
        bad = (finite + (-s * flint.arb(2).log()).exp() - reference).abs_lower()
        passed = prefix_equal and bool(difference < error) and bool(bad > error)
        records.append({'bases': [b, c], 's': item['s'], 'arithmetic_cutoff': ARITHMETIC_CUTOFF,
                        'ordinary_Fourier_degree': FOURIER_DEGREE, 'resonance_cutoff': RESONANCE_CUTOFF,
                        'arithmetic_prefix_exactly_recomputed': prefix_equal,
                        'difference_upper_ball': str(difference), 'proved_infinite_error_ball': str(error),
                        'coefficient_2_perturbation': 1, 'perturbed_difference_lower_ball': str(bad),
                        'all_passed': passed})
        print(f'Independent joint zeta check {b},{c}, {item["s"]}: {passed}', flush=True)
    return records


def moment_checks(source):
    independent = []
    for item in source['actual_root_torus_moment_controls']['independent_records']:
        b, c = item['bases']
        eps = flint.arb(2) ** item['epsilon_power_of_two']
        a = real(Q(1, item['root_order']))
        modes = []
        # A larger mode box exercises different near-cancellations of frequencies.
        for m, n in product(range(-3, 4), repeat=2):
            if not (m or n):
                continue
            frequency = 2 * flint.arb.pi() * (m / flint.arb(b).log() + n / flint.arb(c).log())
            upper = eps ** a * flint.acb(1 + eps, frequency).zeta().abs_upper() ** a
            modes.append(bool(frequency.abs_lower() > 0) and bool(upper < real(Q(1, 10))))
        independent.append({'bases': [b, c], 'epsilon_power_of_two': item['epsilon_power_of_two'],
                            'root_order': item['root_order'], 'nonconstant_modes_checked': len(modes),
                            'all_modes_nonzero_and_moduli_below_one_tenth': all(modes)})
    dependent = []
    for item in source['actual_root_torus_moment_controls']['dependent_records']:
        b, c = item['bases']
        eps = flint.arb(2) ** item['epsilon_power_of_two']
        # Prove zero frequency by the integer relation, not floating cancellation.
        relation = c == b ** 2
        mass = (eps * (1 + eps).zeta()).sqrt()
        dependent.append(relation and bool(mass > real(Q(9, 10))))
    return {'independent_records': independent, 'dependent_controls_checked': len(dependent),
            'all_passed': all(v['all_modes_nonzero_and_moduli_below_one_tenth'] for v in independent) and all(dependent)}


def main():
    started = time.monotonic()
    flint.ctx.prec = 256
    source = json.loads((BASE / 'joint-results/joint_size_analytic.json').read_text())
    arithmetic_source = json.loads((BASE / 'joint-results/joint_size_search.json').read_text())
    points = point_checks(source, arithmetic_source)
    moments = moment_checks(source)
    correct = arithmetic_coefficients(2, 4)[4]
    wrong = correct - root_coefficient(4) / 2 - Q(1, 4)
    checks = {'six_fresh_actual_zeta_comparisons_and_smaller_perturbations': all(v['all_passed'] for v in points),
              'actual_root_torus_moduli_and_dependent_zero_frequency_controls': moments['all_passed'],
              'common_power_projection_shortcut_exactly_rejected': correct == Q(3, 4) and wrong == Q(5, 16),
              'independent_cutoffs_and_summation_method': all(v['ordinary_Fourier_degree'] != s['Fejer_degree']
                  and v['arithmetic_cutoff'] != s['arithmetic_cutoff'] for v, s in zip(points, source['actual_zeta_ball_checks']))}
    result = {'checks': checks, 'all_passed': all(checks.values()), 'actual_zeta_ball_checks': points,
              'actual_root_torus_moment_controls': moments, 'no_production_imports': True,
              'shared_trusted_kernel': 'FLINT/Arb', 'proof': 'joint_size_proof.txt',
              'elapsed_seconds': time.monotonic() - started}
    (BASE / 'joint-results/joint_size_analytic_verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Independent joint analytic audit: {sum(checks.values())}/{len(checks)}; elapsed={result["elapsed_seconds"]:.2f}s')
    assert result['all_passed']


if __name__ == '__main__':
    main()

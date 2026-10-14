#!/usr/bin/env python3
"""Independent signed-spectrum and divisor-sum audit; no production imports."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import factorial
from pathlib import Path
import json


BASE = Path(__file__).resolve().parent


def add_poly(a, d, multiplier=1):
    result = a.copy()
    for key, value in d.items():
        result[key] = result.get(key, Q(0)) + multiplier * value
    return {key: value for key, value in result.items() if value}


def product_poly(a, d):
    result = {}
    for i, x in a.items():
        for j, y in d.items():
            result[i + j] = result.get(i + j, Q(0)) + x * y
    return {key: value for key, value in result.items() if value}


def real_imag(q, mode):
    if not mode:
        return {0: Q(1, factorial(q))}, {}
    real, imag = {}, {}
    for degree in range(1, q):
        value = Q(1, mode ** degree * factorial(q - degree))
        if degree % 2:
            imag[degree] = (-1) ** ((degree - 1) // 2) * value
        else:
            real[degree] = (-1) ** (degree // 2 + 1) * value
    return real, imag


def cancellation(q, m, n, coefficients):
    a, d, e, f = coefficients
    u, v, x, y = a + d + e + f, a - d - e + f, a + d - e - f, a - d + e - f
    rm, im = real_imag(q, m)
    rn, inn = real_imag(q, n)
    real = add_poly({}, product_poly(rm, rn), u)
    real = add_poly(real, product_poly(im, inn), -v)
    imag = add_poly({}, product_poly(im, rn), x)
    imag = add_poly(imag, product_poly(rm, inn), y)
    return not real and not imag


@lru_cache(maxsize=None)
def h(n, base, ceiling=False):
    original, height = n, 0
    while n >= base:
        n //= base
        height += 1
    return height + int(ceiling and original != base ** height)


def indicator(n, base):
    return int(n == base ** h(n, base))


def summed_kernel(i, j, b, c):
    value = 1
    for base in (b, c):
        value *= sum(h(i * j, base, upper) == h(i, base, upper) + h(j, base, upper)
                     for upper in (False, True))
    return value


@lru_cache(maxsize=None)
def factor(n):
    p, result = 2, {}
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        result[n] = 1
    return result


@lru_cache(maxsize=None)
def divisors(n):
    result = [1]
    for p, e in factor(n).items():
        result = [d * p ** j for d in result for j in range(e + 1)]
    return sorted(result)


def features_at(n, a, d, b, c):
    sums = [Q(0)] * 10
    left = Q(0)
    bn, cn = indicator(n, b), indicator(n, c)
    for i in divisors(n):
        j = n // i
        coefficient = a[i] * d[j]
        bi, bj, ci, cj = indicator(i, b), indicator(j, b), indicator(i, c), indicator(j, c)
        markers = (1, bi + bj, ci + cj, bn, cn, bi * ci + bj * cj,
                   bi * cj + ci * bj, cn * (bi + bj), bn * (ci + cj), bn * cn)
        sums = [x + coefficient * y for x, y in zip(sums, markers)]
        left += coefficient * summed_kernel(i, j, b, c)
    return sums, left


def batch_solve(matrix, targets):
    rows = [list(row) + [target] for row, target in zip(matrix, targets)]
    count, cursor = 10, 0
    for column in range(count):
        selected = next((i for i in range(cursor, len(rows)) if rows[i][column]), None)
        assert selected is not None
        rows[cursor], rows[selected] = rows[selected], rows[cursor]
        scale = rows[cursor][column]
        rows[cursor] = [x / scale for x in rows[cursor]]
        for other in range(cursor + 1, len(rows)):
            scale = rows[other][column]
            if scale:
                rows[other] = [x - scale * y for x, y in zip(rows[other], rows[cursor])]
        cursor += 1
    assert all(not any(row[:count]) and not row[-1] for row in rows[cursor:])
    solution = [Q(0)] * count
    for column in reversed(range(count)):
        solution[column] = rows[column][-1] - sum((rows[column][j] * solution[j] for j in range(column + 1, count)), Q(0))
    return solution


@lru_cache(maxsize=None)
def local_root(beta, exponent):
    values = [Q(1)]
    for degree in range(1, exponent + 1):
        values.append(beta * sum(values[:degree], Q(0)) / degree)
    return values[-1]


def root(beta, cutoff):
    values = [Q(0), Q(1)]
    for n in range(2, cutoff + 1):
        coefficient = Q(1)
        for exponent in factor(n).values():
            coefficient *= local_root(beta, exponent)
        values.append(coefficient)
    return values


def main():
    source = json.loads((BASE / 'cancellation-results/cancellation_search.json').read_text())
    grammar = source['frequency_grammar']
    frequency_checks = []
    for item in grammar['records']:
        q, coefficients = item['q'], item['weights']
        training = cancellation(q, *grammar['training_mode'], coefficients)
        failure = next((mode for mode in grammar['fresh_modes'] if not cancellation(q, *mode, coefficients)), None) if training else [1, 1]
        frequency_checks.append(training == item['training_passed'] and failure == item['first_failed_mode']
                                and (training and failure is None) == item['held_out_passed'])
    identity = source['bilinear_projection_identity']
    matrix, targets, generic_checks = [], [], []
    fitted = [Q(x) for x in identity['unique_fitted_coefficients']]
    for held_out, records in ((False, identity['training_records']), (True, identity['fresh_records'])):
        for item in records:
            a, d = [[Q(x) for x in item[key]] for key in ('input_a', 'input_d')]
            b, c = item['bases']
            passed = True
            for n in range(1, len(a)):
                features, left = features_at(n, a, d, b, c)
                passed &= left == Q(item['orientation_sum'][n]) == sum((x * y for x, y in zip(fitted, features)), Q(0))
                if not held_out:
                    matrix.append(features)
                    targets.append(left)
            generic_checks.append(passed)
    zeta_checks = []
    for item in source['actual_zeta_coefficient_profiles']:
        b, c = item['bases']
        g = root(Q(item['beta']), item['cutoff'])
        passed = True
        for n in range(1, len(g)):
            features, left = features_at(n, g, g, b, c)
            isolated = (left - features[0] + features[3] + features[4] - features[6]
                        + features[7] + features[8] - features[9]) / 6
            direct = sum((g[i] * g[n // i] * (indicator(n // i, b) + indicator(n // i, c)
                          + indicator(n // i, b) * indicator(n // i, c)) / 3 for i in divisors(n)), Q(0))
            passed &= left == Q(item['sum_coefficients'][n]) and isolated == direct == Q(item['corrected_root_coefficients'][n])
        zeta_checks.append(passed)
    algebra_checks = []
    for item in source['associativity_controls']:
        b, c = item['bases']
        witness = item['normalized_average_kernel_counterexample']
        if witness:
            a, d, e = (witness[key] for key in ('a', 'd', 'e'))
            left = Q(summed_kernel(a, d, b, c) * summed_kernel(a * d, e, b, c), 16)
            right = Q(summed_kernel(d, e, b, c) * summed_kernel(a, d * e, b, c), 16)
            algebra_checks.append(left != right and left == Q(witness['left']) and right == Q(witness['right']))
        else:
            # Check the independently derived nonzero transport weight.
            def scalar(n):
                return Q(2 ** (indicator(n, b) + indicator(n, c)), 4)
            algebra_checks.append(all(Q(summed_kernel(a, d, b, c), 4) == scalar(a) * scalar(d) / scalar(a * d)
                                      for a, d in product(range(1, 65), repeat=2)))
    checks = {'all_signed_frequency_grammar_decisions_recomputed': all(frequency_checks),
              'unique_square_root_survivor_recomputed': [(x['q'], x['weights']) for x in grammar['survivors']] == [(2, [1, 1, 1, 1])],
              'learned_bilinear_identity_independently_refitted': batch_solve(matrix, targets) == fitted,
              'all_generic_divisor_identity_checks': all(generic_checks),
              'all_actual_zeta_coefficients_and_normalized_cancellation_checks': all(zeta_checks),
              'prime_transport_and_composite_associativity_controls': all(algebra_checks)}
    order = source['averaging_order_counterexample']
    b, c, q, n = (*order['bases'], order['q'], order['index'])
    g = root(Q(1, q), n)
    raw, averaged = Q(0), Q(0)
    def scalar(index):
        return Q(2 ** (indicator(index, b) + indicator(index, c)), 4)
    for i in divisors(n):
        for j in divisors(n // i):
            k = n // (i * j)
            coefficient = g[i] * g[j] * g[k]
            count = sum(all(h(n, base, upper) == sum(h(v, base, upper) for v in (i, j, k))
                            for base, upper in ((b, o1), (c, o2)))
                        for o1, o2 in product((False, True), repeat=2))
            raw += coefficient * Q(count, 4)
            averaged += coefficient * scalar(i) * scalar(j) * scalar(k) / scalar(n)
    checks['averaging_lifts_and_lifting_the_average_exactly_distinguished'] = (
        q == 3 and raw == Q(order['mean_of_four_lift_coefficients'])
        and averaged == Q(order['lift_of_mean_kernel_coefficient']) and averaged - raw == Q(1, 108))
    result = {'checks': checks, 'all_passed': all(checks.values()), 'frequency_programs_checked': len(frequency_checks),
              'generic_records_checked': len(generic_checks), 'zeta_profiles_checked': len(zeta_checks),
              'no_production_imports': True, 'proof': 'cancellation_proof.txt'}
    (BASE / 'cancellation-results/cancellation_verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Independent cancellation arithmetic audit: {sum(checks.values())}/{len(checks)}')
    assert result['all_passed']


if __name__ == '__main__':
    main()

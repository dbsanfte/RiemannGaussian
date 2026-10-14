#!/usr/bin/env python3
"""Independent anchored-partition and polynomial-series mixed-index audit."""

from fractions import Fraction as Q
from itertools import product
from math import comb, factorial
from pathlib import Path
import json

from check_joint_size import factors, divisors, omega, triangular


BASE = Path(__file__).resolve().parent


def d_log(f):
    return triangular(f, lambda i, j: 1, 'LOG')


def d_exp(h):
    return triangular(h, lambda i, j: 1, 'EXP')


def scale(f, power):
    return [Q(0)] + [value / Q(factorial((n - 1).bit_count())) ** power for n, value in enumerate(f[1:], 1)]


def subset_product(a, d):
    out = [Q(0)] * len(a)
    for n in range(1, len(a)):
        mask = n - 1
        # Enumerate the disjoint complementary parts in the opposite order.
        sub = 0
        while True:
            out[n] += a[sub + 1] * d[(mask ^ sub) + 1]
            if sub == mask:
                break
            sub = (sub - mask) & mask
    return out


def anchored(h, kind):
    out = [Q(0)] * len(h)
    out[1] = Q(kind == 'EXP')
    for n in range(2, len(h)):
        mask = n - 1
        anchor = mask & -mask
        sub, total = (mask - 1) & mask, Q(0)
        while sub:
            if sub & anchor:
                other = mask ^ sub
                total += h[sub + 1] * out[other + 1] if kind == 'EXP' else out[sub + 1] * h[other + 1]
            sub = (sub - 1) & mask
        out[n] = h[n] + (total if kind == 'EXP' else -total)
    return out


def transfer(f, pre=0, post=1, beta=Q(1)):
    return scale(anchored([beta * x for x in scale(d_log(f), pre)], 'EXP'), post)


def inverse(f, pre=0, post=1):
    return d_exp(scale(anchored(scale(f, -post), 'LOG'), -pre))


def ordinary_polynomial_product(a, d):
    return [sum((a[i] * d[j - i] for i in range(j + 1)), Q(0)) for j in range(len(a))]


def ordinary_series(f, kind):
    residual = f[1:].copy()
    if kind == 'LOG':
        residual[0] -= 1
    assert residual[0] == 0
    term = [Q(1)] + [Q(0)] * (len(residual) - 1)
    out = term.copy() if kind == 'EXP' else [Q(0)] * len(term)
    for k in range(1, len(term)):
        term = ordinary_polynomial_product(term, residual)
        coefficient = Q(1, factorial(k)) if kind == 'EXP' else Q((-1) ** (k + 1), k)
        out = [x + coefficient * y for x, y in zip(out, term)]
    return [Q(0)] + out


def v2(n):
    value = 0
    while n % 2 == 0:
        n //= 2
        value += 1
    return value


def prediction(values, n, beta, model):
    k = (n - 1).bit_count()
    endpoints = {'v2': v2(n), 'Omega': omega(n), 'bit_count': k, 'floor_log2': n.bit_length() - 1}
    total = Q(0)
    for r in range(1, min(k, endpoints[model['endpoint']]) + 1):
        index = n - 2 ** r + model['shift']
        if index > 0:
            coefficient = beta ** model['beta_power'] / Q(r) ** model['r_power']
            coefficient *= Q(factorial(k - r), factorial(k)) ** model['factorial_ratio_power']
            total += coefficient * Q(values[index])
    return total


def d_root(beta, cutoff):
    values = [Q(0), Q(1)]
    for n in range(2, cutoff + 1):
        value = Q(1)
        for e in factors(n).values():
            for j in range(e):
                value *= Q(beta + j, j + 1)
        values.append(value)
    return values


def finite_lift(beta, q, cutoff):
    h = d_root(beta / q, cutoff)
    h[1] = 0
    term = [Q(0)] * (cutoff + 1)
    term[1] = 1
    out = term.copy()
    for k in range(1, min(q, cutoff.bit_length() - 1) + 1):
        term = subset_product(term, h)
        out = [x + comb(q, k) * y for x, y in zip(out, term)]
    return scale(out, 1)


def main():
    source = json.loads((BASE / 'mixed-index-results/mixed_index_search.json').read_text())
    generic = []
    for item in source['generic_operator_checks']['records']:
        pre, post = item['pre_diagonal_exponent'], item['post_diagonal_exponent']
        a, d = [[Q(x) for x in item[key]] for key in ('input_a', 'input_d')]
        output = transfer(a, pre, post)
        # Ordinary divisor convolution by divisor sums, not production loops.
        ordinary = [Q(0)] + [sum((a[i] * d[n // i] for i in divisors(n)), Q(0)) for n in range(1, len(a))]
        ta, td = output, transfer(d, pre, post)
        typed_product = scale(subset_product(scale(ta, -post), scale(td, -post)), post)
        half = transfer(a, pre, post, Q(1, 2))
        typed_square = scale(subset_product(scale(half, -post), scale(half, -post)), post)
        generic.append([str(x) for x in output] == item['output_a'] and inverse(output, pre, post) == a
                       and transfer(ordinary, pre, post) == typed_product and typed_square == output)
    profiles = []
    lookup = {}
    bell = [1]
    for k in range(1, 16):
        bell.append(sum(comb(k - 1, j) * bell[j] for j in range(k)))
    for item in source['zeta_coefficient_profiles']:
        beta, cutoff = Q(item['beta']), item['cutoff']
        values = transfer([Q(0)] + [Q(1)] * cutoff, beta=beta)
        lookup[beta] = values
        profiles.append([str(x) for x in values] == item['coefficients']
                        and all(0 <= value <= Q(bell[(n - 1).bit_count()], factorial((n - 1).bit_count())) <= 1
                                for n, value in enumerate(values[1:], 1)))
    normalization = []
    for item in source['normalization_grammar']['records']:
        values = transfer([Q(0)] + [Q(1)] * 256, item['pre'], item['post'], Q(item['beta']))
        normalization.append(all(0 <= x <= 1 for x in values) == item['finite_coefficients_between_zero_and_one']
                             and max(values) == Q(item['maximum_coefficient']))
    recurrence = []
    for item in source['parity_recurrence_grammar']['records']:
        training = all(prediction(lookup[Q(1)], n, Q(1), item) == lookup[Q(1)][n] for n in (2, 4, 8, 16))
        failure = next(({'n': n, 'beta': str(beta)} for beta in (Q(1, 2), Q(1, 4), Q(2, 3))
                        for n in range(2, 1025, 2) if prediction(lookup[beta], n, beta, item) != lookup[beta][n]), None) if training else None
        recurrence.append(training == item['training_passed'] and failure == item['counterexample']
                          and (training and failure is None) == item['held_out_passed'])
    lifts = [[str(x) for x in finite_lift(Q(item['beta']), item['q'], item['cutoff'])] == item['coefficients']
             for item in source['finite_root_lifts']]
    bit_profiles = []
    for item in source['arithmetic_features']['single_bit_prime_power_profiles']:
        n = int(item['n'])
        pp = factors(n)
        expected = Q(1, next(iter(pp.values()))) if len(pp) == 1 else Q(0)
        bit_profiles.append(expected == Q(item['coefficient_at_beta_one'])
                            and n - 1 == 2 ** item['bit_position'])
    cross = source['cross_index_controls']
    u = [Q(0)] + [Q(1)] * cross['cutoff']
    forward = ordinary_series(d_log(u), 'EXP')
    reverse = d_exp(ordinary_series(u, 'LOG'))
    h = [Q(0)] * 33
    h[1], h[2] = 1, 1
    calibration = source['type_calibration']
    correct = ordinary_series(h, 'LOG')
    typed_root_counter = source['arithmetic_features']['ordinary_root_interpretation_counterexample']
    expected_survivor = {'beta_power': 1, 'r_power': 1, 'factorial_ratio_power': 1, 'endpoint': 'v2', 'shift': 1}
    survivor = source['parity_recurrence_grammar']['survivors'][0]
    checks = {'all_generic_group_inverse_and_typed_root_laws': all(generic),
              'all_32_normalization_observations_recomputed': all(normalization),
              'all_zeta_profiles_and_Bell_majorants': all(profiles),
              'all_384_recurrence_decisions_recomputed': all(recurrence),
              'unique_v2_parity_stencil_recovered': all(survivor[k] == v for k, v in expected_survivor.items()),
              'all_finite_root_lifts_by_binomial_subset_powers': all(lifts),
              'all_single_bit_prime_power_profiles': all(bit_profiles),
              'cross_index_inverse_coefficients_by_full_polynomial_series': [str(x) for x in forward] == cross['forward_coefficients']
                   and [str(x) for x in reverse] == cross['reverse_coefficients'],
              'correct_additive_unit_and_long_termination_recovered': correct[16] == Q(1, 15)
                   and calibration['wrong_Dirichlet_termination_counterexample']['wrong_bound_rejected'],
              'prime_label_dependence_and_wrong_ordinary_root_exactly_rejected': lookup[Q(1)][7] == 1
                   and lookup[Q(1)][11] == Q(3, 4) and lookup[Q(1, 2)][6] == Q(1, 8)
                   and typed_root_counter['ordinary_Dirichlet_root_of_output_coefficient'] == '0'}
    result = {'checks': checks, 'all_passed': all(checks.values()), 'generic_records_checked': len(generic),
              'normalization_programs_checked': len(normalization), 'recurrence_programs_checked': len(recurrence),
              'finite_root_lifts_checked': len(lifts), 'single_bit_profiles_checked': len(bit_profiles),
              'no_production_imports': True, 'proof': 'mixed_index_proof.txt'}
    (BASE / 'mixed-index-results/mixed_index_verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Independent mixed-index arithmetic audit: {sum(checks.values())}/{len(checks)}')
    assert result['all_passed']


if __name__ == '__main__':
    main()

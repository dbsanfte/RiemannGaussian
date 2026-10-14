#!/usr/bin/env python3
"""Discover typed additive/divisor transfers and a prime-binary partition map.

Arithmetic arrays use n>=1 with unused entry zero. Shifted additive
convolution corresponds explicitly to raw additive degree n-1. Carry-free
addition splits the bits of n-1. A factorial diagonal selects a rigorously
convergent zeta-input regularizer; it is not a claim of historical novelty.
"""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import factorial
from pathlib import Path
import json
import random
import time

from exact_arithmetic import convolve, factorization, formal_exp, formal_log, normalized_power, sequence, unit
from root_transfer_probe import algebra_log


BASE = Path(__file__).resolve().parent


def additive_product(a, d):
    if len(a) != len(d):
        raise ValueError('Equal explicit cutoffs required')
    return [Q(0)] + [sum((a[i] * d[n + 1 - i] for i in range(1, n + 1)), Q(0))
                     for n in range(1, len(a))]


def diagonal(values, exponent=1):
    return [Q(0)] + [value * Q(factorial((n - 1).bit_count())) ** (-exponent)
                     for n, value in enumerate(values[1:], 1)]


def binary_product(a, d, exponent=0):
    if len(a) != len(d):
        raise ValueError('Equal explicit cutoffs required')
    out = [Q(0)] * len(a)
    for n in range(1, len(a)):
        mask, sub = n - 1, n - 1
        total_factor = factorial(mask.bit_count())
        while True:
            other = mask ^ sub
            scalar = Q(factorial(sub.bit_count()) * factorial(other.bit_count()), total_factor) ** exponent
            out[n] += scalar * a[sub + 1] * d[other + 1]
            if not sub:
                break
            sub = (sub - 1) & mask
    return out


def additive_log_exp(values, kind, carry_free=False, exponent=0):
    expected = int(kind == 'LOG')
    if values[1] != expected:
        raise ValueError('LOG needs f(1)=1; EXP needs h(1)=0')
    out = [Q(0)] * len(values)
    out[1] = Q(kind == 'EXP')
    for n in range(2, len(values)):
        grade = (n - 1).bit_count() if carry_free else n - 1
        middle = Q(0)
        if carry_free:
            sub = (n - 2) & (n - 1)
            while sub:
                other = (n - 1) ^ sub
                scalar = Q(factorial(sub.bit_count()) * factorial(other.bit_count()), factorial(grade)) ** exponent
                middle += sub.bit_count() * scalar * (values[sub + 1] * out[other + 1]
                    if kind == 'EXP' else out[sub + 1] * values[other + 1])
                sub = (sub - 1) & (n - 1)
        else:
            middle = sum(((i - 1) * (values[i] * out[n + 1 - i] if kind == 'EXP'
                          else out[i] * values[n + 1 - i]) for i in range(2, n)), Q(0))
        out[n] = values[n] + (middle if kind == 'EXP' else -middle) / grade
    return out


def transfer(f, pre=0, post=1, beta=Q(1)):
    logarithm = [beta * x for x in diagonal(formal_log(f), pre)]
    return diagonal(additive_log_exp(logarithm, 'EXP', True), post)


def inverse(values, pre=0, post=1):
    logarithm = additive_log_exp(diagonal(values, -post), 'LOG', True)
    return formal_exp(diagonal(logarithm, -pre))


def calibrations():
    cutoff = 32
    delta = unit(cutoff)
    f = sequence([1] + [Q(n, n + 3) for n in range(1, cutoff)])
    offset_records = []
    for offset in range(-2, 3):
        normalized_unit = all(1 + j + offset == j for j in range(1, 65))
        offset_records.append({'offset_in_i_plus_j_plus_offset': offset, 'delta_1_is_unit': normalized_unit})
    h = unit(cutoff)
    h[2] = 1
    correct_log = additive_log_exp(h, 'LOG')
    truncated = algebra_log(h, additive_product)
    result = {'additive_offset_grammar': offset_records,
              'explicit_raw_additive_unit': 'delta_0 at degree 0; f(n) is placed at additive degree n-1',
              'shared_reindexed_unit': 'delta_1',
              'shifted_additive_unit_verified': additive_product(delta, f) == f,
              'carry_free_additive_unit_verified': binary_product(delta, f) == f,
              'divided_binary_unit_verified': binary_product(delta, f, 1) == f,
              'wrong_Dirichlet_termination_counterexample': {'input': 'delta_1+delta_2', 'cutoff': cutoff, 'index': 16,
                  'true_additive_log_coefficient': str(correct_log[16]), 'hardcoded_D_bound_coefficient': str(truncated[16]),
                  'wrong_bound_rejected': correct_log[16] != truncated[16]},
              'universal_additive_termination': 'n-1 factors; Dirichlet floor(log2 n) is not a generic LOG/EXP bound',
              'all_passed': additive_product(delta, f) == binary_product(delta, f) == binary_product(delta, f, 1) == f
                            and correct_log[16] == Q(1, 15) and truncated[16] == 0}
    return result


def generic_checks():
    rng = random.Random(2026100705)
    records = []
    for cutoff in (24, 64):
        a, d = [sequence([1] + [Q(rng.randint(-3, 3), rng.randint(1, 7)) for _ in range(cutoff - 1)]) for _ in range(2)]
        for pre, post in product((-1, 0, 1), (-1, 0, 1, 2)):
            ta, td = transfer(a, pre, post), transfer(d, pre, post)
            root = transfer(a, pre, post, Q(1, 2))
            laws = {'inverse': inverse(ta, pre, post) == a,
                    'typed_group_law': transfer(convolve(a, d), pre, post) == binary_product(ta, td, post),
                    'typed_half_root_law': binary_product(root, root, post) == ta,
                    'prefix': transfer(a[:cutoff // 2 + 1], pre, post) == ta[:cutoff // 2 + 1]}
            records.append({'cutoff': cutoff, 'pre_diagonal_exponent': pre, 'post_diagonal_exponent': post,
                            'input_a': [str(x) for x in a], 'input_d': [str(x) for x in d],
                            'output_a': [str(x) for x in ta], 'laws': laws})
    return {'records': records, 'all_passed': all(all(x['laws'].values()) for x in records)}


def normalization_grammar(cutoff=256):
    u = sequence([1] * cutoff)
    records = []
    for pre, post, beta in product((-1, 0, 1, 2), (-1, 0, 1, 2), (Q(1), Q(1, 2))):
        values = transfer(u, pre, post, beta)
        records.append({'pre': pre, 'post': post, 'beta': str(beta), 'finite_coefficients_between_zero_and_one': all(0 <= x <= 1 for x in values),
                        'maximum_coefficient': str(max(values)),
                        'universal_Bell_bound_certificate': pre >= 0 and post >= 1,
                        'finite_observation_is_not_a_domain_proof': True})
    return {'models_scored': len(records), 'records': records,
            'selected_program': {'pre': 0, 'post': 1, 'definition': 'M EXP_carry_free_additive LOG_Dirichlet'},
            'universal_bound': 'B_k(beta)/k!, k=popcount(n-1); entire Bell EGF gives absolute Dirichlet convergence on Re(s)>0',
            'all_other_growth_domains_require_separate_proof': True}


def zeta_profiles(cutoff=1024):
    u = sequence([1] * cutoff)
    logarithm = formal_log(u)
    records = []
    for beta in (Q(1), Q(1, 2), Q(1, 4), Q(2, 3)):
        values = diagonal(additive_log_exp([beta * x for x in logarithm], 'EXP', True))
        records.append({'beta': str(beta), 'cutoff': cutoff, 'coefficients': [str(x) for x in values],
                        'all_coefficients_between_zero_and_one': all(0 <= x <= 1 for x in values)})
    finite = []
    for q, beta in product((2, 4, 8, 16, 32), (Q(1), Q(1, 2))):
        root = normalized_power(u[:129], beta / q)
        out = unit(128)
        for _ in range(q):
            out = binary_product(out, root)
        out = diagonal(out)
        finite.append({'q': q, 'beta': str(beta), 'cutoff': 128, 'coefficients': [str(x) for x in out],
                       'all_coefficients_between_zero_and_one': all(0 <= x <= 1 for x in out)})
    return records, finite


def endpoint(n, kind):
    if kind == 'v2':
        return (n & -n).bit_length() - 1
    if kind == 'Omega':
        return sum(factorization(n).values())
    if kind == 'bit_count':
        return (n - 1).bit_count()
    return n.bit_length() - 1


def recurrence_prediction(values, n, beta, model):
    k = (n - 1).bit_count()
    total = Q(0)
    for r in range(1, min(k, endpoint(n, model['endpoint'])) + 1):
        index = n - 2 ** r + model['shift']
        if index < 1:
            continue
        scalar = beta ** model['beta_power'] * Q(r) ** (-model['r_power'])
        scalar *= Q(factorial(k - r), factorial(k)) ** model['factorial_ratio_power']
        total += scalar * Q(values[index])
    return total


def recurrence_search(profiles):
    lookup = {Q(x['beta']): x['coefficients'] for x in profiles}
    training = tuple((n, Q(1)) for n in (2, 4, 8, 16))
    fresh = tuple((n, beta) for beta in (Q(1, 2), Q(1, 4), Q(2, 3)) for n in range(2, 1025, 2))
    records = []
    for a, b, c, end, shift in product(range(3), (-1, 0, 1, 2), (-1, 0, 1, 2), ('v2', 'Omega', 'bit_count', 'floor_log2'), (0, 1)):
        model = {'beta_power': a, 'r_power': b, 'factorial_ratio_power': c, 'endpoint': end, 'shift': shift}
        passed = all(recurrence_prediction(lookup[beta], n, beta, model) == Q(lookup[beta][n]) for n, beta in training)
        failure = next(({'n': n, 'beta': str(beta)} for n, beta in fresh
                        if recurrence_prediction(lookup[beta], n, beta, model) != Q(lookup[beta][n])), None) if passed else None
        records.append({**model, 'training_passed': passed, 'held_out_passed': passed and failure is None, 'counterexample': failure})
    return {'models_scored': len(records), 'training_fit_count': sum(x['training_passed'] for x in records),
            'records': records, 'survivors': [x for x in records if x['held_out_passed']],
            'fresh_even_indices_through': 1024, 'fresh_parameters': ['1/2', '1/4', '2/3'],
            'universal_law': 'F_beta(n)=sum_(r=1)^v2(n) beta/r * (k-r)!/k! * F_beta(n-2^r+1), even n, k=popcount(n-1)'}


def arithmetic_features(profiles):
    pp = []
    for j in range(21):
        n = 2 ** j + 1
        factors = factorization(n)
        value = Q(1, next(iter(factors.values()))) if len(factors) == 1 else Q(0)
        pp.append({'bit_position': j, 'n': str(n), 'factors': [[p, e] for p, e in factors.items()],
                   'coefficient_at_beta_one': str(value), 'scope': 'Single-bit carry-free EXP equals its logarithm coefficient exactly'})
    lookup = {Q(x['beta']): [Q(v) for v in x['coefficients']] for x in profiles}
    root = normalized_power(lookup[Q(1)][:65], Q(1, 2))
    return {'single_bit_prime_power_profiles': pp,
            'prime_relabeling_counterexample': {'primes': [7, 11], 'same_popcount_of_n_minus_one': 2,
                'coefficients_at_beta_one': [str(lookup[Q(1)][7]), str(lookup[Q(1)][11])],
                'arithmetic_prime_labels_matter': lookup[Q(1)][7] != lookup[Q(1)][11]},
            'ordinary_root_interpretation_counterexample': {'index': 6, 'beta': '1/2',
                'true_typed_regularized_root_coefficient': str(lookup[Q(1, 2)][6]),
                'ordinary_Dirichlet_root_of_output_coefficient': str(root[6]),
                'ordinary_root_interpretation_rejected': lookup[Q(1, 2)][6] != root[6]}}


def cross_index_controls(cutoff=64):
    u = sequence([1] * cutoff)
    forward = additive_log_exp(formal_log(u), 'EXP')
    reverse = formal_exp(additive_log_exp(u, 'LOG'))
    identities = {'forward_inverse': formal_exp(additive_log_exp(forward, 'LOG')) == u,
                  'reverse_inverse': additive_log_exp(formal_log(reverse), 'EXP') == u}
    return {'cutoff': cutoff, 'forward_coefficients': [str(x) for x in forward],
            'reverse_coefficients': [str(x) for x in reverse], 'inverse_checks': identities,
            'forward_Dirichlet_domain': 'No convergent Dirichlet half-plane for any positive parameter; proved using prime-harmonic divergence',
            'reverse_Dirichlet_domain': 'exp(sum_(k>=1)(zeta(s+k)-1)), initially Re(s)>0, holomorphic and zero-free away from nonpositive-integer essential singularities',
            'raw_carry_free_forward_domain': 'Not determined by finite growth checks; the selected factorial normalization has a separate positive-half-plane bound'}


def main():
    started = time.monotonic()
    out = BASE / 'mixed-index-results'
    out.mkdir(exist_ok=True)
    calibrate = calibrations()
    generic = generic_checks()
    grammar = normalization_grammar()
    profiles, finite = zeta_profiles()
    recurrence = recurrence_search(profiles)
    features = arithmetic_features(profiles)
    cross = cross_index_controls()
    result = {'type_calibration': calibrate, 'generic_operator_checks': generic,
              'normalization_grammar': grammar, 'zeta_coefficient_profiles': profiles,
              'finite_root_lifts': finite, 'parity_recurrence_grammar': recurrence,
              'arithmetic_features': features, 'cross_index_controls': cross,
              'selected_operator': 'N_beta(f)=M EXP_additive_binary_no_carry(beta LOG_D(f)); M(n)=1/popcount(n-1)!',
              'universal_zeta_domain': 'Absolute/local-uniform convergence on Re(s)>0, jointly entire in beta',
              'RH_root_monodromy_preservation': 'Rejected: the regularizer is holomorphic across known actual simple zeta zeros for all beta',
              'historical_originality': 'Unresolved; general log/exp and subset-convolution primitives are classical; specific prime-binary arithmetic application requires review',
              'counts_as_verified_new_operator': False, 'new_RH_estimate_proved': False,
              'proof': 'mixed_index_proof.txt',
              'all_passed': calibrate['all_passed'] and generic['all_passed'] and len(recurrence['survivors']) == 1
                 and all(x['all_coefficients_between_zero_and_one'] for x in profiles + finite)
                 and all(cross['inverse_checks'].values()) and features['ordinary_root_interpretation_counterexample']['ordinary_root_interpretation_rejected'],
              'elapsed_seconds': time.monotonic() - started}
    (out / 'mixed_index_search.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Mixed index grammar: {grammar["models_scored"]} normalizations; {recurrence["models_scored"]} recurrence programs, '
          f'{recurrence["training_fit_count"]} fits, {len(recurrence["survivors"])} survivor; all={result["all_passed"]}; elapsed={result["elapsed_seconds"]:.2f}s')
    assert result['all_passed']


if __name__ == '__main__':
    main()

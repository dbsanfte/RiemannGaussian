#!/usr/bin/env python3
"""Search ordinary-root-sensitive quadratic index differences and their laws."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb, gcd
from pathlib import Path
import json
import random
import time

from exact_arithmetic import convolve, formal_exp, formal_log, normalized_power, sequence


BASE = Path(__file__).resolve().parent


def weights(m):
    return [(-1) ** (m - a) * comb(m, a) for a in range(m + 1)]


def difference(values, m, iterations=1):
    if values[1] != 0:
        raise ValueError('Index differences act on the augmentation ideal h(1)=0')
    out = list(values)
    for _ in range(iterations):
        nxt = [Q(0)] * len(out)
        for n in range(2, len(out)):
            if n * n >= len(out):
                break
            for a, w in enumerate(weights(m)):
                index = n * n + a * n
                if index < len(out):
                    nxt[index] += w * out[n]
        out = nxt
    return out


def transform(f, m=2, iterations=2, beta=Q(1)):
    h = formal_log(f)
    correction = difference(h, m, iterations)
    return formal_exp([beta * (x + y) for x, y in zip(h, correction)])


def inverse(f, m=2, iterations=2):
    term = formal_log(f)
    out, sign = list(term), -1
    while any(term):
        term = difference(term, m, iterations)
        out = [x + sign * y for x, y in zip(out, term)]
        sign = -sign
    return formal_exp(out)


def multiply(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


@lru_cache(maxsize=None)
def words(m, iterations):
    records = []
    for word in product(range(m + 1), repeat=iterations):
        poly, weight = [0, 1], 1
        for a in word:
            squared = multiply(poly, poly)
            for i, x in enumerate(poly):
                squared[i] += a * x
            poly, weight = squared, weight * weights(m)[a]
        records.append((word, weight, tuple(poly)))
    return records


def power_coefficients(poly, s, cutoff):
    # H*y'=-s*H'*y, y=H^(-s), H(0)=1.
    out = [Q(1)]
    for n in range(1, cutoff + 1):
        out.append(-sum((Q(poly[j]) * (n - j + s * j) * out[n - j]
                         for j in range(1, min(n, len(poly) - 1) + 1)), Q(0)) / n)
    return out


def kernel_coefficients(m, iterations, s, cutoff):
    out = [Q(0)] * (cutoff + 1)
    for _, weight, polynomial in words(m, iterations):
        values = power_coefficients(polynomial[::-1], s, cutoff)
        out = [x + weight * y for x, y in zip(out, values)]
    return out


def finite_difference_grammar():
    records = []
    for w in product(range(-3, 4), repeat=4):
        if not any(w) or gcd(*w) != 1 or next(x for x in reversed(w) if x) < 0:
            continue
        train = sum(w) == 0 and sum(a * w[a] for a in range(4)) == 0
        held = train and sum(a * a * w[a] for a in range(4)) == 0
        records.append({'weights': list(w), 'training_passed': train, 'held_out_passed': held})
    return {'models_scored': len(records), 'training_fits': sum(x['training_passed'] for x in records),
            'survivors': [x for x in records if x['held_out_passed']], 'records': records,
            'known_operator_calibration': 'The maximal survivor is classical third forward difference, not a new primitive'}


def cancellation_profiles():
    pairs = ((1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3),
             (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (5, 1), (6, 1))
    records = []
    for m, k in pairs:
        for s in (Q(1), Q(1, 2), Q(2, 3)):
            coefficients = kernel_coefficients(m, k, s, max(32, (m + 1) * 2 ** k))
            order = next(j for j, value in enumerate(coefficients) if value)
            records.append({'difference_order': m, 'iterations': k, 's': str(s),
                            'image_degree': 2 ** k, 'first_nonzero_Taylor_degree': order,
                            'leading_coefficient': str(coefficients[order]),
                            'coefficients': [str(x) for x in coefficients]})
    return records


def order_grammar(profiles):
    observed = {(x['difference_order'], x['iterations']): x['first_nonzero_Taylor_degree'] for x in profiles}
    train = ((1, 1), (1, 2), (2, 1))
    records = []
    for a, b, c, d in product(range(-2, 4), range(-3, 4), range(-2, 3), range(-4, 5)):
        predicted = lambda m, k: a * m * 2 ** k + b * m + c * k + d
        fitted = all(predicted(m, k) == observed[m, k] for m, k in train)
        failure = next(([m, k] for m, k in observed if predicted(m, k) != observed[m, k]), None) if fitted else None
        records.append({'a_m_2k': a, 'b_m': b, 'c_k': c, 'd': d, 'training_passed': fitted,
                        'held_out_passed': fitted and failure is None, 'first_counterexample': failure})
    return {'models_scored': len(records), 'training_fits': sum(x['training_passed'] for x in records),
            'survivors': [x for x in records if x['held_out_passed']], 'records': records,
            'universal_law': 'r(m,k)=m*(2^k-1), with generic exact order and universal vanishing below r'}


def leading_grammar(profiles):
    values = {(x['difference_order'], x['iterations'], Q(x['s'])): Q(x['leading_coefficient']) for x in profiles}
    pairs = [(m, k, s, old, values[m, k + 1, s]) for (m, k, s), old in values.items() if (m, k + 1, s) in values]
    train = [x for x in pairs if x[0] == 1 and x[1] == 1][:2]
    records = []
    for a, b, c in product(range(-1, 3), range(-1, 3), range(-2, 3)):
        def predicts(item):
            m, k, s, old, _ = item
            start = a * 2 ** k * s + b * m * (2 ** k - 1) + c
            scalar = Q((-1) ** m)
            for j in range(m):
                scalar *= start + j
            return old * scalar
        fitted = all(predicts(x) == x[-1] for x in train)
        failure = next(([x[0], x[1], str(x[2])] for x in pairs if predicts(x) != x[-1]), None) if fitted else None
        records.append({'a_degree_s': a, 'b_previous_order': b, 'c': c, 'training_passed': fitted,
                        'held_out_passed': fitted and failure is None, 'counterexample': failure})
    return {'models_scored': len(records), 'training_fits': sum(x['training_passed'] for x in records),
            'survivors': [x for x in records if x['held_out_passed']], 'records': records,
            'universal_law': 'c(m,k+1;s)=(-1)^m*(2^k*s+m*(2^k-1))_m*c(m,k;s), c(m,0;s)=1'}


def generic_checks():
    rng = random.Random(2026100706)
    records = []
    for cutoff in (64, 192):
        f, g = [sequence([1] + [Q(rng.randint(-3, 3), rng.randint(1, 7)) for _ in range(cutoff - 1)]) for _ in range(2)]
        for m, k in ((1, 1), (1, 2), (2, 1), (2, 2), (3, 1)):
            pf, pg = transform(f, m, k), transform(g, m, k)
            root = transform(f, m, k, Q(1, 2))
            checks = {'inverse': inverse(pf, m, k) == f,
                      'ordinary_D_group_law': transform(convolve(f, g), m, k) == convolve(pf, pg),
                      'ordinary_D_half_root': convolve(root, root) == pf and normalized_power(pf, Q(1, 2)) == root,
                      'prefix': transform(f[:33], m, k) == pf[:33]}
            records.append({'cutoff': cutoff, 'm': m, 'k': k, 'input_f': [str(x) for x in f],
                            'input_g': [str(x) for x in g], 'output_f': [str(x) for x in pf], 'checks': checks})
    return {'records': records, 'all_passed': all(all(x['checks'].values()) for x in records)}


def sparse_difference(values, m, k, cutoff):
    out = dict(values)
    for _ in range(k):
        nxt = {}
        for n, value in out.items():
            for a, weight in enumerate(weights(m)):
                image = n * n + a * n
                if image <= cutoff:
                    nxt[image] = nxt.get(image, Q(0)) + weight * value
        out = {n: x for n, x in nxt.items() if x}
    return out


def deep_inverse_control():
    cutoff, seed = 10 ** 8, {2: Q(2, 7), 3: Q(-3, 11)}
    shifted = sparse_difference(seed, 2, 2, cutoff)
    h = {n: seed.get(n, Q(0)) + shifted.get(n, Q(0)) for n in seed.keys() | shifted.keys()}
    recovered, term, sign, steps = dict(h), dict(h), -1, 0
    while term:
        term = sparse_difference(term, 2, 2, cutoff)
        for n, value in term.items():
            recovered[n] = recovered.get(n, Q(0)) + sign * value
        recovered = {n: x for n, x in recovered.items() if x}
        sign, steps = -sign, steps + 1
    first = sparse_difference(h, 2, 2, cutoff)
    short_inverse = {n: h.get(n, Q(0)) - first.get(n, Q(0)) for n in h.keys() | first.keys()}
    short_inverse = {n: x for n, x in short_inverse.items() if x}
    return {'cutoff': cutoff, 'seed': {str(n): str(x) for n, x in seed.items()},
            'nonzero_inverse_powers_required': steps - 1, 'exact_inverse_recovered': recovered == seed,
            'truncated_after_first_correction_rejected': short_inverse != seed,
            'first_wrong_coefficient': next({'n': n, 'value': str(x)} for n, x in sorted(short_inverse.items()) if seed.get(n, Q(0)) != x)}


def zeta_checks():
    cutoff = 1024
    u = sequence([1] * cutoff)
    logu = formal_log(u)
    records = []
    for beta in (Q(1), Q(1, 2), Q(1, 4), Q(2, 3)):
        values = transform(u, 2, 2, beta)
        root = normalized_power(transform(u, 2, 2), beta)
        records.append({'beta': str(beta), 'cutoff': cutoff, 'coefficients': [str(x) for x in values],
                        'ordinary_root_identity': values == root})
    impulse = [Q(0)] * 193
    impulse[2] = 1
    h2 = difference(impulse, 2, 2)
    impulse[2], impulse[3] = 0, 1
    h3 = difference(impulse, 2, 2)
    f1 = list(map(Q, records[0]['coefficients']))
    return {'profiles': records, 'all_passed': all(x['ordinary_root_identity'] for x in records),
            'prime_relabeling_counterexample': {'swap_primes': [2, 3], 'original_index': 20, 'relabeled_index': 45,
                'relabel_then_transform_coefficient': str(h3[45]), 'transform_then_relabel_coefficient': str(h2[20]),
                'arithmetic_prime_labels_matter': h3[45] != h2[20]},
            'zeta_input_prime_relabeling_counterexample': {'swap_primes': [2, 3], 'indices': [20, 45],
                'coefficients_at_beta_one': [str(f1[20]), str(f1[45])],
                'arithmetic_prime_labels_matter': f1[20] != f1[45],
                'multiplicativity_rejected_at_coprime_four_and_five': f1[20] != f1[4] * f1[5]},
            'squared_index_calibration': {'classical_scalar_log_series': 'LOG(zeta(2s))',
                'coefficient_2_is_not_mapped_to_delta_4_without_declared_pushforward': True},
            'ordinary_Dirichlet_series_negative_domain_gate': {'coefficient_at_p_to_2k': '(-1)^(m*k)/r for seed p^r, prime p>m',
                'no_ordinary_coefficient_series_convergence_on_Re_s_le_zero': True,
                'negative_half_plane_is_a_grouped_analytic_continuation_not_absolute_Dirichlet_convergence': True}}


def main():
    started = time.monotonic()
    out = BASE / 'difference-results'
    out.mkdir(exist_ok=True)
    calibration = finite_difference_grammar()
    profiles = cancellation_profiles()
    order, leading = order_grammar(profiles), leading_grammar(profiles)
    generic, deep, zeta = generic_checks(), deep_inverse_control(), zeta_checks()
    result = {'finite_difference_calibration': calibration, 'exact_kernel_profiles': profiles,
              'cancellation_order_grammar': order, 'leading_recurrence_grammar': leading,
              'generic_operator_checks': generic, 'deep_sparse_inverse_control': deep, 'zeta_checks': zeta,
              'selected_operator_family': 'P_(m,k,beta)(f)=EXP_D(beta*(I+A_m^k)*LOG_D(f)); A_m=sum_a (-1)^(m-a)binom(m,a) E_(n^2+a*n), E acts only on h(1)=0',
              'proved_correction_domain': 'Re(s)>-m+(m+1)/2^k; zero-free correction is exp(beta*Delta_(m,k))',
              'selected_comparison_instance': {'m': 2, 'k': 2, 'correction_domain': 'Re(s)>-5/4'},
              'trivial_zero_control_instance': {'m': 6, 'k': 1, 'correction_domain': 'Re(s)>-5/2'},
              'historical_originality': 'Unresolved; finite differences, linear augmentation maps and formal arithmetic LOG/EXP are classical',
              'counts_as_verified_new_operator': False, 'new_RH_estimate_proved': False, 'proof': 'difference_proof.txt',
              'all_passed': len(calibration['survivors']) == len(order['survivors']) == len(leading['survivors']) == 1
                and generic['all_passed'] and deep['exact_inverse_recovered'] and deep['truncated_after_first_correction_rejected']
                and zeta['all_passed'] and zeta['prime_relabeling_counterexample']['arithmetic_prime_labels_matter'],
              'elapsed_seconds': time.monotonic() - started}
    (out / 'difference_search.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Difference search: weights {calibration["models_scored"]}/{calibration["training_fits"]}/{len(calibration["survivors"])}; '
          f'orders {order["models_scored"]}/{order["training_fits"]}/{len(order["survivors"])}; leading {leading["models_scored"]}/{leading["training_fits"]}/{len(leading["survivors"])}; all={result["all_passed"]}; elapsed={result["elapsed_seconds"]:.2f}s')
    assert result['all_passed']


if __name__ == '__main__':
    main()

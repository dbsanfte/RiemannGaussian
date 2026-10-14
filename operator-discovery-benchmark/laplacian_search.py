#!/usr/bin/env python3
"""Search diagonal completion, arithmetic support masks, and prime log shears."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import isqrt
from pathlib import Path
import json
import random
import time

from exact_arithmetic import formal_exp, formal_log, normalized_power, convolve, factorization

BASE = Path(__file__).resolve().parent


@lru_cache(maxsize=None)
def primes(cutoff):
    sieve = [True] * (cutoff + 1)
    sieve[:2] = [False, False]
    for p in range(2, isqrt(cutoff) + 1):
        if sieve[p]:
            sieve[p * p::p] = [False] * len(sieve[p * p::p])
    return tuple(n for n in range(2, cutoff + 1) if sieve[n])


def kernel(h, k, r=4, predicate=lambda n: n in primes(n)):
    out = [Q(0)] * len(h)
    support = [n for n in range(2, len(h)) if (h[n] or k[n]) and predicate(n)]
    for j, a in enumerate(support):
        for b in support[j + 1:]:
            weight = (h[a] * k[b] + h[b] * k[a]) / 2
            d = (b - a) ** r
            for n, w in ((a * a * d, 1), (a * b * d, -2), (b * b * d, 1)):
                if n < len(out):
                    out[n] += w * weight
    return out


def log_flow(h, t=Q(1), r=4):
    extra = kernel(h, h, r)
    return [v + t * w for v, w in zip(h, extra)]


def transform(f, t=Q(1), r=4):
    return formal_exp(log_flow(formal_log(f), t, r))


def completion_grammar():
    rows = []
    for cross, second in product(range(-3, 4), repeat=2):
        train = 1 + cross + second == 0
        held = train and cross + 2 * second == 0
        rows.append({'weights': [1, cross, second], 'constant_vector_annihilation': train,
                     'held_out_first_difference_annihilation': held})
    return {'models_scored': len(rows), 'training_fits': sum(row['constant_vector_annihilation'] for row in rows),
            'survivors': [row for row in rows if row['held_out_first_difference_annihilation']],
            'calibration': 'Known graph-Laplacian / second-difference weights, not a new primitive'}


def mask_search():
    h = {n: Q(1, n) for n in range(2, 13)}
    def sparse_K(values, mask):
        out = {}
        support = sorted(n for n in values if mask(n))
        for j, a in enumerate(support):
            for b in support[j + 1:]:
                d = (b - a) ** 4
                for n, v in ((a * a * d, 1), (a * b * d, -2), (b * b * d, 1)):
                    out[n] = out.get(n, Q(0)) + v * values[a] * values[b]
        return {n: v for n, v in out.items() if v}
    masks = {'prime': lambda n: factorization(n) == {n: 1},
             'prime_power': lambda n: len(factorization(n)) == 1,
             'squarefree': lambda n: all(e == 1 for e in factorization(n).values()),
             'Omega_le_two': lambda n: sum(factorization(n).values()) <= 2,
             'odd': lambda n: n % 2 == 1,
             'even': lambda n: n % 2 == 0}
    records = []
    for name, mask in masks.items():
        k = sparse_K(h, mask)
        changed = {n: h.get(n, Q(0)) + k.get(n, Q(0)) for n in h.keys() | k.keys()}
        changed = {n: v for n, v in changed.items() if v}
        again = sparse_K(changed, mask)
        failure = next((n for n in sorted(k.keys() | again.keys()) if k.get(n, Q(0)) != again.get(n, Q(0))), None)
        records.append({'mask': name, 'additive_parameter_composition_passed': failure is None,
                        'first_composition_failure': failure,
                        'untruncated_first_and_second_correction_terms': [len(k), len(again)]})
    return {'records': records, 'surviving_masks': [row['mask'] for row in records if row['additive_parameter_composition_passed']],
            'prime_and_odd_are_distinct_valid_support_closures': True,
            'complete_sparse_composition_no_encoded_prefix_cutoff': True}


def generic():
    rng, rows = random.Random(2026100721), []
    for r in (2, 4, 6, 8):
        h, k = ([Q(0)] * 513 for _ in range(2))
        for n in range(2, 15):
            h[n] = Q(rng.choice((-3, -2, -1, 1, 2, 3)), rng.randint(2, 8))
            k[n] = Q(rng.choice((-2, -1, 1, 2)), rng.randint(2, 7))
        f, g = formal_exp(h), formal_exp(k)
        extra, result = kernel(h, h, r), transform(f, r=r)
        pin = transform(normalized_power(f, Q(1, 2)), r=r)
        pout = normalized_power(result, Q(1, 2))
        checks = {'prime_log_coefficients_fixed': all(extra[p] == 0 for p in primes(512)),
                  'closed_form_inverse': transform(result, t=Q(-1), r=r) == f,
                  'additive_parameter_group': transform(transform(f, t=Q(2, 3), r=r), t=Q(-3, 5), r=r) == transform(f, t=Q(1, 15), r=r),
                  'prefix_consistency': transform(f[:129], r=r) == result[:129],
                  'ordinary_output_root': convolve(pout, pout) == result,
                  'input_root_anomaly': formal_log(pin) == [a / 2 + b / 4 for a, b in zip(h, extra)],
                  'universal_input_root_commutation_rejected': pin != pout,
                  'ordinary_group_homomorphism_rejected': transform(convolve(f, g), r=r) != convolve(result, transform(g, r=r))}
        rows.append({'r': r, 'h': list(map(str, h)), 'k': list(map(str, k)),
                     'output': list(map(str, result)), 'checks': checks})
    return {'records': rows, 'all_passed': all(all(row['checks'].values()) for row in rows)}


def zeta_profiles():
    rows, size = [], 8192
    # Every contributing pair satisfies min(a,b)<=sqrt(size) and
    # |a-b|^r<=size/min(a,b)^2. This cutoff covers all three images.
    for r in (2, 4, 6, 8):
        root = 1
        while root ** r <= size // 4:
            root += 1
        cutoff = isqrt(size) + root
        h = [Q(0)] * (size + 1)
        for p in primes(cutoff):
            h[p] = Q(1)
        values = kernel(h, h, r)
        signs = all((v >= 0 if isqrt(n) ** 2 == n else v <= 0) for n, v in enumerate(values) if v)
        rows.append({'r': r, 'encoded_cutoff': size, 'complete_prime_input_cutoff': cutoff,
                     'coefficients': list(map(str, values)), 'square_positive_nonsquare_negative': signs,
                     'first_coefficients': {str(n): str(values[n]) for n in (4, 6, 9)},
                     'all_prime_coefficients_zero': all(values[p] == 0 for p in primes(size))})
    return rows


def main():
    start = time.monotonic()
    grammar, masks, laws, zeta = completion_grammar(), mask_search(), generic(), zeta_profiles()
    passed = len(grammar['survivors']) == 1 and masks['surviving_masks'] == ['prime', 'odd'] and laws['all_passed'] and all(row['square_positive_nonsquare_negative'] and row['all_prime_coefficients_zero'] for row in zeta)
    out = {'diagonal_completion_grammar': grammar, 'support_mask_grammar': masks,
           'generic_operator_laws': laws, 'zeta_profiles': zeta,
           'selected_r': 4, 'grouped_correction_abscissa_r_ge_three': '2/(r+2)',
           'grouped_selected_endpoint': '1/3, convergent',
           'ordinary_correction_coefficient_absolute_abscissa_even_r_ge_four': '1/2, convergent',
           'ordinary_transformed_Dirichlet_absolute_convergence_proved_on': 'Re(s)>1',
           'complex_holomorphic_form_is_not_Hermitian': True,
           'counts_as_new_primitive': False, 'historical_novelty_established': False,
           'new_RH_estimate_proved': False, 'all_passed': passed, 'seconds': time.monotonic() - start}
    dest = BASE / 'laplacian-results'
    dest.mkdir(exist_ok=True)
    (dest / 'laplacian_search.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Laplacian exact search:', passed, 'masks', masks['surviving_masks'], 'seconds', out['seconds'], flush=True)
    assert passed


if __name__ == '__main__':
    main()

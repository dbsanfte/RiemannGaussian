#!/usr/bin/env python3
"""Learn an unambiguous prime-power sector and decode sum-grafted indices."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import gcd
from pathlib import Path
import json
import random
import time

import flint

from exact_arithmetic import factorization
from pair_fibre_probe import prime_powers

BASE = Path(__file__).resolve().parent


def phi(a, b, r=3):
    return a * b * (a + b) ** r


def factor_native(n):
    factors = {}
    for p, e in flint.fmpz(n).factor():
        p, e = int(p), int(e)
        factors[p] = factors.get(p, 0) + e
        assert flint.fmpz(p).is_prime()
    assert product_integer(p ** e for p, e in factors.items()) == n
    return factors


def decode_factor(factors, r=3, cardinality=2, mode='full'):
    visible = {p: e for p, e in factors.items() if e % r}
    if len(visible) != cardinality:
        return None
    exponents = {'full': lambda e: e, 'residue': lambda e: e % r, 'quotient': lambda e: e // r}
    return product_integer(p ** exponents[mode](e) for p, e in visible.items())


def product_integer(values):
    out = 1
    for value in values:
        out *= value
    return out


def pair_decoder(n, r=3):
    f = factor_native(n)
    visible = [(p, e) for p, e in sorted(f.items()) if e % r]
    if len(visible) != 2:
        return None
    a, b = (p ** e for p, e in visible)
    return (min(a, b), max(a, b)) if phi(a, b, r) == n else None


def target(a, b, r=3):
    x, y = factorization(a), factorization(b)
    if len(x) != len(y) or len(x) != 1:
        return None
    p, e = next(iter(x.items()))
    q, f = next(iter(y.items()))
    return a * b if p != q and e % r and f % r else None


def encode_sparse(h, r=3):
    out = {}
    for m, v in h.items():
        factors = factorization(m)
        if len(factors) == 2 and all(e % r for e in factors.values()):
            a, b = (p ** e for p, e in factors.items())
            n = phi(a, b, r)
            out[n] = out.get(n, Q(0)) + v
    return {n: v for n, v in out.items() if v}


def decode_sparse(h, r=3):
    out = {}
    for n, v in h.items():
        pair = pair_decoder(n, r)
        if pair:
            m = pair[0] * pair[1]
            out[m] = out.get(m, Q(0)) + v
    return {m: v for m, v in out.items() if v}


def sparse_operator_laws():
    records = []
    for r in (2, 3, 4):
        h = {1: Q(1), 6: Q(2, 7), 10: Q(-3, 5), 12: Q(7, 13), 24: Q(-5, 11), 25: Q(4, 9), 80: Q(3, 17), 1296: Q(7, 19)}
        f = {1: Q(-1), 6: Q(8, 3), phi(2, 3, r): Q(2, 5), phi(2, 5, r): Q(-7, 13), phi(16, 81, r): Q(11, 17), 14929920: Q(19, 23)}
        mask = {m: v for m, v in h.items() if len(factorization(m)) == 2 and all(e % r for e in factorization(m).values())}
        D, E = lambda x: decode_sparse(x, r), lambda x: encode_sparse(x, r)
        projected = E(D(f))
        extra = {n: Q(3, 7) * v for n, v in f.items()}
        checks = {'D_E_is_decoded_sector_projection': D(E(h)) == mask,
                  'E_D_is_idempotent': E(D(projected)) == projected,
                  'D_E_is_idempotent': D(E(mask)) == mask,
                  'decoder_linearity': D(extra) == {n: Q(3, 7) * v for n, v in D(f).items()},
                  'ordinary_unit_preservation_rejected': D({1: Q(1)}) == {},
                  'non_image_input_rejected': D({6: Q(1)}) == {}}
        records.append({'r': r, 'decoded_test_input': {str(n): str(v) for n, v in h.items()},
                        'encoded_test_input': {str(n): str(v) for n, v in f.items()}, 'checks': checks})
    return {'records': records, 'all_passed': all(all(row['checks'].values()) for row in records)}


def decoder_grammar():
    training = ((2, 3), (3, 5), (8, 3), (3, 27), (2, 2))
    fresh = ((16, 81), (32, 25), (25, 49), (128, 5), (7, 64), (4, 4), (9, 27), (27, 125), (2, 65537))
    profiles = [{'inputs': [a, b], 'encoded_index': phi(a, b), 'factors': factor_native(phi(a, b)),
                 'target_product_or_none': target(a, b), 'training': j < len(training)}
                for j, (a, b) in enumerate(training + fresh)]
    records = []
    for r, k, mode in product(range(2, 10), range(1, 5), ('full', 'residue', 'quotient')):
        def predicts(row):
            return decode_factor(row['factors'], r, k, mode)
        fitted = all(predicts(row) == row['target_product_or_none'] for row in profiles if row['training'])
        failure = next((row['inputs'] for row in profiles if not row['training'] and predicts(row) != row['target_product_or_none']), None) if fitted else None
        records.append({'modulus': r, 'visible_prime_count': k, 'exponent_mode': mode,
                        'training_passed': fitted, 'held_out_passed': fitted and failure is None,
                        'first_counterexample': failure})
    return {'models_scored': len(records), 'training_fits': sum(r['training_passed'] for r in records),
            'survivors': [r for r in records if r['held_out_passed']], 'records': records, 'profiles': profiles}


def generic_profiles():
    rng, records = random.Random(2026100708), []
    for cutoff, r in product((64, 128), (2, 3, 4)):
        pp = prime_powers(cutoff)
        a = {n: Q(rng.choice((-3, -2, -1, 1, 2, 3)), rng.randint(2, 7)) for n, p, e in pp}
        b = {n: Q(rng.choice((-3, -2, -1, 1, 2, 3)), rng.randint(2, 7)) for n, p, e in pp}
        encoded, decoded, expected = {}, {}, {}
        for x in a:
            for y in b:
                n = phi(x, y, r)
                encoded[n] = encoded.get(n, Q(0)) + a[x] * b[y]
                if target(x, y, r) is not None:
                    expected[x * y] = expected.get(x * y, Q(0)) + a[x] * b[y]
        for n, value in encoded.items():
            pair = pair_decoder(n, r)
            if pair:
                m = pair[0] * pair[1]
                decoded[m] = decoded.get(m, Q(0)) + value
        clean = lambda h: {n: v for n, v in h.items() if v}
        passed = clean(decoded) == clean(expected)
        records.append({'prime_power_input_cutoff': cutoff, 'r': r,
                        'input_a': {str(n): str(v) for n, v in a.items()}, 'input_b': {str(n): str(v) for n, v in b.items()},
                        'decoded_coefficients': {str(n): str(v) for n, v in sorted(clean(decoded).items())},
                        'cross_prime_D_identity_passed': passed})
    return {'records': records, 'all_passed': all(x['cross_prime_D_identity_passed'] for x in records)}


def zeta_decoded_profile():
    cutoff = 8192
    pp = prime_powers(4096)
    # Enumerate the ENTIRE bounded-input correction before applying the
    # decoder. It is not pre-filtered to match the conjectured identity.
    encoded, origins = {}, {}
    for j, (a, p, e) in enumerate(pp):
        for b, q, f in pp[j:]:
            n = phi(a, b)
            encoded[n] = encoded.get(n, Q(0)) + Q(1 if a == b else 2, e * f)
            origins.setdefault(n, (a, b))
    values, queries = [Q(0)] * (cutoff + 1), []
    for n, value in encoded.items():
        a, b = origins[n]
        factors = factorization(a + b)
        factors = {p: 3 * e for p, e in factors.items()}
        for v in (a, b):
            for p, e in factorization(v).items():
                factors[p] = factors.get(p, 0) + e
        m = decode_factor(factors)
        if m is not None and m <= cutoff:
            visible = [p ** e for p, e in factors.items() if e % 3]
            assert len(visible) == 2 and phi(*visible) == n
            values[m] += value
            queries.append({'decoded_index': m, 'encoded_index': n, 'encoded_coefficient': str(value)})
    expected = [Q(0)] * (cutoff + 1)
    for m in range(2, cutoff + 1):
        factors = factorization(m)
        if len(factors) == 2 and all(e % 3 for e in factors.values()):
            e, f = factors.values()
            expected[m] = Q(2, e * f)
    return {'decoded_cutoff': cutoff, 'raw_prime_power_input_cutoff': 4096,
            'raw_unordered_pairs': len(pp) * (len(pp) + 1) // 2, 'raw_encoded_term_count': len(encoded),
            'queries': sorted(queries, key=lambda x: x['decoded_index']),
            'decoded_coefficients': [str(v) for v in values],
            'exact_formula': '2/(e*f) at p^e*q^f, p!=q and r does not divide e or f; zero elsewhere',
            'formula_passed': values == expected}


def prefix_controls():
    return {'decoded_index': 10, 'required_encoded_index': phi(2, 5), 'available_encoded_cutoff': 2048,
            'available_prefix_suffices': phi(2, 5) <= 2048, 'coefficient_if_available': '2',
            'unavailable_query_may_be_replaced_by_zero': False}


def optimal_norm_profiles():
    records = []
    for q, sigma_out in product((3, 5, 17, 257, 65537), (Q(1, 2), Q(1), Q(3, 2), Q(2), Q(5, 2))):
        n, m = phi(2, q), 2 * q
        ratio_squared = Q(n, m ** int(2 * sigma_out))
        records.append({'prime_pair': [2, q], 'encoded_index': n, 'decoded_index': m,
                        'source_sigma': '1/2', 'target_sigma': str(sigma_out),
                        'norm_ratio_squared': str(ratio_squared)})
    return {'records': records, 'sharp_bound': 'D_r: A_sigma -> A_tau is bounded iff tau >= (r+1)*sigma, for sigma>0 on the admissible sector',
            'exact_operator_norm_when_bounded': '6^(sigma-tau)*5^(r*sigma)',
            'same_halfplane_bounded_decoder_rejected': True, 'zeta_specific_decoded_absolute_abscissa': '1',
            'encoded_correction_proved_absolute_halfplane': 'Re(s)>2/5',
            'power_weighted_same_RH_halfplane_tradeoff': {'regularizer': 'Multiply the decoded coefficient at n by n^(-lambda)',
                                                       'sharp_boundedness_condition': 'tau+lambda >= (r+1)*sigma',
                                                       'r': 3, 'available_source_sigma_gt': '2/5', 'requested_target_tau': '1/2',
                                                       'necessary_lambda_gt': '11/10',
                                                       'critical_zero_real_part_after_shift_lt': '-3/5',
                                                       'universal_r_ge_two_lambda_gt': '(3*r+2)/(2*(r+2))',
                                                       'universal_shifted_critical_zero_real_part_lt': '-r/(r+2)',
                                                       'scope': 'This decoder and pure power-weight regularizations only'}}


def main():
    started = time.monotonic()
    grammar, generic, zeta = decoder_grammar(), generic_profiles(), zeta_decoded_profile()
    operator_laws = sparse_operator_laws()
    passed = len(grammar['survivors']) == 1 and grammar['survivors'][0]['modulus'] == 3 and generic['all_passed'] and zeta['formula_passed'] and operator_laws['all_passed']
    result = {'decoder_grammar': grammar, 'generic_decoder_identity': generic, 'zeta_decoded_profile': zeta,
              'prefix_and_unavailable_input_controls': prefix_controls(), 'norm_loss_profiles': optimal_norm_profiles(),
              'generic_linear_decoder_encoder_laws': operator_laws,
              'all_prime_power_fibres_injective_claimed': False, 'decoder_scope': 'The sector with exactly two nonzero exponent residues modulo r',
              'raw_zeta_action_reduces_to_known_mask': True,
              'historical_novelty_established': False, 'new_RH_estimate_proved': False,
              'native_factor_entry_regression': {'n': phi(2, 65537), 'raw_entries': [[int(p), int(e)] for p, e in flint.fmpz(phi(2, 65537)).factor()],
                                                 'aggregated_factorization': factor_native(phi(2, 65537)),
                                                 'exact_product_reconstruction_required': True,
                                                 'wrong_last_entry_dictionary_rejected': {int(p): int(e) for p, e in flint.fmpz(phi(2, 65537)).factor()} != factor_native(phi(2, 65537))},
              'all_passed': passed, 'seconds': time.monotonic() - started}
    dest = BASE / 'decode-results'
    dest.mkdir(exist_ok=True)
    (dest / 'decode_search.json').write_text(json.dumps(result, indent=2) + '\n')
    print('Decoder programs:', grammar['models_scored'], 'training fits:', grammar['training_fits'], 'survivors:', grammar['survivors'], flush=True)
    print('Raw encoded terms:', zeta['raw_encoded_term_count'], 'decoded queries:', len(zeta['queries']), 'all passed:', passed, 'seconds', result['seconds'], flush=True)
    assert passed


if __name__ == '__main__':
    main()

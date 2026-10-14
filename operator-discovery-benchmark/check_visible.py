#!/usr/bin/env python3
"""Independent complete-integer-fibre and harmonic audit of the visible decoder."""

from fractions import Fraction as Q
from functools import lru_cache
from math import isqrt
from pathlib import Path
import json
import time

import flint

BASE = Path(__file__).resolve().parent


@lru_cache(maxsize=None)
def factors(n):
    fs = {}
    for p, e in flint.fmpz(n).factor():
        p, e = int(p), int(e)
        assert flint.fmpz(p).is_prime()
        fs[p] = fs.get(p, 0) + e
    value = 1
    for p, e in fs.items():
        value *= p ** e
    assert value == n
    return fs


@lru_cache(maxsize=None)
def all_integer_pairs(n, r):
    sums = [1]
    for p, e in factors(n).items():
        sums = [s * p ** j for s in sums for j in range(e // r + 1)]
    pairs = []
    for s in sums:
        m = n // s ** r
        D = s * s - 4 * m
        if D < 0:
            continue
        root = isqrt(D)
        if root * root == D and (s - root) % 2 == 0:
            a, b = (s - root) // 2, (s + root) // 2
            if a >= 2 and a * b * (a + b) ** r == n:
                pairs.append((a, b))
    return tuple(sorted(set(pairs)))


def prime_power_pairs(n, r):
    return [pair for pair in all_integer_pairs(n, r) if len(factors(pair[0])) == len(factors(pair[1])) == 1]


def eligible_pair(a, b, r):
    fa, fb = factors(a), factors(b)
    if len(fa) != 1 or len(fb) != 1:
        return False
    (p, e), (q, f) = next(iter(fa.items())), next(iter(fb.items()))
    return bool((e + f) % r) if p == q else bool(e % r and f % r)


def classifier(source):
    profiles = source['single_visible_classifier_grammar']['profiles']
    for profile in profiles:
        a, b = profile['pair']
        n = a * b * (a + b) ** 3
        assert n == profile['encoded_index']
        visible = [p for p, e in factors(n).items() if e % 3]
        target = len(factors(a * b)) == 1 and len(visible) == 1
        assert target == profile['one_visible_same_prime_target']
    for row in source['single_visible_classifier_grammar']['records']:
        def predicts(profile):
            n, power = profile['encoded_index'], row['visible_power_comparison_exponent']
            maximal_r_power = 1
            for p, e in factors(n).items():
                maximal_r_power *= p ** (e // 3)
            residual = n // maximal_r_power ** 3
            visible = [(p, e) for p, e in factors(n).items() if residual % p == 0]
            return len(visible) == 1 and visible[0][0] ** (visible[0][1] * power) > n
        train = all(predicts(p) == p['one_visible_same_prime_target'] for p in profiles if p['training'])
        fail = next((p['pair'] for p in profiles if not p['training'] and predicts(p) != p['one_visible_same_prime_target']), None) if train else None
        assert row['training_passed'] == train and row['held_out_passed'] == (train and fail is None) and row['first_failure'] == fail
    return True


def reconstruction(source):
    profiles = source['same_prime_reconstruction_grammar']['profiles']
    for row in source['same_prime_reconstruction_grammar']['records']:
        def predicts(profile):
            n = profile['encoded_index']
            possible = prime_power_pairs(n, 3)
            eligible = [pair for pair in possible if eligible_pair(*pair, 3) and len(factors(pair[0] * pair[1])) == 1]
            assert len(eligible) <= 1
            if not eligible:
                return None
            a, b = eligible[0]
            (p, e), (_, f) = next(iter(factors(a).items())), next(iter(factors(b).items()))
            v = factors(n)[p]
            marker = row['two_shift'] if p == 2 and a == b else 0
            return list(eligible[0]) if (3 + row['divisor_offset']) * e == v - (f - e) - marker else None
        train = all(predicts(p) == p['same_prime_decoded_pair_target'] for p in profiles if p['training'])
        fail = next((p['pair'] for p in profiles if not p['training'] and predicts(p) != p['same_prime_decoded_pair_target']), None) if train else None
        assert row['training_passed'] == train and row['held_out_passed'] == (train and fail is None) and row['first_failure'] == fail
    return True


def generic(source):
    for row in source['generic_filtered_bilinear_identity']['records']:
        a, b = ({int(n): Q(v) for n, v in row[key].items()} for key in ('a', 'b'))
        r, image_indices = row['r'], set()
        for x in a:
            for y in b:
                image_indices.add(x * y * (x + y) ** r)
        decoded = {}
        for n in image_indices:
            pp = prime_power_pairs(n, r)
            accepted = [pair for pair in pp if eligible_pair(*pair, r)]
            if accepted:
                assert len(accepted) == len(pp) == 1
                x, y = accepted[0]
                v = a.get(x, Q(0)) * b.get(y, Q(0))
                if x != y:
                    v += a.get(y, Q(0)) * b.get(x, Q(0))
                decoded[x * y] = decoded.get(x * y, Q(0)) + v
        decoded = {n: v for n, v in decoded.items() if v}
        assert decoded == {int(n): Q(v) for n, v in row['decoded_coefficients'].items()}
    return True


def zeta(source):
    count, same_prime = 0, 0
    for profile in source['zeta_profiles']:
        r, values = profile['r'], [Q(0)] * (profile['decoded_cutoff'] + 1)
        for row in profile['queries']:
            pp = prime_power_pairs(row['encoded_index'], r)
            assert len(pp) == 1 and eligible_pair(*pp[0], r)
            x, y = pp[0]
            assert list(pp[0]) == row['pair'] and x * y == row['decoded_index']
            e, f = next(iter(factors(x).values())), next(iter(factors(y).values()))
            v = Q(1 if x == y else 2, e * f)
            assert v == Q(row['encoded_coefficient'])
            values[x * y] += v
            count += 1
            same_prime += len(factors(x * y)) == 1
        recorded = list(map(Q, profile['decoded_coefficients']))
        assert values == recorded
        full = [Q(0)] * len(values)
        for n in range(2, len(values)):
            fs = factors(n)
            if len(fs) == 1:
                k = next(iter(fs.values()))
                full[n] = Q(2, k) * sum((Q(1, e) for e in range(1, k)), Q(0))
            elif len(fs) == 2:
                e, f = fs.values()
                full[n] = Q(2, e * f)
        first = next(n for n in range(2, len(values)) if values[n] != full[n])
        assert first == profile['first_defect_index'] == 2 ** r
        assert values[first] - full[first] == Q(profile['first_defect_coefficient']) == -Q(2, r) * sum((Q(1, j) for j in range(1, r)), Q(0))
    return {'all_passed': True, 'complete_prime_power_fibre_queries': count, 'same_prime_queries': same_prime}


def harmonic_cancellation(source):
    profiles = source['local_cancellation_grammar']['profiles']
    for row in profiles:
        r = row['r']
        values = [Q(0), Q(0)]
        for k in range(2, len(row['coefficients'])):
            H = sum((Q(1, e) for e in range(1, k)), Q(0))
            h = sum((Q(1, e) for e in range(1, k) if e % r and (k - e) % r), Q(0))
            values.append(Q(2, k) * ((H if k % r else 0) - h))
        assert values == list(map(Q, row['coefficients']))
        assert all(v == 0 for v in values[:r]) and values[r] < 0 and all(abs(v) <= 1 for v in values)
    order = [(a, b) for a in range(-1, 4) for b in range(-3, 4)
             if all(a * p['r'] + b == p['first_degree'] for p in profiles)]
    assert order == [(1, 0)] and len(source['local_cancellation_grammar']['order_survivors']) == 1
    survivors = []
    for sign in (-1, 1):
        for scale in (1, 2, 3):
            for offset in (-1, 0, 1):
                for power in (0, 1, 2):
                    if all(sign * scale * sum((Q(1, j) for j in range(1, p['r'] + offset + 1)), Q(0)) / p['r'] ** power == Q(p['first_coefficient']) for p in profiles):
                        survivors.append((sign, scale, offset, power))
    assert survivors == [(-1, 2, -1, 1)]
    return True


def norms(source):
    for row in source['weighted_norm_profiles']['records']:
        r, k, sigma, tau = row['r'], row['total_exponent'], Q(row['sigma']), Q(row['tau'])
        exponent = int(2 * r * sigma)
        value = sum((Q(2 ** e + 2 ** (k - e), 2 ** k) ** exponent for e in range(1, k // 2 + 1)), Q(0))
        assert sigma * (r + 1) == tau and Q(row['row_norm_squared']) == value and k % r
        if r * sigma >= 1:
            assert value <= 1
    assert any(Q(row['row_norm_squared']) > 1 for row in source['weighted_norm_profiles']['records'])
    kernel = {int(n): Q(v) for n, v in source['weighted_norm_profiles']['nonzero_kernel'].items()}
    out = {}
    for n, v in kernel.items():
        pp = prime_power_pairs(n, 3)
        assert len(pp) == 1 and eligible_pair(*pp[0], 3)
        m = pp[0][0] * pp[0][1]
        out[m] = out.get(m, Q(0)) + v
    assert kernel and not any(out.values())
    assert source['weighted_norm_profiles']['unqualified_Hilbert_boundary_norm_one_rejected']
    return True


def main():
    start = time.monotonic()
    source = json.loads((BASE / 'visible-results/visible_search.json').read_text())
    assert source['all_passed']
    audit = zeta(source)
    checks = {'oversized_threshold_grammar_recomputed': classifier(source),
              'same_prime_reconstruction_by_complete_integer_fibres': reconstruction(source),
              'generic_signed_bilinear_identity_on_unrelated_inputs': generic(source),
              'all_six_zeta_profiles_by_complete_prime_power_fibres': audit['all_passed'],
              'first_defect_and_local_harmonic_cancellation': harmonic_cancellation(source),
              'weighted_Hilbert_rows_kernel_and_low_weight_negative_controls': norms(source)}
    out = {'checks': checks, 'exact_zeta_audit': audit, 'production_imports': False,
           'shared_trusted_kernel': 'FLINT exact integer factorization/primality; independent full sum-divisors and discriminants',
           'all_passed': all(checks.values()), 'seconds': time.monotonic() - start}
    (BASE / 'visible-results/visible_verification.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Independent visible decoder exact audit:', sum(checks.values()), '/', len(checks), audit, 'seconds:', out['seconds'], flush=True)
    assert out['all_passed']


if __name__ == '__main__':
    main()

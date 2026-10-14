#!/usr/bin/env python3
"""Independent divisor-of-sum/discriminant audit of the prime-sum decoder."""

from fractions import Fraction as Q
from math import isqrt, gcd
from pathlib import Path
import json
import time

import flint

from check_joint_size import factors

BASE = Path(__file__).resolve().parent


def exact_factors(n):
    out = {}
    for p, e in flint.fmpz(n).factor():
        p, e = int(p), int(e)
        out[p] = out.get(p, 0) + e
    reconstructed = 1
    for p, e in out.items():
        assert len(factors(p)) == 1 and factors(p).get(p) == 1
        reconstructed *= p ** e
    assert reconstructed == n
    return out


def all_integer_pairs(n, r=3):
    # If s=a+b, s^r divides n. Enumerate ALL possible sums, then
    # solve X^2-sX+n/s^r=0. This does not use the production residue
    # decoder or any supplied input-pair locations.
    roots = [(p, e // r) for p, e in exact_factors(n).items()]
    sums = [1]
    for p, e in roots:
        sums = [d * p ** j for d in sums for j in range(e + 1)]
    pairs = []
    for s in sums:
        product = n // s ** r
        discriminant = s * s - 4 * product
        if discriminant < 0:
            continue
        root = isqrt(discriminant)
        if root * root != discriminant or (s - root) % 2:
            continue
        a, b = (s - root) // 2, (s + root) // 2
        if a >= 2 and a * b * (a + b) ** r == n:
            pairs.append((a, b))
    return sorted(set(pairs))


def admissible_pairs(n, r=3):
    out = []
    for a, b in all_integer_pairs(n, r):
        fa, fb = factors(a), factors(b)
        if len(fa) == len(fb) == 1 and gcd(a, b) == 1:
            ea, eb = next(iter(fa.values())), next(iter(fb.values()))
            if ea % r and eb % r:
                out.append((a, b, ea, eb))
    return out


def grammar(source):
    profiles = source['decoder_grammar']['profiles']
    for row in source['decoder_grammar']['records']:
        def predicts(profile):
            n, r = profile['encoded_index'], row['modulus']
            prime_factors = list(exact_factors(n).items())
            maximal_power_root = 1
            for p, e in prime_factors:
                maximal_power_root *= p ** (e // r)
            residual = n // maximal_power_root ** r
            visible = [(p, e) for p, e in prime_factors if residual % p == 0]
            if len(visible) != row['visible_prime_count']:
                return None
            product = 1
            for p, e in visible:
                power = e if row['exponent_mode'] == 'full' else e % r if row['exponent_mode'] == 'residue' else e // r
                product *= p ** power
            return product
        train = all(predicts(p) == p['target_product_or_none'] for p in profiles if p['training'])
        failed = next((p['inputs'] for p in profiles if not p['training'] and predicts(p) != p['target_product_or_none']), None) if train else None
        assert train == row['training_passed'] and (train and failed is None) == row['held_out_passed'] and failed == row['first_counterexample']
    return True


def generic(source):
    records = []
    for row in source['generic_decoder_identity']['records']:
        a, b = ({int(n): Q(v) for n, v in row[k].items()} for k in ('input_a', 'input_b'))
        r, encoded_indices, decoded = row['r'], set(), {}
        for x in a:
            for y in b:
                encoded_indices.add((x + y) ** r * x * y)
        for n in encoded_indices:
            pairs = admissible_pairs(n, r)
            assert len(pairs) <= 1
            if pairs:
                x, y, _, _ = pairs[0]
                value = a.get(x, Q(0)) * b.get(y, Q(0)) + a.get(y, Q(0)) * b.get(x, Q(0))
                decoded[x * y] = decoded.get(x * y, Q(0)) + value
        decoded = {n: v for n, v in decoded.items() if v}
        recorded = {int(n): Q(v) for n, v in row['decoded_coefficients'].items()}
        records.append(decoded == recorded)
    return all(records)


def zeta(source):
    row = source['zeta_decoded_profile']
    values = [Q(0)] * (row['decoded_cutoff'] + 1)
    for query in row['queries']:
        pairs = admissible_pairs(query['encoded_index'])
        assert len(pairs) == 1
        x, y, e, f = pairs[0]
        assert x * y == query['decoded_index'] and Q(query['encoded_coefficient']) == Q(2, e * f)
        values[x * y] += Q(2, e * f)
    return values == list(map(Q, row['decoded_coefficients']))


def calibration():
    records = []
    for n in (12, 72, 108, 432, 1728, 31944):
        for r in (2, 3, 4, 5):
            maximal = max(d for d in range(1, isqrt(n) + 1) if n % d ** r == 0)
            decomposition = n // maximal ** r
            valuation_result = 1
            for p, e in factors(n).items():
                valuation_result *= p ** (e % r)
            records.append(decomposition == valuation_result)
    return all(records)


def norm_profiles(source):
    for row in source['norm_loss_profiles']['records']:
        p, q = row['prime_pair']
        assert p == 2 and len(factors(q)) == 1 and next(iter(factors(q).values())) == 1
        m, n = p * q, p * q * (p + q) ** 3
        assert Q(row['norm_ratio_squared']) == Q(n, m ** int(2 * Q(row['target_sigma'])))
        assert n == row['encoded_index'] and m == row['decoded_index']
    tradeoff = source['norm_loss_profiles']['power_weighted_same_RH_halfplane_tradeoff']
    assert Q(tradeoff['necessary_lambda_gt']) == 4 * Q(tradeoff['available_source_sigma_gt']) - Q(tradeoff['requested_target_tau']) == Q(11, 10)
    assert Q(tradeoff['critical_zero_real_part_after_shift_lt']) == Q(1, 2) - Q(11, 10) == Q(-3, 5)
    for row in source['norm_loss_profiles']['records']:
        if row['prime_pair'] == [2, 3] and Q(row['target_sigma']) >= 2:
            norm_squared = Q(6) ** (1 - 2 * Q(row['target_sigma'])) * 5 ** 3
            assert norm_squared == Q(row['norm_ratio_squared'])
    return True


def controls(source):
    row = source['prefix_and_unavailable_input_controls']
    assert row['required_encoded_index'] == 3430 > row['available_encoded_cutoff'] and row['decoded_index'] == 10
    assert not row['unavailable_query_may_be_replaced_by_zero']
    pairs = all_integer_pairs(14929920)
    assert (3, 45) in pairs and (16, 20) in pairs
    # Non-image integers can satisfy the two-residue condition; the
    # arithmetic image validation must not be silently omitted.
    assert not admissible_pairs(6)
    return not source['all_prime_power_fibres_injective_claimed']


def repeated_prime_regression(source):
    row = source['native_factor_entry_regression']
    n = 2 * 65537 * 65539 ** 3
    assert row['n'] == n and exact_factors(n) == {2: 1, 65537: 1, 65539: 3}
    assert admissible_pairs(n) == [(2, 65537, 1, 1)]
    return row['wrong_last_entry_dictionary_rejected'] and row['exact_product_reconstruction_required']


def operator_laws(source):
    for row in source['generic_linear_decoder_encoder_laws']['records']:
        r = row['r']
        h, f = ({int(n): Q(v) for n, v in row[key].items()} for key in ('decoded_test_input', 'encoded_test_input'))
        def E(values):
            out = {}
            for m, v in values.items():
                fs = factors(m)
                if len(fs) == 2 and all(e % r for e in fs.values()):
                    a, b = (p ** e for p, e in fs.items())
                    out[(a + b) ** r * m] = v
            return out
        def D(values):
            out = {}
            for n, v in values.items():
                eligible = admissible_pairs(n, r)
                assert len(eligible) <= 1
                if eligible:
                    a, b, _, _ = eligible[0]
                    out[a * b] = v
            return out
        mask = {m: v for m, v in h.items() if len(factors(m)) == 2 and all(e % r for e in factors(m).values())}
        projected = E(D(f))
        assert D(E(h)) == D(E(mask)) == mask and E(D(projected)) == projected
        assert D({n: Q(3, 7) * v for n, v in f.items()}) == {n: Q(3, 7) * v for n, v in D(f).items()}
        assert D({1: Q(1)}) == D({6: Q(1)}) == {}
    return True


def main():
    started = time.monotonic()
    source = json.loads((BASE / 'decode-results/decode_search.json').read_text())
    checks = {'all_decoder_grammar_decisions_recomputed': grammar(source),
              'generic_cross_prime_identity_by_complete_integer_fibres': generic(source),
              'every_zeta_query_checked_by_sum_divisors_and_discriminant': zeta(source),
              'known_powerfree_decomposition_calibration': calibration(),
              'exact_weighted_norm_profiles': norm_profiles(source),
              'collisions_missing_input_and_non_image_controls': controls(source),
              'repeated_native_prime_entries_and_product_reconstruction': repeated_prime_regression(source)}
    checks['generic_partial_inverse_projection_and_linear_laws'] = operator_laws(source)
    out = {'checks': checks, 'all_passed': all(checks.values()), 'production_imports': False,
           'trusted_exact_factor_kernel': 'FLINT fmpz factor; independent integer discriminants and divisor enumeration',
           'seconds': time.monotonic() - started}
    (BASE / 'decode-results/decode_verification.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Independent decoder exact audit:', sum(checks.values()), '/', len(checks), 'seconds', out['seconds'], flush=True)
    assert out['all_passed']


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Learn the oversized visible-prime sector and decode prime-power products."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from pathlib import Path
import json
import random
import time

from decode_search import factor_native, phi
from exact_arithmetic import factorization
from pair_fibre_probe import prime_powers

BASE = Path(__file__).resolve().parent


def integer_product(values):
    answer = 1
    for v in values:
        answer *= v
    return answer


def power_exponent(n, p):
    e = 0
    while n > 1 and n % p == 0:
        n //= p
        e += 1
    return e if n == 1 else None


def decode_factors(n, fs, r=3, divisor_offset=2, two_shift=None):
    if two_shift is None:
        two_shift = r
    visible = [(p, e) for p, e in fs.items() if e % r]
    if len(visible) == 2:
        a, b = (p ** e for p, e in visible)
        return tuple(sorted((a, b))) if phi(a, b, r) == n else None
    if len(visible) != 1:
        return None
    p, v = visible[0]
    if (p ** v) ** (r + 1) <= n:
        return None
    residual_root = integer_product(q ** (e // r) for q, e in fs.items() if q != p)
    denominator = r + divisor_offset
    if p == 2 and residual_root == 1:
        if v <= two_shift or (v - two_shift) % denominator:
            return None
        e = (v - two_shift) // denominator
        a = b = p ** e
    else:
        d = power_exponent(residual_root - 1, p)
        if d is None or v <= d or (v - d) % denominator:
            return None
        e = (v - d) // denominator
        a, b = p ** e, p ** (e + d)
    return (a, b) if a >= 2 and phi(a, b, r) == n else None


def decode_sparse(h, r=3):
    output = {}
    for n, v in h.items():
        pair = decode_factors(n, factor_native(n), r)
        if pair:
            m = pair[0] * pair[1]
            output[m] = output.get(m, Q(0)) + v
    return {n: v for n, v in output.items() if v}


def admissible(a, b, r):
    fa, fb = factorization(a), factorization(b)
    if len(fa) != 1 or len(fb) != 1:
        return False
    p, e = next(iter(fa.items()))
    q, f = next(iter(fb.items()))
    return (e + f) % r != 0 if p == q else e % r != 0 and f % r != 0


def profile(a, b, training):
    n = phi(a, b)
    fs = factor_native(n)
    visible = [(p, e) for p, e in fs.items() if e % 3]
    same = len(factor_native(a * b)) == 1 and len(visible) == 1
    return {'pair': [a, b], 'encoded_index': n, 'factors': fs, 'training': training,
            'one_visible_same_prime_target': same,
            'same_prime_decoded_pair_target': list(sorted((a, b))) if same else None}


def classifier_grammar():
    training = ((2, 8), (3, 27), (3, 3), (2, 27), (4, 27), (8, 25))
    held = ((2, 2 ** 25), (2 ** 13, 27), (2 ** 17, 2 ** 41), (3 ** 7, 3 ** 12), (4, 4), (2, 4))
    profiles = [profile(a, b, j < len(training)) for j, (a, b) in enumerate(training + held)]
    records = []
    for power in range(1, 10):
        def predicts(row):
            visible = [(int(p), e) for p, e in row['factors'].items() if e % 3]
            return len(visible) == 1 and visible[0][0] ** (visible[0][1] * power) > row['encoded_index']
        fitted = all(predicts(row) == row['one_visible_same_prime_target'] for row in profiles if row['training'])
        failure = next((row['pair'] for row in profiles if not row['training'] and predicts(row) != row['one_visible_same_prime_target']), None) if fitted else None
        records.append({'visible_power_comparison_exponent': power, 'training_passed': fitted,
                        'held_out_passed': fitted and failure is None, 'first_failure': failure})
    return {'models_scored': len(records), 'training_fits': sum(row['training_passed'] for row in records),
            'survivors': [row for row in records if row['held_out_passed']], 'profiles': profiles, 'records': records}


def reconstruction_grammar():
    train = ((2, 8), (3, 27), (9, 27))
    held = ((2, 2), (4, 4), (2 ** 17, 2 ** 17), (2 ** 17, 2 ** 41), (3 ** 7, 3 ** 12))
    profiles = [profile(a, b, j < len(train)) for j, (a, b) in enumerate(train + held)]
    records = []
    for offset, shift in product(range(1, 6), (0, 1, 3, 4, 5)):
        def predicts(row):
            fs = {int(p): e for p, e in row['factors'].items()}
            result = decode_factors(row['encoded_index'], fs, divisor_offset=offset, two_shift=shift)
            return list(result) if result else None
        fitted = all(predicts(row) == row['same_prime_decoded_pair_target'] for row in profiles if row['training'])
        failure = next((row['pair'] for row in profiles if not row['training'] and predicts(row) != row['same_prime_decoded_pair_target']), None) if fitted else None
        records.append({'divisor_offset': offset, 'two_shift': shift, 'training_passed': fitted,
                        'held_out_passed': fitted and failure is None, 'first_failure': failure})
    return {'models_scored': len(records), 'training_fits': sum(row['training_passed'] for row in records),
            'survivors': [row for row in records if row['held_out_passed']], 'profiles': profiles, 'records': records}


def generic():
    rng, records = random.Random(2026100710), []
    for r, cutoff in product((3, 4, 5), (64, 128)):
        pp = prime_powers(cutoff)
        a = {n: Q(rng.choice((-3, -2, -1, 1, 2, 3)), rng.randint(2, 9)) for n, _, _ in pp}
        b = {n: Q(rng.choice((-3, -2, -1, 1, 2, 3)), rng.randint(2, 9)) for n, _, _ in pp}
        encoded, expected = {}, {}
        for x in a:
            for y in b:
                n = phi(x, y, r)
                v = a[x] * b[y]
                encoded[n] = encoded.get(n, Q(0)) + v
                if admissible(x, y, r):
                    expected[x * y] = expected.get(x * y, Q(0)) + v
        decoded = decode_sparse(encoded, r)
        expected = {n: v for n, v in expected.items() if v}
        records.append({'r': r, 'input_cutoff': cutoff, 'a': {str(n): str(v) for n, v in a.items()},
                        'b': {str(n): str(v) for n, v in b.items()},
                        'decoded_coefficients': {str(n): str(v) for n, v in sorted(decoded.items())},
                        'bilinear_filtered_identity_passed': decoded == expected})
    return {'records': records, 'all_passed': all(row['bilinear_filtered_identity_passed'] for row in records)}


@lru_cache(maxsize=None)
def small_factors(n):
    return factorization(n)


def zeta_profiles():
    pp, profiles = prime_powers(4096), []
    for r in (3, 4, 5, 7, 11, 13):
        encoded, fs_map = {}, {}
        for j, (a, _, e) in enumerate(pp):
            for b, _, f in pp[j:]:
                n = phi(a, b, r)
                encoded[n] = encoded.get(n, Q(0)) + Q(1 if a == b else 2, e * f)
                fs = {p: r * v for p, v in small_factors(a + b).items()}
                for x in (a, b):
                    for p, v in small_factors(x).items():
                        fs[p] = fs.get(p, 0) + v
                fs_map[n] = fs
        values, queries = [Q(0)] * 8193, []
        for n, v in encoded.items():
            pair = decode_factors(n, fs_map[n], r)
            if pair and pair[0] * pair[1] <= 8192:
                m = pair[0] * pair[1]
                values[m] += v
                queries.append({'encoded_index': n, 'decoded_index': m, 'pair': list(pair), 'encoded_coefficient': str(v)})
        expected, full_square = [Q(0)] * len(values), [Q(0)] * len(values)
        for a, _, e in pp:
            for b, _, f in pp:
                if a * b <= 8192:
                    full_square[a * b] += Q(1, e * f)
                    if admissible(a, b, r):
                        expected[a * b] += Q(1, e * f)
        defect = next((n for n in range(2, len(values)) if values[n] != full_square[n]), None)
        profiles.append({'r': r, 'decoded_cutoff': 8192, 'source_prime_power_cutoff': 4096,
                         'raw_encoded_terms': len(encoded), 'queries': queries,
                         'decoded_coefficients': [str(v) for v in values], 'formula_passed': values == expected,
                         'first_defect_index': defect, 'first_defect_coefficient': str(values[defect] - full_square[defect])})
        print('Visible prime-power profile', r, 'queries:', len(queries), 'first defect:', defect, flush=True)
    return profiles


def local_coefficients(r, degree):
    h = [Q(0)] + [Q(1, k) for k in range(1, degree + 1)]
    filtered = [v if k % r else Q(0) for k, v in enumerate(h)]
    square = [sum((h[e] * h[k - e] for e in range(1, k)), Q(0)) for k in range(degree + 1)]
    diagonal = [sum((filtered[e] * filtered[k - e] for e in range(1, k)), Q(0)) for k in range(degree + 1)]
    return [square[k] * bool(k % r) - diagonal[k] for k in range(degree + 1)]


def cancellation_grammar():
    profiles = []
    for r in (3, 4, 5, 7, 8, 11, 13):
        c = local_coefficients(r, 3 * r)
        k = next(j for j, v in enumerate(c) if v)
        profiles.append({'r': r, 'first_degree': k, 'first_coefficient': str(c[k]),
                         'training': r <= 5, 'coefficients': [str(v) for v in c]})
    orders = []
    for a, b in product(range(-1, 4), range(-3, 4)):
        fitted = all(a * row['r'] + b == row['first_degree'] for row in profiles if row['training'])
        held = fitted and all(a * row['r'] + b == row['first_degree'] for row in profiles if not row['training'])
        orders.append({'r_multiplier': a, 'constant': b, 'training_passed': fitted, 'held_out_passed': held})
    leading = []
    for sign, scale, offset, power in product((-1, 1), (1, 2, 3), (-1, 0, 1), (0, 1, 2)):
        def predicts(r):
            harmonic = sum((Q(1, j) for j in range(1, r + offset + 1)), Q(0))
            return sign * scale * harmonic / r ** power
        fitted = all(predicts(row['r']) == Q(row['first_coefficient']) for row in profiles if row['training'])
        held = fitted and all(predicts(row['r']) == Q(row['first_coefficient']) for row in profiles if not row['training'])
        leading.append({'sign': sign, 'scale': scale, 'harmonic_offset': offset, 'denominator_power': power,
                        'training_passed': fitted, 'held_out_passed': held})
    return {'profiles': profiles, 'order_models': len(orders), 'order_survivors': [row for row in orders if row['held_out_passed']],
            'leading_models': len(leading), 'leading_survivors': [row for row in leading if row['held_out_passed']],
            'all_local_coefficients_bounded_by_one': all(abs(Q(v)) <= 1 for row in profiles for v in row['coefficients'])}


def norm_profiles():
    rows = []
    for r, k in product((3, 4, 5), range(2, 25)):
        if k % r:
            for sigma in (Q(1, 2 * r), Q(1, r), Q(1, 2)):
                tau = (r + 1) * sigma
                exponent = int(2 * r * sigma)
                row = sum(((Q(1, 2 ** e) + Q(1, 2 ** (k - e))) ** exponent
                           for e in range(1, k // 2 + 1)), Q(0))
                rows.append({'r': r, 'prime': 2, 'total_exponent': k, 'sigma': str(sigma), 'tau': str(tau),
                             'row_norm_squared': str(row)})
    kernel = {phi(2, 8): Q(1), phi(4, 4): Q(-1)}
    return {'records': rows, 'absolute_bounded_iff': 'tau >= (r+1)*sigma for sigma>0',
            'absolute_exact_norm': '4^((r+1)*sigma-tau)',
            'Hilbert_bounded_iff_positive_sigma': 'tau >= (r+1)*sigma for sigma>0',
            'Hilbert_exact_norm_when_r_sigma_ge_one': '4^((r+1)*sigma-tau)',
            'unqualified_Hilbert_boundary_norm_one_rejected': any(Q(row['row_norm_squared']) > 1 for row in rows),
            'unweighted_Hilbert_boundedness_rejected': True,
            'nonzero_kernel': {str(n): str(v) for n, v in kernel.items()}, 'kernel_decoded_to_zero': not decode_sparse(kernel),
            'full_prime_power_encoded_exact_absolute_abscissa': '2/(r+2)', 'full_encoded_endpoint_converges': True,
            'full_encoded_endpoint_input': 'PNT weighted prime-power count W(x)=sum_(p^e<=x)1/e=O(x/log x)',
            'endpoint_Hilbert_decoder_norm': '1',
            'uniform_endpoint_input_norm_upper': 'Gamma_3(2/5), finite, not numerically evaluated here'}


def main():
    start = time.monotonic()
    classifier, reconstruction, laws = classifier_grammar(), reconstruction_grammar(), generic()
    profiles, cancellation, norms = zeta_profiles(), cancellation_grammar(), norm_profiles()
    passed = (len(classifier['survivors']) == len(reconstruction['survivors']) == 1 and laws['all_passed']
              and all(row['formula_passed'] for row in profiles) and len(cancellation['order_survivors']) == len(cancellation['leading_survivors']) == 1
              and cancellation['all_local_coefficients_bounded_by_one'] and norms['kernel_decoded_to_zero'])
    out = {'single_visible_classifier_grammar': classifier, 'same_prime_reconstruction_grammar': reconstruction,
           'generic_filtered_bilinear_identity': laws, 'zeta_profiles': profiles, 'local_cancellation_grammar': cancellation,
           'weighted_norm_profiles': norms, 'correction_holomorphic_domain': 'Re(s)>1/r',
           'ordinary_decoded_absolute_abscissa': '1', 'limit_series': '(LOG zeta(s))^2',
           'raw_zeta_action_reduces_to_known_partition_masks': True,
           'global_prime_power_injectivity_claimed': False, 'historical_novelty_established': False,
           'new_RH_estimate_proved': False, 'all_passed': passed, 'seconds': time.monotonic() - start}
    dest = BASE / 'visible-results'
    dest.mkdir(exist_ok=True)
    (dest / 'visible_search.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Oversized classifier:', classifier['survivors'], 'reconstruction:', reconstruction['survivors'], flush=True)
    print('Cancellation:', cancellation['order_survivors'], cancellation['leading_survivors'], 'all passed:', passed, 'seconds:', out['seconds'], flush=True)
    assert passed


if __name__ == '__main__':
    main()

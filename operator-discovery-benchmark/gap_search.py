#!/usr/bin/env python3
"""Exact gap-index operations, root anomaly, and collision-dependent inverse mass."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from pathlib import Path
import json
import random
import time

from exact_arithmetic import convolve, formal_exp, formal_log, normalized_power
from pair_fibre_probe import prime_powers

BASE = Path(__file__).resolve().parent


def index(a, b, r=3):
    return a * b * abs(a - b) ** r


@lru_cache(maxsize=None)
def fibres(cutoff, r=3):
    table = {}
    a = 2
    while a * (a + 1) <= cutoff:
        b = a + 1
        while index(a, b, r) <= cutoff:
            table.setdefault(index(a, b, r), []).append((a, b))
            b += 1
        a += 1
    return table


def couple(a, b, r=3):
    assert len(a) == len(b) and a[1] == b[1] == 0
    out = [Q(0)] * len(a)
    for n, pairs in fibres(len(a) - 1, r).items():
        out[n] = sum((a[x] * b[y] + a[y] * b[x] for x, y in pairs), Q(0))
    return out


def transform(f, r=3, beta=Q(1), family='input'):
    h = formal_log(f)
    extra = couple(h, h, r)
    amplitude = beta ** 2 if family == 'input' else beta
    return formal_exp([beta * a + amplitude * b for a, b in zip(h, extra)])


def inverse(f, r=3):
    h, g = formal_log(f), [Q(0)] * len(f)
    for n in range(2, len(f)):
        g[n] = h[n] - sum((2 * g[a] * g[b] for a, b in fibres(len(f) - 1, r).get(n, [])), Q(0))
    return formal_exp(g)


def generic():
    rng, rows = random.Random(2026100711), []
    for r in (1, 2, 3, 5):
        size = 512
        h = [Q(0)] * (size + 1)
        k = [Q(0)] * (size + 1)
        for a in range(2, 9):
            h[a], k[a] = Q(rng.choice((-3, -2, -1, 1, 2, 3)), rng.randint(2, 7)), Q(rng.choice((-2, -1, 1, 2)), rng.randint(2, 9))
        f, g = formal_exp(h), formal_exp(k)
        out = transform(f, r)
        pin, pout = transform(f, r, Q(1, 2)), transform(f, r, Q(1, 2), 'output')
        extra = couple(h, h, r)
        checks = {'triangular_inverse': inverse(out, r) == f,
                  'prefix_consistency': transform(f[:129], r) == out[:129],
                  'ordinary_output_square_root': convolve(pout, pout) == out,
                  'quadratic_input_root_amplitude': transform(normalized_power(f, Q(1, 2)), r) == pin,
                  'exact_root_anomaly': formal_log(pin) == [a + Q(-1, 4) * b for a, b in zip(formal_log(pout), extra)],
                  'odd_quotient_fixed': all(out[n] == f[n] for n in range(1, size + 1, 2)),
                  'ordinary_unit_group_homomorphism_rejected': transform(convolve(f, g), r) != convolve(out, transform(g, r)),
                  'universal_half_root_commutation_rejected': pin != pout}
        rows.append({'r': r, 'input_h': [str(v) for v in h], 'input_k': [str(v) for v in k],
                     'output_f': [str(v) for v in out], 'checks': checks})
    return {'records': rows, 'all_passed': all(all(row['checks'].values()) for row in rows)}


def sparse_couple(a, b, r):
    out = {}
    for x, v in a.items():
        for y, w in b.items():
            if x != y:
                n = index(x, y, r)
                out[n] = out.get(n, Q(0)) + v * w
    return {n: v for n, v in out.items() if v}


def inverse_tree_profile(seeds, r, leaves=6):
    terms, rows = {1: {n: Q(1) for n in seeds}}, []
    for ell in range(1, leaves + 1):
        overlaps = Q(0)
        if ell > 1:
            own = {}
            for left in range(1, ell):
                right = ell - left
                overlaps += sum((abs(v * terms[right].get(n, Q(0))) for n, v in terms[left].items()), Q(0))
                for n, v in sparse_couple(terms[left], terms[right], r).items():
                    own[n] = own.get(n, Q(0)) - v
            terms[ell] = {n: v for n, v in own.items() if v}
        rows.append({'leaves': ell, 'coefficients': {str(n): str(v) for n, v in sorted(terms[ell].items())},
                     'absolute_mass': str(sum((abs(v) for v in terms[ell].values()), Q(0))),
                     'ordered_equal_index_overlap_mass': str(overlaps)})
    return {'r': r, 'seeds': list(seeds), 'records': rows}


def tree_mass_grammar(profiles):
    records = []
    for multiplier, shift, offset in product((Q(1, 2), Q(1), Q(2)), (1, 2, 3), (-2, -1, 0)):
        def predicts(profile, ell):
            masses = {row['leaves']: Q(row['absolute_mass']) for row in profile['records']}
            raw = sum((masses[j] * masses[ell - j] for j in range(1, ell)), Q(0))
            return raw - (multiplier * Q(shift) ** (ell // 2 + offset) * masses[ell // 2] if ell % 2 == 0 else 0)
        training = all(predicts(p, ell) == Q(p['records'][ell - 1]['absolute_mass']) for p in profiles[:2] for ell in (2, 3, 4))
        fresh = training and all(predicts(p, ell) == Q(p['records'][ell - 1]['absolute_mass']) for p in profiles[:3] for ell in (5, 6))
        failure = next((ell for ell in range(2, 7) if predicts(profiles[3], ell) != Q(profiles[3]['records'][ell - 1]['absolute_mass'])), None) if fresh else None
        records.append({'multiplier': str(multiplier), 'base': shift, 'half_leaf_offset': offset,
                        'training_passed': training, 'fresh_two_seed_passed': fresh, 'three_seed_collision_first_failure': failure})
    # Equivalent parameter encodings reduce to the same 2^(k-1) factor.
    formulas = sorted(set((row['base'], Q(row['multiplier']) * Q(row['base']) ** row['half_leaf_offset']) for row in records if row['fresh_two_seed_passed']))
    universal = []
    for p in profiles:
        masses = {row['leaves']: Q(row['absolute_mass']) for row in p['records']}
        ok = all(masses[ell] == sum((masses[j] * masses[ell - j] for j in range(1, ell)), Q(0)) - Q(p['records'][ell - 1]['ordered_equal_index_overlap_mass']) for ell in range(2, 7))
        universal.append(ok)
    return {'models_scored': len(records), 'two_seed_canonical_formulas': [[b, str(v)] for b, v in formulas],
            'records': records, 'all_two_seed_survivors_rejected_on_collision_seeds': all(row['three_seed_collision_first_failure'] == 4 for row in records if row['fresh_two_seed_passed']),
            'universal_mass_minus_overlap_identity_passed': all(universal),
            'known_conditional_calibration': 'Asymmetric colored binary-tree law when distinct trees have distinct encoded indices; not a universal arithmetic inverse recurrence'}


def zeta_profiles():
    pp = prime_powers(4096)
    profiles = []
    for r in (1, 2, 3, 4, 5):
        values, queries = [Q(0)] * 8193, []
        for j, (a, _, e) in enumerate(pp):
            for b, _, f in pp[j + 1:]:
                n = index(a, b, r)
                if n <= 8192:
                    values[n] += Q(2, e * f)
                    queries.append({'index': n, 'a': a, 'b': b, 'ordered_pair_coefficient': str(Q(2, e * f))})
        profiles.append({'r': r, 'encoded_cutoff': 8192, 'complete_input_cutoff': 4096,
                         'queries': queries, 'coefficients': [str(v) for v in values],
                         'coefficient_six': str(values[6]), 'all_nonzero_indices_even': all(n % 2 == 0 for n, v in enumerate(values) if v)})
    return profiles


def autocorrelation_calibration():
    a, b = {2: Q(1), 3: Q(-2, 3), 5: Q(4, 7)}, {2: Q(-3, 5), 4: Q(2), 5: Q(1, 11)}
    records = []
    for d in range(1, 8):
        # Use a separate ordered enumeration as the profile oracle.
        correct = sum((x * y for n, x in a.items() for m, y in b.items() if abs(n - m) == d), Q(0))
        records.append({'gap': d, 'ordered_correlation': str(correct)})
    return {'a': {str(n): str(v) for n, v in a.items()}, 'b': {str(n): str(v) for n, v in b.items()},
            'records': records, 'calibration': 'classical bilinear additive correlation; diagonal gap zero excluded'}


def main():
    start = time.monotonic()
    laws = generic()
    trees = [inverse_tree_profile((2, 3), r) for r in (1, 2, 3)] + [inverse_tree_profile((2, 3, 5), 1)]
    grammar = tree_mass_grammar(trees)
    zeta = zeta_profiles()
    negative_input = [Q(0)] * 7
    negative_input[2], negative_input[3] = Q(1), Q(-1)
    negative_coefficient = couple(negative_input, negative_input)[6]
    passed = laws['all_passed'] and grammar['universal_mass_minus_overlap_identity_passed'] and grammar['all_two_seed_survivors_rejected_on_collision_seeds'] and all(row['all_nonzero_indices_even'] and row['coefficient_six'] == '2' for row in zeta) and negative_coefficient == -2
    out = {'generic_operator_laws': laws, 'inverse_tree_profiles': trees, 'inverse_mass_grammar': grammar,
           'zeta_profiles': zeta, 'known_additive_correlation_calibration': autocorrelation_calibration(),
           'gap_one_collision_control': {'r': 1, 'pairs': [[2, 5], [3, 5]], 'index': 30, 'global_prime_power_injectivity_rejected': True},
           'nonassociativity_control': {'r': 3, 'left': index(index(2, 3), 4), 'right': index(2, index(3, 4))},
           'diagonal_annihilation': True, 'exact_absolute_abscissa': 'max(2/(r+2),1/2)',
           'positive_semidefinite_kernel_rejected': {'input': {'2': '1', '3': '-1'}, 'negative_coefficient_six': str(negative_coefficient)},
           'endpoint_converges_iff': 'r=1 or r>=3', 'endpoint_divergence_r_two': True,
           'selected_r': 3, 'root_factor_holomorphic_domain': 'Re(s)>1/2',
           'root_factor_continuous_on_closed_halfplane_for_r_ge_three': True,
           'correction_holomorphic_across_critical_zero_disks_claimed': False,
           'counts_as_new_primitive': False, 'historical_novelty_established': False, 'new_RH_estimate_proved': False,
           'all_passed': passed, 'seconds': time.monotonic() - start}
    dest = BASE / 'gap-results'
    dest.mkdir(exist_ok=True)
    (dest / 'gap_search.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Gap exact source:', passed, 'seconds', out['seconds'], 'two-seed mass', [row['absolute_mass'] for row in trees[0]['records']], flush=True)
    assert passed


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Exact search for nonlinear logarithmic couplings with prime-sum indices."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb
from pathlib import Path
import json
import random
import time

from exact_arithmetic import convolve, factorization, formal_exp, formal_log, normalized_power, sequence

BASE = Path(__file__).resolve().parent


def index(x, y, r=3):
    return x * y * (x + y) ** r


@lru_cache(maxsize=None)
def fibres(cutoff, r):
    out = {}
    x = 2
    while index(x, x, r) <= cutoff:
        y = x
        while index(x, y, r) <= cutoff:
            out.setdefault(index(x, y, r), []).append((x, y))
            y += 1
        x += 1
    return out


def couple(a, b, r=3):
    assert len(a) == len(b) and a[1] == b[1] == 0
    out = [Q(0)] * len(a)
    for n, pairs in fibres(len(a) - 1, r).items():
        out[n] = sum((a[x] * b[y] if x == y else a[x] * b[y] + a[y] * b[x]
                      for x, y in pairs), Q(0))
    return out


def transform(f, r=3, beta=Q(1), family='input'):
    h = formal_log(f)
    extra = couple(h, h, r)
    c = beta ** 2 if family == 'input' else beta
    return formal_exp([beta * x + c * y for x, y in zip(h, extra)])


def inverse(f, r=3):
    h, out = formal_log(f), [Q(0)] * len(f)
    table = fibres(len(f) - 1, r)
    for n in range(2, len(f)):
        out[n] = h[n] - sum(((1 if x == y else 2) * out[x] * out[y]
                             for x, y in table.get(n, [])), Q(0))
    return formal_exp(out)


def sparse_couple(a, b, r):
    out = {}
    for x, v in a.items():
        for y, w in b.items():
            n = index(x, y, r)
            out[n] = out.get(n, Q(0)) + v * w
    return {n: v for n, v in out.items() if v}


def inverse_tree_profiles(r, leaves=6):
    rows, terms = [], {1: {2: Q(1)}}
    for ell in range(1, leaves + 1):
        if ell > 1:
            own = {}
            for left in range(1, ell):
                for n, v in sparse_couple(terms[left], terms[ell - left], r).items():
                    own[n] = own.get(n, Q(0)) - v
            terms[ell] = {n: v for n, v in own.items() if v}
        rows.append({'leaves': ell, 'support': {str(n): str(v) for n, v in sorted(terms[ell].items())},
                     'total_signed_mass': str(sum(terms[ell].values(), Q(0))),
                     'support_count': len(terms[ell])})
    return rows


def catalan_grammar(profiles):
    values = {r['leaves']: abs(Q(r['total_signed_mass'])) for r in profiles}
    records = []
    for a, b, c, d in product(range(-2, 6), repeat=4):
        if c == d == 0:
            continue
        def predict(ell):
            den = c * ell + d
            return values[ell] * Q(a * ell + b, den) if den else None
        train = all(predict(ell) == values[ell + 1] for ell in (1, 2))
        failed = next((ell for ell in (3, 4, 5) if predict(ell) != values[ell + 1]), None) if train else None
        records.append({'a': a, 'b': b, 'c': c, 'd': d, 'training_passed': train,
                        'held_out_passed': train and failed is None, 'first_counterexample': failed})
    survivors = [r for r in records if r['held_out_passed']]
    return {'models_scored': len(records), 'training_fits': sum(r['training_passed'] for r in records),
            'survivors': survivors, 'records': records,
            'known_operator_calibration': 'Catalan C_l/C_(l-1)=(4*l-2)/(l+1); equivalent rational programs count once'}


def generic_controls():
    rng, rows = random.Random(2026100707), []
    for r in (0, 1, 2, 3):
        cutoff = 1024
        inputs = []
        for _ in range(2):
            h = [Q(0)] * (cutoff + 1)
            for n in range(2, 10):
                h[n] = Q(rng.choice((-3, -2, -1, 1, 2, 3)), rng.randint(2, 7))
            inputs.append(formal_exp(h))
        f, g = inputs
        pf = transform(f, r)
        beta, h = Q(1, 2), formal_log(f)
        extra = couple(h, h, r)
        pin, pout = transform(f, r, beta, 'input'), transform(f, r, beta, 'output')
        checks = {'exact_inverse': inverse(pf, r) == f,
                  'prefix_consistency': transform(f[:129], r) == pf[:129],
                  'output_root_law': convolve(pout, pout) == pf,
                  'input_power_formula': transform(normalized_power(f, beta), r) == pin,
                  'root_anomaly': formal_log(pin) == [x + beta * (beta - 1) * y
                                                   for x, y in zip(formal_log(pout), extra)],
                  'odd_quotient_fixed' if r else 'r_zero_odd_quotient_control': all(pf[n] == f[n] for n in range(1, len(f), 2)) if r else any(pf[n] != f[n] for n in range(1, len(f), 2)),
                  'input_root_commutation_rejected': pin != pout,
                  'ordinary_group_homomorphism_rejected': transform(convolve(f, g), r) != convolve(pf, transform(g, r))}
        rows.append({'r': r, 'cutoff': cutoff, 'input_f': [str(x) for x in f],
                     'input_g': [str(x) for x in g], 'output_f': [str(x) for x in pf], 'checks': checks})
    return {'records': rows, 'all_passed': all(all(row['checks'].values()) for row in rows)}


def homogeneity_grammar():
    # A coordinate-polynomial toy grammar tests the universal half-root
    # constraint after conjugation by arithmetic LOG/EXP. No zeta labels.
    records = []
    training, fresh = (Q(1), Q(2)), (Q(-3, 7), Q(5, 11))
    for coefficients in product(range(-2, 3), repeat=5):
        def value(t):
            return sum((Q(c) * t ** j for j, c in enumerate(coefficients)), Q(0))
        train = all(value(t / 2) == value(t) / 2 for t in training)
        held = train and all(value(t / 2) == value(t) / 2 for t in fresh)
        records.append({'coefficients': list(coefficients), 'training_passed': train, 'held_out_passed': held})
    surviving = [r for r in records if r['held_out_passed']]
    return {'models_scored': len(records), 'training_fits': sum(r['training_passed'] for r in records),
            'survivors': surviving, 'records': records,
            'all_survivors_linear': all(all(c == 0 for j, c in enumerate(r['coefficients']) if j != 1) for r in surviving),
            'theorem_scope': 'Coefficient-local maps polynomial in input coefficients; homogeneous-part comparison extends to formal maps at the unit'}


def amplitude_grammar():
    # The log-coordinate at index Phi(2,2) is quadratic in beta for an
    # impulse source. Score polynomials, holding out two rational roots.
    train, fresh = (Q(1), Q(1, 2)), (Q(1, 4), Q(2, 3))
    records = []
    for c in product(range(-2, 3), repeat=4):
        value = lambda t: sum((Q(v) * t ** j for j, v in enumerate(c)), Q(0))
        fitted = all(value(t) == t ** 2 for t in train)
        held = fitted and all(value(t) == t ** 2 for t in fresh)
        records.append({'coefficients': list(c), 'training_passed': fitted, 'held_out_passed': held})
    return {'models_scored': len(records), 'training_fits': sum(x['training_passed'] for x in records),
            'survivors': [x for x in records if x['held_out_passed']], 'records': records}


def structural_controls():
    roots = []
    for r in range(7):
        abscissa = Q(2, r + 2)
        roots.append({'r': r, 'first_coupling_index': index(2, 2, r),
                      'sufficient_correction_halfplane': str(abscissa),
                      'certificate_crosses_critical_line': abscissa < Q(1, 2),
                      'known_pure_D_product': r == 0,
                      'continuation_outside_sufficient_domain_rejected': False})
    assoc = []
    for r in (1, 2, 3):
        lhs, rhs = index(index(2, 2, r), 3, r), index(2, index(2, 3, r), r)
        assoc.append({'r': r, 'left_index': lhs, 'right_index': rhs, 'associativity_rejected': lhs != rhs})
    return {'domain_grammar': roots, 'nonassociativity_controls': assoc,
            'prime_relabel_counterexample': {'r': 3, 'source_prime': 2, 'target_prime': 3,
                                             'source_interaction': index(2, 2), 'relabeled_interaction': 3 ** 8,
                                             'interaction_after_relabel': index(3, 3),
                                             'prime_relabel_invariance_rejected': 3 ** 8 != index(3, 3)},
            'selected_r': 3, 'selection_rule': 'Least r in xy*(x+y)^r whose AM-GM certificate covers Re(s)>1/2 and a neighborhood beyond it'}


def zeta_profiles():
    cutoff, profiles = 2048, []
    h = [Q(0)] * (cutoff + 1)
    for n in range(2, cutoff + 1):
        f = factorization(n)
        if len(f) == 1:
            h[n] = Q(1, next(iter(f.values())))
    extra = couple(h, h)
    for beta, family in product((Q(1), Q(1, 2), Q(1, 4), Q(2, 3)), ('input', 'output')):
        c = beta ** 2 if family == 'input' else beta
        values = formal_exp([beta * x + c * y for x, y in zip(h, extra)])
        profiles.append({'beta': str(beta), 'family': family, 'cutoff': cutoff,
                         'coefficients': [str(x) for x in values],
                         'all_coefficients_nonnegative': all(x >= 0 for x in values)})
    return {'profiles': profiles, 'log_correction_coefficients': {str(n): str(v) for n, v in enumerate(extra) if v},
            'first_zeta_input_half_root_disagreement': {'n': 256, 'input_minus_output': '-1/4'},
            'nonlinear_scaling_rejected': next(x for x in profiles if x['beta'] == '1/2' and x['family'] == 'input')['coefficients'][256]
                                          != next(x for x in profiles if x['beta'] == '1/2' and x['family'] == 'output')['coefficients'][256]}


def odd_quotient_controls(source):
    records = []
    for row in source['generic_operator_checks']['records']:
        r = row['r']
        f, pf = [list(map(Q, row[k])) for k in ('input_f', 'output_f')]
        equal = all(f[n] == pf[n] for n in range(1, len(f), 2))
        records.append({'r': r, 'odd_quotient_fixed': equal, 'all_passed': equal if r else not equal})
    integer_zeta = next(row for row in source['zeta_profiles']['profiles'] if row['beta'] == '1' and row['family'] == 'input')
    at256 = Q(integer_zeta['coefficients'][256])
    coefficients = integer_zeta['coefficients']
    nonmultiplicative = Q(coefficients[750]) == 3 and Q(coefficients[2]) == Q(coefficients[375]) == 1
    # At an odd output, EVERY input pair is excluded by parity. This
    # certificate is an exact fibre check, not a new full-series run.
    from exact_arithmetic import factorization
    divisors = [1]
    for p, e in factorization(6561).items():
        divisors = [d * p ** j for d in divisors for j in range(e + 1)]
    no_odd_fibre = not any(index(x, y) == 6561 for x in divisors for y in divisors if x >= 2 and y >= 2)
    return {'records': records, 'universal_law': 'Restriction to odd indices satisfies O(P_r(f))=O(f) for all r>=1',
            'zeta_actual_prime_relabel_counterexample': {'input': 'u(n)=1', 'n': 256, 'operator_coefficient': str(at256),
                                                        'swap_primes': [2, 3], 'relabeled_n': 6561, 'relabeled_operator_coefficient': '1',
                                                        'odd_output_fibre_exactly_empty': no_odd_fibre,
                                                        'prime_relabel_invariance_rejected': at256 != 1 and no_odd_fibre},
            'zeta_actual_nonmultiplicativity_counterexample': {'coprime_indices': [2, 375],
                                                              'factor_coefficients': [coefficients[2], coefficients[375]],
                                                              'product_index': 750, 'product_coefficient': coefficients[750],
                                                              'multiplicativity_rejected': nonmultiplicative},
            'all_passed': all(row['all_passed'] for row in records) and at256 == 2 and no_odd_fibre and nonmultiplicative}


def main():
    start = time.monotonic()
    tree = {str(r): inverse_tree_profiles(r) for r in (0, 3)}
    generic = generic_controls()
    hgram, amplitude, cat = homogeneity_grammar(), amplitude_grammar(), catalan_grammar(tree['3'])
    structural, zeta = structural_controls(), zeta_profiles()
    passed = (generic['all_passed'] and hgram['all_survivors_linear'] and len(amplitude['survivors']) == 1
              and bool(cat['survivors']) and all(r['associativity_rejected'] for r in structural['nonassociativity_controls'])
              and structural['prime_relabel_counterexample']['prime_relabel_invariance_rejected']
              and zeta['nonlinear_scaling_rejected'] and all(r['all_coefficients_nonnegative'] for r in zeta['profiles']))
    out = {'operator': 'P_r(f)=EXP_D(LOG_D f+K_r(LOG_D f,LOG_D f)); Phi_r(x,y)=xy(x+y)^r',
           'generic_operator_checks': generic, 'universal_root_constraint_grammar': hgram,
           'input_root_amplitude_grammar': amplitude, 'inverse_tree_profiles': tree,
           'inverse_mass_recurrence_grammar': cat, 'structural_controls': structural, 'zeta_profiles': zeta,
           'historical_novelty_established': False, 'new_RH_estimate_proved': False,
           'all_passed': passed, 'seconds': time.monotonic() - start}
    out['odd_quotient_controls'] = odd_quotient_controls(out)
    out['all_passed'] = out['all_passed'] and out['odd_quotient_controls']['all_passed']
    dest = BASE / 'pair-results'
    dest.mkdir(exist_ok=True)
    (dest / 'pair_search.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Nonlinear pair search:', out['all_passed'], 'seconds', out['seconds'], flush=True)
    assert out['all_passed']


if __name__ == '__main__':
    main()

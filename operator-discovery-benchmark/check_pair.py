#!/usr/bin/env python3
"""Independent output-fibre, divisor-recursion and ordered-tree pair audit."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb
from pathlib import Path
import json
import time

from check_joint_size import divisors, conv
from check_mixed_index import d_log, d_exp

BASE = Path(__file__).resolve().parent


@lru_cache(maxsize=None)
def output_fibre(n, r):
    # Decode the OUTPUT integer through its divisors, in contrast to
    # scattering input pairs in the production search.
    return tuple((x, y) for x in divisors(n) if x >= 2
                 for y in divisors(n // x) if y >= 2
                 and (x + y) ** r == n // (x * y))


def pairing(a, b, r=3):
    return [Q(0), Q(0)] + [sum((a[x] * b[y] for x, y in output_fibre(n, r)), Q(0))
                           for n in range(2, len(a))]


def apply(f, r=3, beta=Q(1), family='input'):
    h = d_log(f)
    extra = pairing(h, h, r)
    c = beta * beta if family == 'input' else beta
    return d_exp([beta * x + c * y for x, y in zip(h, extra)])


def generic(source):
    records = []
    for row in source['generic_operator_checks']['records']:
        f, g = [list(map(Q, row[key])) for key in ('input_f', 'input_g')]
        r = row['r']
        pf, beta = apply(f, r), Q(1, 2)
        h, recovered = d_log(pf), [Q(0)] * len(pf)
        for n in range(2, len(pf)):
            recovered[n] = h[n] - sum((recovered[x] * recovered[y] for x, y in output_fibre(n, r)), Q(0))
        pin, pout = apply(f, r, beta, 'input'), apply(f, r, beta, 'output')
        extra = pairing(d_log(f), d_log(f), r)
        checks = {'production_coefficients': pf == list(map(Q, row['output_f'])),
                  'exact_inverse': d_exp(recovered) == f,
                  'prefix_consistency': apply(f[:129], r) == pf[:129],
                  'output_root_law': conv(pout, pout, lambda x, y: 1) == pf,
                  'input_power_formula': apply(d_exp([beta * x for x in d_log(f)]), r) == pin,
                  'root_anomaly': d_log(pin) == [x + beta * (beta - 1) * y for x, y in zip(d_log(pout), extra)],
                  'input_root_commutation_rejected': pin != pout,
                  'ordinary_group_homomorphism_rejected': apply(conv(f, g, lambda x, y: 1), r) != conv(pf, apply(g, r), lambda x, y: 1)}
        records.append({'r': r, 'checks': checks, 'all_passed': all(checks.values())})
    return records


@lru_cache(maxsize=None)
def ordered_trees(leaves):
    if leaves == 1:
        return (None,)
    return tuple((left, right) for a in range(1, leaves)
                 for left in ordered_trees(a) for right in ordered_trees(leaves - a))


def tree_value(tree, r):
    if tree is None:
        return 2
    x, y = (tree_value(child, r) for child in tree)
    return (x + y) ** r * y * x


def trees(source):
    records = []
    for r, profiles in source['inverse_tree_profiles'].items():
        for row in profiles:
            ell, support = row['leaves'], {}
            sign = (-1) ** (ell - 1)
            for tree in ordered_trees(ell):
                value = str(tree_value(tree, int(r)))
                support[value] = support.get(value, Q(0)) + sign
            expected = {n: Q(v) for n, v in row['support'].items()}
            mass = Q(sign * comb(2 * ell - 2, ell - 1), ell)
            records.append(support == expected and sum(support.values(), Q(0)) == mass == Q(row['total_signed_mass'])
                           and len(support) == row['support_count'])
    return all(records)


def grammar(source):
    for row in source['universal_root_constraint_grammar']['records']:
        def defect(t):
            return sum((Q(c) * (Q(1, 2) ** j - Q(1, 2)) * t ** j
                        for j, c in enumerate(row['coefficients'])), Q(0))
        train = all(defect(t) == 0 for t in (Q(1), Q(2)))
        fresh = train and all(defect(t) == 0 for t in (Q(-3, 7), Q(5, 11)))
        assert train == row['training_passed'] and fresh == row['held_out_passed']
    assert source['universal_root_constraint_grammar']['all_survivors_linear']
    for row in source['input_root_amplitude_grammar']['records']:
        value = lambda t: sum((Q(c) * t ** j for j, c in enumerate(row['coefficients'])), Q(0))
        train = all(value(t) == t ** 2 for t in (Q(1), Q(1, 2)))
        fresh = train and all(value(t) == t ** 2 for t in (Q(1, 4), Q(2, 3)))
        assert train == row['training_passed'] and fresh == row['held_out_passed']
    mass = lambda ell: Q(comb(2 * ell - 2, ell - 1), ell)
    for row in source['inverse_mass_recurrence_grammar']['records']:
        def passes(ell):
            den = row['c'] * ell + row['d']
            return bool(den) and mass(ell) * Q(row['a'] * ell + row['b'], den) == mass(ell + 1)
        train = all(passes(ell) for ell in (1, 2))
        failed = next((ell for ell in (3, 4, 5) if not passes(ell)), None) if train else None
        assert train == row['training_passed'] and (train and failed is None) == row['held_out_passed']
        assert failed == row['first_counterexample']
    return True


def zeta(source):
    rows, source_profiles = [], source['zeta_profiles']['profiles']
    cutoff = source_profiles[0]['cutoff']
    u = [Q(0)] + [Q(1)] * cutoff
    extra = pairing(d_log(u), d_log(u))
    expected_extra = {str(n): str(x) for n, x in enumerate(extra) if x}
    for row in source_profiles:
        own = apply(u, beta=Q(row['beta']), family=row['family'])
        rows.append(own == list(map(Q, row['coefficients'])) and all(x >= 0 for x in own))
    pin, pout = (apply(u, beta=Q(1, 2), family=f) for f in ('input', 'output'))
    mismatch = next(n for n in range(1, len(pin)) if pin[n] != pout[n])
    return all(rows) and expected_extra == source['zeta_profiles']['log_correction_coefficients'] and mismatch == 256 and pin[256] - pout[256] == Q(-1, 4)


def structural(source):
    s = source['structural_controls']
    for row in s['domain_grammar']:
        r = row['r']
        assert row['first_coupling_index'] == 4 ** (r + 1)
        assert Q(row['sufficient_correction_halfplane']) == Q(1, 1 + Q(r, 2))
        assert row['certificate_crosses_critical_line'] == (r >= 3)
        assert not row['continuation_outside_sufficient_domain_rejected']
    for row in s['nonassociativity_controls']:
        phi = lambda x, y: (x + y) ** row['r'] * x * y
        assert row['left_index'] == phi(phi(2, 2), 3) != phi(2, phi(2, 3)) == row['right_index']
    p = s['prime_relabel_counterexample']
    return p['source_interaction'] == 256 and p['relabeled_interaction'] == 6561 and p['interaction_after_relabel'] == 1944


def r_zero_closed_inverse(source):
    # Universal scalar Catalan inverse, calibrated on h=t*delta_2.
    for row in source['inverse_tree_profiles']['0']:
        ell = row['leaves']
        assert set(row['support']) == {str(2 ** ell)}
        assert Q(row['support'][str(2 ** ell)]) == (-1) ** (ell - 1) * Q(comb(2 * ell - 2, ell - 1), ell)
    return True


def odd_quotient(source):
    rows = source['odd_quotient_controls']
    for row, original in zip(rows['records'], source['generic_operator_checks']['records']):
        f, pf = [list(map(Q, original[k])) for k in ('input_f', 'output_f')]
        equal = all(f[n] == pf[n] for n in range(1, len(f), 2))
        assert equal == row['odd_quotient_fixed'] and (equal if row['r'] else not equal)
    zeta = rows['zeta_actual_prime_relabel_counterexample']
    integer = next(r for r in source['zeta_profiles']['profiles'] if r['beta'] == '1' and r['family'] == 'input')
    coefficients = list(map(Q, integer['coefficients']))
    nonmultiplicative = coefficients[750] == 3 and coefficients[2] * coefficients[375] == 1
    return coefficients[256] == 2 and not output_fibre(6561, 3) and zeta['relabeled_operator_coefficient'] == '1' and nonmultiplicative


def main():
    start = time.monotonic()
    source = json.loads((BASE / 'pair-results/pair_search.json').read_text())
    rows = generic(source)
    checks = {'independent_output_fibres_and_generic_inverse_root_anomaly': all(x['all_passed'] for x in rows),
              'all_grammar_decisions_recomputed': grammar(source), 'ordered_binary_trees_reproduce_sparse_inverse': trees(source),
              'actual_zeta_profiles_and_half_root_counterexample': zeta(source),
              'domain_nonassociativity_and_prime_relabel_controls': structural(source),
              'known_Catalan_square_root_inverse_r_zero': r_zero_closed_inverse(source),
              'odd_quotient_and_actual_zeta_prime_relabel_counterexample': odd_quotient(source)}
    result = {'checks': checks, 'all_passed': all(checks.values()), 'generic_records': rows,
              'production_imports': False, 'seconds': time.monotonic() - start}
    (BASE / 'pair-results/pair_verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print('Independent pair exact audit:', sum(checks.values()), '/', len(checks), 'seconds', result['seconds'], flush=True)
    assert result['all_passed']


if __name__ == '__main__':
    main()

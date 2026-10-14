#!/usr/bin/env python3
"""Independent Newton interpolation, log/exp and divisor-root verification."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb, factorial
from pathlib import Path
import json
import time

from check_mixed_index import d_log, d_exp
from check_joint_size import divisors


BASE = Path(__file__).resolve().parent


def word_value(n, word):
    for a in word:
        n = n * (n + a)
    return n


def word_weight(m, word):
    out = 1
    for a in word:
        out *= (-1) ** (m - a) * comb(m, a)
    return out


@lru_cache(maxsize=None)
def interpolated(m, k):
    out = []
    degree = 2 ** k
    for word in product(range(m + 1), repeat=k):
        table = [Q(word_value(n, word)) for n in range(degree + 1)]
        polynomial, falling = [Q(0)] * (degree + 1), [Q(1)]
        for j in range(degree + 1):
            for i, value in enumerate(falling):
                polynomial[i] += table[0] * value / factorial(j)
            table = [b - a for a, b in zip(table, table[1:])]
            nxt = [Q(0)] * (len(falling) + 1)
            for i, value in enumerate(falling):
                nxt[i] -= j * value
                nxt[i + 1] += value
            falling = nxt
        assert polynomial[-1] == 1 and polynomial[0] == 0
        out.append((word, word_weight(m, word), polynomial[::-1]))
    return out


def coefficient_series(m, k, s, cutoff):
    out = [Q(0)] * (cutoff + 1)
    for _, weight, h in interpolated(m, k):
        log = [Q(0)] * (cutoff + 1)
        for n in range(1, cutoff + 1):
            own = h[n] if n < len(h) else Q(0)
            log[n] = own - sum((Q(j, n) * log[j] * h[n - j]
                              for j in range(1, n) if n - j < len(h)), Q(0))
        power = [Q(1)]
        for n in range(1, cutoff + 1):
            power.append(-s * sum((Q(j, n) * log[j] * power[n - j] for j in range(1, n + 1)), Q(0)))
        out = [x + weight * y for x, y in zip(out, power)]
    return out


def push(h, m, k):
    out = [Q(0)] * len(h)
    for n in range(2, len(h)):
        if n ** (2 ** k) >= len(h):
            break
        for word in product(range(m + 1), repeat=k):
            image = word_value(n, word)
            if image < len(h):
                out[image] += word_weight(m, word) * h[n]
    return out


def arithmetic_profile(beta, cutoff, m=2, k=2):
    u = [Q(0)] + [Q(1)] * cutoff
    log = d_log(u)
    extra = push(log, m, k)
    return d_exp([beta * (x + y) for x, y in zip(log, extra)])


def d_product(a, b):
    return [Q(0)] + [sum((a[d] * b[n // d] for d in divisors(n)), Q(0)) for n in range(1, len(a))]


def generic_checks(source):
    passed = []
    for row in source['generic_operator_checks']['records']:
        f, g = [list(map(Q, row[key])) for key in ('input_f', 'input_g')]
        m, k = row['m'], row['k']
        def apply(a, beta=Q(1)):
            h = d_log(a)
            extra = push(h, m, k)
            return d_exp([beta * (x + y) for x, y in zip(h, extra)])
        pf, pg = apply(f), apply(g)
        term = d_log(pf)
        inverse_log, sign = list(term), -1
        while any(term):
            term = push(term, m, k)
            inverse_log = [x + sign * y for x, y in zip(inverse_log, term)]
            sign *= -1
        root = apply(f, Q(1, 2))
        passed.append(pf == list(map(Q, row['output_f'])) and d_exp(inverse_log) == f
                      and apply(d_product(f, g)) == d_product(pf, pg)
                      and d_product(root, root) == pf
                      and root == d_exp([x / 2 for x in d_log(pf)])
                      and apply(f[:33]) == pf[:33])
    return all(passed)


def grammar_checks(source, profiles):
    lookup = {(r['difference_order'], r['iterations'], Q(r['s'])): coefficients
              for r, coefficients in profiles}
    weight_records = source['finite_difference_calibration']['records']
    for r in weight_records:
        w = r['weights']
        training = sum(w) == sum(-a * w[a] for a in range(4)) == 0
        fresh = training and sum(Q(3, 8) * a * a * w[a] for a in range(4)) == 0
        assert training == r['training_passed'] and fresh == r['held_out_passed']
    order_records = source['cancellation_order_grammar']['records']
    orders = {(m, k): next(j for j, value in enumerate(v) if value) for (m, k, s), v in lookup.items()}
    for r in order_records:
        predicts = lambda m, k: r['a_m_2k'] * m * 2 ** k + r['b_m'] * m + r['c_k'] * k + r['d']
        training = all(predicts(m, k) == orders[m, k] for m, k in ((1, 1), (1, 2), (2, 1)))
        failure = next(([m, k] for m, k in orders if predicts(m, k) != orders[m, k]), None) if training else None
        assert training == r['training_passed'] and failure == r['first_counterexample']
        assert (training and failure is None) == r['held_out_passed']
    leading = {(m, k, s): next(x for x in coefficients if x) for (m, k, s), coefficients in lookup.items()}
    pairs = [(m, k, s, old, leading[m, k + 1, s]) for (m, k, s), old in leading.items() if (m, k + 1, s) in leading]
    train = [x for x in pairs if x[0] == x[1] == 1][:2]
    for r in source['leading_recurrence_grammar']['records']:
        def predicts(item):
            m, k, s, old, _ = item
            base = r['a_degree_s'] * 2 ** k * s + r['b_previous_order'] * m * (2 ** k - 1) + r['c']
            value = old * (-1) ** m
            for j in range(m):
                value *= base + j
            return value
        training = all(predicts(x) == x[-1] for x in train)
        failure = next(([m, k, str(s)] for m, k, s, old, new in pairs if predicts((m, k, s, old, new)) != new), None) if training else None
        assert training == r['training_passed'] and failure == r['counterexample']
        assert (training and failure is None) == r['held_out_passed']
    return True


def sparse_triangular(source):
    row = source['deep_sparse_inverse_control']
    cutoff, seed = row['cutoff'], {int(n): Q(x) for n, x in row['seed'].items()}
    def image(values):
        out = {}
        for n, value in values.items():
            for word in product(range(3), repeat=2):
                index = word_value(n, word)
                if index <= cutoff:
                    out[index] = out.get(index, Q(0)) + word_weight(2, word) * value
        return {n: x for n, x in out.items() if x}
    residual = dict(seed)
    for n, value in image(seed).items():
        residual[n] = residual.get(n, Q(0)) + value
    h, recovered = dict(residual), {}
    while residual:
        n = min(residual)
        value = residual.pop(n)
        recovered[n] = value
        for index, x in image({n: value}).items():
            residual[index] = residual.get(index, Q(0)) - x
        residual = {j: x for j, x in residual.items() if x}
    short = dict(h)
    for n, x in image(h).items():
        short[n] = short.get(n, Q(0)) - x
    short = {n: x for n, x in short.items() if x}
    wrong = row['first_wrong_coefficient']
    return recovered == seed and short != seed and short[wrong['n']] == Q(wrong['value']) and row['nonzero_inverse_powers_required'] == 2


def main():
    started = time.monotonic()
    source = json.loads((BASE / 'difference-results/difference_search.json').read_text())
    profiles, exact = [], True
    for row in source['exact_kernel_profiles']:
        values = coefficient_series(row['difference_order'], row['iterations'], Q(row['s']), len(row['coefficients']) - 1)
        exact &= values == list(map(Q, row['coefficients']))
        profiles.append((row, values))
    zeta = True
    for row in source['zeta_checks']['profiles']:
        values = arithmetic_profile(Q(row['beta']), row['cutoff'])
        zeta &= values == list(map(Q, row['coefficients']))
    # s=0 annihilates the kernel identically, so a generic exact-order
    # statement must not be asserted at every complex parameter.
    special = all(not any(coefficient_series(m, k, Q(0), 32)) for m, k in ((1, 1), (1, 2), (2, 2), (3, 3)))
    checks = {'all_interpolated_word_kernel_coefficients': exact,
              'all_three_grammar_decisions_independently_recomputed': grammar_checks(source, profiles),
              'all_generic_ordinary_D_root_group_and_inverse_laws': generic_checks(source),
              'deep_inverse_by_triangular_elimination_and_wrong_short_inverse': sparse_triangular(source),
              'all_zeta_profiles_by_independent_divisor_Euler_recursions': zeta,
              'exceptional_s_zero_rejects_unqualified_exact_cancellation_order': special,
              'third_forward_difference_rediscovered': source['finite_difference_calibration']['survivors'][0]['weights'] == [-1, 3, -3, 1]}
    result = {'checks': checks, 'all_passed': all(checks.values()), 'no_production_imports': True,
              'word_polynomial_method': 'Newton interpolation of exact integer image values',
              'proof': 'difference_proof.txt', 'elapsed_seconds': time.monotonic() - started}
    (BASE / 'difference-results/difference_verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Independent difference audit: {sum(checks.values())}/{len(checks)}; elapsed={result["elapsed_seconds"]:.2f}s')
    assert result['all_passed']


if __name__ == '__main__':
    main()

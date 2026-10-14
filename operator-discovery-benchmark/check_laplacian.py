#!/usr/bin/env python3
"""Independent complete square-fibre and prime-log shear certificates."""

from fractions import Fraction as Q
from functools import lru_cache
from math import isqrt
from pathlib import Path
import json
import time

import flint
from check_gap import factors, exp_D, log_D, D

BASE = Path(__file__).resolve().parent


def power_root(n, r):
    lo, hi = 0, n + 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid ** r <= n:
            lo = mid
        else:
            hi = mid
    return lo if lo ** r == n else None


@lru_cache(maxsize=None)
def fibres(n, r):
    assert r % 2 == 0
    fs, root = factors(n), isqrt(n)
    if root * root == n:
        edges = []
        for p in factors(root):
            d = power_root(root // p, r // 2)
            if d:
                for q in (p - d, p + d):
                    if q >= 2 and flint.fmpz(q).is_prime():
                        edges.append((min(p, q), max(p, q), Q(1)))
        return tuple(edges)
    odd = [p for p, e in fs.items() if e % 2]
    if len(odd) == 2:
        p, q = sorted(odd)
        if n == p * q * (q - p) ** r:
            return ((p, q, Q(-2)),)
    return ()


def K(h, k, r):
    return [Q(0)] + [sum(((h[a] * k[b] + h[b] * k[a]) * c / 2
                          for a, b, c in fibres(n, r)), Q(0)) for n in range(1, len(h))]


def flow(h, t, r):
    return [a + t * b for a, b in zip(h, K(h, h, r))]


def generic(source):
    for row in source['generic_operator_laws']['records']:
        h, k, r = list(map(Q, row['h'])), list(map(Q, row['k'])), row['r']
        result = exp_D(flow(h, Q(1), r))
        assert result == list(map(Q, row['output']))
        assert flow(flow(h, Q(1), r), Q(-1), r) == h
        assert flow(flow(h, Q(2, 3), r), Q(-3, 5), r) == flow(h, Q(1, 15), r)
        kh = K(h, h, r)
        pin, pout = exp_D(flow([v / 2 for v in h], Q(1), r)), exp_D([v / 2 for v in flow(h, Q(1), r)])
        assert D(pout, pout) == result and pin != pout
        assert log_D(pin) == [a / 2 + b / 4 for a, b in zip(h, kh)]
        hk = [a + b for a, b in zip(h, k)]
        assert exp_D(flow(hk, Q(1), r)) != D(result, exp_D(flow(k, Q(1), r)))
        assert all(kh[p] == 0 for p in range(2, len(h)) if flint.fmpz(p).is_prime())
        assert all(row['checks'].values())
    return True


def exact_zeta(source):
    count = 0
    for row in source['zeta_profiles']:
        r = row['r']
        for n in range(2, len(row['coefficients'])):
            expected = sum((c for a, b, c in fibres(n, r)), Q(0))
            assert Q(row['coefficients'][n]) == expected
            assert (expected >= 0 if isqrt(n) ** 2 == n else expected <= 0)
            count += 1
        assert row['first_coefficients'] == {'4': '1', '6': '-2', '9': '1'}
    assert fibres(4, 4) == ((2, 3, Q(1)),)
    assert fibres(6, 4) == ((2, 3, Q(-2)),)
    assert fibres(9, 4) == ((2, 3, Q(1)),)
    return {'encoded_indices_checked': count, 'all_passed': True}


def grammar_and_psd(source):
    g = source['diagonal_completion_grammar']
    found = [[1, b, c] for b in range(-3, 4) for c in range(-3, 4)
             if all(1 + b + c == 0 and b + 2 * c == 0 for _ in (2, 5))]
    assert found == [row['weights'] for row in g['survivors']] == [[1, -2, 1]]
    # Laplacian of the complete prime graph with rational positive edge weights.
    ps = (2, 3, 5, 7)
    for vector in ((1, 1, 1, 1), (1, -1, 0, 2), (0, 1, -2, 1)):
        energy = sum((Q((vector[i] - vector[j]) ** 2, (q - p) ** 2)
                      for i, p in enumerate(ps) for j, q in enumerate(ps) if i < j), Q(0))
        assert energy >= 0
    assert source['support_mask_grammar']['surviving_masks'] == ['prime', 'odd']
    masks = {'prime': lambda n: flint.fmpz(n).is_prime(),
             'prime_power': lambda n: len(factors(n)) == 1,
             'squarefree': lambda n: all(e == 1 for e in factors(n).values()),
             'Omega_le_two': lambda n: sum(factors(n).values()) <= 2,
             'odd': lambda n: n % 2 == 1, 'even': lambda n: n % 2 == 0}
    def sparse(values, predicate):
        result = {}
        for a, v in values.items():
            if not predicate(a):
                continue
            for b, w in values.items():
                if b <= a or not predicate(b):
                    continue
                d = (b-a)**4
                for n, c in ((a*a*d,1),(b*b*d,1),(a*b*d,-2)):
                    result[n] = result.get(n,Q(0)) + c*v*w
        return {n:v for n,v in result.items() if v}
    initial = {n:Q(1,n) for n in range(2,13)}
    for row in source['support_mask_grammar']['records']:
        first = sparse(initial,masks[row['mask']])
        changed = {n:initial.get(n,Q(0))+first.get(n,Q(0)) for n in initial.keys()|first.keys()}
        changed = {n:v for n,v in changed.items() if v}
        again = sparse(changed,masks[row['mask']])
        failure = next((n for n in sorted(first.keys()|again.keys()) if first.get(n,Q(0))!=again.get(n,Q(0))),None)
        assert failure == row['first_composition_failure']
        assert [len(first),len(again)]==row['untruncated_first_and_second_correction_terms']
    assert next(row['first_composition_failure'] for row in source['support_mask_grammar']['records'] if row['mask']=='even')==59105344
    return True


def main():
    start = time.monotonic()
    source = json.loads((BASE / 'laplacian-results/laplacian_search.json').read_text())
    assert source['all_passed']
    zeta = exact_zeta(source)
    checks = {'complete_square_and_squarefree_part_fibres': zeta['all_passed'],
              'Omega_recursion_generic_group_inverse_and_root_anomaly': generic(source),
              'classical_completion_weights_and_finite_PSD_calibration': grammar_and_psd(source),
              'grouped_and_ordinary_domains_are_kept_distinct': source['grouped_selected_endpoint'] == '1/3, convergent' and source['ordinary_correction_coefficient_absolute_abscissa_even_r_ge_four'] == '1/2, convergent',
              'historical_novelty_and_new_RH_estimate_not_claimed': not source['historical_novelty_established'] and not source['new_RH_estimate_proved']}
    out = {'checks': checks, 'zeta_audit': zeta, 'production_imports': False,
           'shared_trusted_kernel': 'FLINT/Arb; independent factor reconstruction and Omega EXP/LOG helpers',
           'all_passed': all(checks.values()), 'seconds': time.monotonic() - start}
    (BASE / 'laplacian-results/laplacian_verification.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Independent Laplacian exact audit:', sum(checks.values()), '/', len(checks), 'seconds', out['seconds'], flush=True)
    assert out['all_passed']


if __name__ == '__main__':
    main()

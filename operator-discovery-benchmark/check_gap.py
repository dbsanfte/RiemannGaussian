#!/usr/bin/env python3
"""Independent difference-discriminant, Omega-recursion and density audit."""

from fractions import Fraction as Q
from functools import lru_cache
from math import isqrt, ceil
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
    reconstructed = 1
    for p, e in fs.items():
        reconstructed *= p ** e
    assert reconstructed == n
    return fs


@lru_cache(maxsize=None)
def divisors(n):
    ds = [1]
    for p, e in factors(n).items():
        ds = [d * p ** j for d in ds for j in range(e + 1)]
    return tuple(sorted(ds))


def omega(n):
    return sum(factors(n).values())


def exp_D(h):
    f = [Q(0)] * len(h)
    f[1] = Q(1)
    for n in range(2, len(h)):
        f[n] = sum((omega(d) * h[d] * f[n // d] for d in divisors(n) if d > 1), Q(0)) / omega(n)
    return f


def log_D(f):
    h = [Q(0)] * len(f)
    for n in range(2, len(f)):
        h[n] = f[n] - sum((omega(d) * h[d] * f[n // d] for d in divisors(n) if 1 < d < n), Q(0)) / omega(n)
    return h


def D(a, b):
    return [Q(0)] + [sum((a[d] * b[n // d] for d in divisors(n)), Q(0)) for n in range(1, len(a))]


@lru_cache(maxsize=None)
def complete_fibres(n, r):
    possible_differences = [1]
    for p, e in factors(n).items():
        possible_differences = [d * p ** j for d in possible_differences for j in range(e // r + 1)]
    pairs = []
    for d in possible_differences:
        m = n // d ** r
        T = d * d + 4 * m
        root = isqrt(T)
        if root * root == T and (root - d) % 2 == 0:
            a = (root - d) // 2
            b = a + d
            if a >= 2 and a * b * d ** r == n:
                pairs.append((a, b))
    return tuple(sorted(pairs))


def K(a, b, r):
    out = [Q(0)] * len(a)
    for n in range(2, len(a)):
        out[n] = sum((a[x] * b[y] + a[y] * b[x] for x, y in complete_fibres(n, r)), Q(0))
    return out


def generic(source):
    for row in source['generic_operator_laws']['records']:
        h, k = (list(map(Q, row[key])) for key in ('input_h', 'input_k'))
        r, f, g = row['r'], exp_D(h), exp_D(k)
        kh = K(h, h, r)
        result = exp_D([a + b for a, b in zip(h, kh)])
        assert result == list(map(Q, row['output_f']))
        result_log, recovered = log_D(result), [Q(0)] * len(h)
        for n in range(2, len(h)):
            recovered[n] = result_log[n] - sum((2 * recovered[a] * recovered[b] for a, b in complete_fibres(n, r)), Q(0))
        assert recovered == h and log_D(f) == h
        pin = exp_D([a / 2 + b / 4 for a, b in zip(h, kh)])
        pout = exp_D([a / 2 + b / 2 for a, b in zip(h, kh)])
        assert D(pout, pout) == result and pin != pout
        hk = [a + b for a, b in zip(h, k)]
        assert exp_D([a + b for a, b in zip(hk, K(hk, hk, r))]) != D(result, exp_D([a + b for a, b in zip(k, K(k, k, r))]))
        assert all(result[n] == f[n] for n in range(1, len(f), 2))
        assert all(row['checks'].values())
    return True


def zeta(source):
    count, collisions = 0, []
    for profile in source['zeta_profiles']:
        r = profile['r']
        for n, v in enumerate(profile['coefficients']):
            if n < 2:
                continue
            pp = [(a, b) for a, b in complete_fibres(n, r) if len(factors(a)) == len(factors(b)) == 1]
            expected = sum((Q(2, next(iter(factors(a).values())) * next(iter(factors(b).values()))) for a, b in pp), Q(0))
            assert expected == Q(v)
            count += 1
            if len(pp) > 1:
                collisions.append({'r': r, 'index': n, 'prime_power_fibre': [list(pair) for pair in pp]})
        assert profile['coefficient_six'] == '2'
    assert complete_fibres(30, 1) == ((2, 5), (3, 5), (5, 6))
    assert [(a, b) for a, b in complete_fibres(30, 1) if len(factors(a)) == len(factors(b)) == 1] == [(2, 5), (3, 5)]
    return {'encoded_indices_checked': count, 'collision_records': collisions, 'all_passed': True}


def inverse_mass(source):
    for profile in source['inverse_tree_profiles']:
        r, rows = profile['r'], profile['records']
        terms = [{int(n): Q(v) for n, v in row['coefficients'].items()} for row in rows]
        for j in range(1, len(rows)):
            out, overlap = {}, Q(0)
            for left in range(j):
                right = j - left - 1
                for a, v in terms[left].items():
                    for b, w in terms[right].items():
                        if a == b:
                            overlap += abs(v * w)
                        else:
                            n = a * b * max(a - b, b - a) ** r
                            out[n] = out.get(n, Q(0)) - v * w
            out = {n: v for n, v in out.items() if v}
            assert out == terms[j]
            masses = [sum((abs(v) for v in t.values()), Q(0)) for t in terms]
            assert masses[j] == sum((masses[left] * masses[j - left - 1] for left in range(j)), Q(0)) - overlap
            assert overlap == Q(rows[j]['ordered_equal_index_overlap_mass'])
    small = source['inverse_tree_profiles'][0]['records']
    assert [Q(row['absolute_mass']) for row in small] == [2, 2, 8, 32, 160, 800]
    collided = source['inverse_tree_profiles'][3]['records']
    assert Q(collided[3]['absolute_mass']) == 232
    assert source['inverse_mass_grammar']['all_two_seed_survivors_rejected_on_collision_seeds']
    return True


def correlation(source):
    data = source['known_additive_correlation_calibration']
    a, b = ({int(n): Q(v) for n, v in data[key].items()} for key in ('a', 'b'))
    for row in data['records']:
        d = row['gap']
        expected = sum((a.get(n, Q(0)) * b.get(n + d, Q(0)) + b.get(n, Q(0)) * a.get(n + d, Q(0)) for n in range(1, 6)), Q(0))
        assert expected == Q(row['ordered_correlation'])
    h = [Q(0)] * 7
    h[2], h[3] = Q(1), Q(-1)
    assert K(h, h, 3)[6] == -2 == Q(source['positive_semidefinite_kernel_rejected']['negative_coefficient_six'])
    return True


def density(probe):
    largest = max(row['X'] for row in probe['finite_prime_density_certificates']) * 2
    sieve = [True] * (largest + 1)
    sieve[0] = sieve[1] = False
    for p in range(2, isqrt(largest) + 1):
        if sieve[p]:
            for n in range(p * p, largest + 1, p):
                sieve[n] = False
    primes = [n for n in range(2, largest + 1) if sieve[n]]
    for row in probe['finite_prime_density_certificates']:
        X = row['X']
        ps = [p for p in primes if X <= p <= 2 * X]
        assert len(ps) == row['prime_count']
        for D, J, pairs, L in [(row['D'], row['interval_count'], row['within_interval_unordered_prime_pairs'], row['Cauchy_pair_lower'])] + [(v['D'], v['interval_count'], v['within_interval_unordered_prime_pairs'], v['Cauchy_pair_lower']) for v in row['layer_records']]:
            counts = [0] * J
            for p in ps:
                counts[(p - X) // D] += 1
            actual = sum(v * (v - 1) // 2 for v in counts)
            assert J == ceil((X + 1) / D) and actual == pairs
            assert Q(L) == (Q(len(ps) ** 2, J) - len(ps)) / 2 and actual >= Q(L)
        lower = sum((Q(v['within_interval_unordered_prime_pairs'], 2 * X * v['D']) for v in row['layer_records']), Q(0))
        assert lower == Q(row['r_two_balanced_energy_lower'])
    flint.ctx.prec = 256
    pp = [(n, next(iter(factors(n).values()))) for n in range(2, 257) if len(factors(n)) == 1]
    gamma = sum((flint.arb(2) / (e * f) / flint.arb(a * b * (b - a) ** 3).sqrt()
                 for j, (a, e) in enumerate(pp) for b, f in pp[j + 1:]), flint.arb(0))
    fft = next(row['finite_prefix_energy'] for row in probe['endpoint_energy_profiles'] if row['r'] == 3 and row['sigma'] == 0.5 and row['input_cutoff'] == 256)
    assert abs(gamma - flint.arb(fft)).abs_upper() < flint.arb('1e-11')
    return {'all_passed': True, 'independent_native_finite_energy_ball': gamma.str(20),
            'finite_density_certificates_checked': len(probe['finite_prime_density_certificates']),
            'infinite_convergence_inferred_from_FFT': False}


def main():
    start = time.monotonic()
    source = json.loads((BASE / 'gap-results/gap_search.json').read_text())
    probe = json.loads((BASE / 'gap-results/gap_endpoint_probe.json').read_text())
    assert source['all_passed'] and probe['all_passed']
    z, d = zeta(source), density(probe)
    checks = {'unrelated_generic_inputs_Omega_recursion_root_and_inverse': generic(source),
              'five_complete_difference_discriminant_zeta_prefixes': z['all_passed'],
              'inverse_overlap_mass_and_failed_binary_tree_extrapolation': inverse_mass(source),
              'known_bilinear_additive_correlation_calibration': correlation(source),
              'independent_finite_prime_density_counts_and_Arb_FFT_calibration': d['all_passed'],
              'global_injectivity_and_unproved_new_RH_estimate_rejected': not source['new_RH_estimate_proved'] and source['gap_one_collision_control']['global_prime_power_injectivity_rejected']}
    out = {'checks': checks, 'zeta_audit': z, 'finite_density_audit': d,
           'production_imports': False, 'shared_trusted_kernel': 'FLINT exact factorization/primality and Arb; independent discriminants, Omega recurrences and integer sieve',
           'all_passed': all(checks.values()), 'seconds': time.monotonic() - start}
    (BASE / 'gap-results/gap_verification.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Independent gap exact audit:', sum(checks.values()), '/', len(checks), 'indices', z['encoded_indices_checked'], 'seconds', out['seconds'], flush=True)
    assert out['all_passed']


if __name__ == '__main__':
    main()

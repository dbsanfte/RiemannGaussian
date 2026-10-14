#!/usr/bin/env python3
"""Exploratory gap energies and exact finite prime-density lower certificates."""

from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import math
import time

import numpy as np

BASE = Path(__file__).resolve().parent


def prime_data(cutoff):
    mask = np.ones(cutoff + 1, dtype=bool)
    mask[:2] = False
    for p in range(2, math.isqrt(cutoff) + 1):
        if mask[p]:
            mask[p * p::p] = False
    primes = np.flatnonzero(mask)
    g = np.zeros(cutoff + 1)
    for p in map(int, primes):
        n, e = p, 1
        while n <= cutoff:
            g[n] = 1 / e
            n *= p
            e += 1
    return primes, g


def correlation(weights):
    length = 1 << (2 * len(weights) - 1).bit_length()
    F = np.fft.rfft(weights, length)
    return np.fft.irfft(F * F.conjugate(), length)[:len(weights)]


def energy(weights, r, sigma):
    c = correlation(weights)
    d = np.arange(1, len(c), dtype=float)
    return float(2 * np.dot(c[1:], d ** (-r * sigma)))


def density_certificate(primes, X):
    ps = primes[(primes >= X) & (primes <= 2 * X)]
    m = len(ps)
    D = max(1, math.ceil(8 * X / m))
    J = math.ceil((X + 1) / D)
    counts = np.bincount((ps - X) // D, minlength=J)
    pairs = sum(int(v) * (int(v) - 1) // 2 for v in counts)
    lower = (Q(m * m, J) - m) / 2
    layers, layer_lower = [], Q(0)
    d = 1
    while d < math.ceil(4 * X / m):
        d *= 2
    while 2 * d <= X:
        j = math.ceil((X + 1) / d)
        cs = np.bincount((ps - X) // d, minlength=j)
        a = sum(int(v) * (int(v) - 1) // 2 for v in cs)
        L = (Q(m * m, j) - m) / 2
        layer_lower += Q(a, 2 * X * d)
        layers.append({'D': d, 'interval_count': j, 'within_interval_unordered_prime_pairs': a,
                       'Cauchy_pair_lower': str(L)})
        d *= 2
    return {'X': X, 'prime_count': m, 'D': D, 'interval_count': J,
            'within_interval_unordered_prime_pairs': pairs, 'Cauchy_pair_lower': str(lower),
            'layer_records': layers, 'r_two_balanced_energy_lower': str(layer_lower),
            'finite_count_inequality_passed': Q(pairs) >= lower and all(Q(row['within_interval_unordered_prime_pairs']) >= Q(row['Cauchy_pair_lower']) for row in layers)}


def scaling_grammar():
    targets = []
    for r in (1, 2, 3, 4, 5, 7):
        x = 11
        balanced = x * (2 * x) * x ** r
        doubled = (2 * x) * (4 * x) * (2 * x) ** r
        adjacent = [n * (n + 1) * 1 ** r for n in (11, 12, 13, 14)]
        second = [adjacent[j + 2] - 2 * adjacent[j + 1] + adjacent[j] for j in (0, 1)]
        assert doubled == balanced * 2 ** (r + 2) and second == [2, 2]
        targets.append({'r': r, 'balanced_degree': r + 2, 'near_pair_degree': 2,
                        'scaling_prediction': str(max(Q(2, r + 2), Q(1, 2))), 'training': r <= 3})
    records = []
    constants = sorted(set(Q(a, b) for a in range(1, 5) for b in range(1, 5)))
    for numerator, offset, constant in product(range(1, 5), range(0, 5), constants):
        def predicts(r):
            return max(Q(numerator, r + offset), constant)
        fitted = all(predicts(row['r']) == Q(row['scaling_prediction']) for row in targets if row['training'])
        held = fitted and all(predicts(row['r']) == Q(row['scaling_prediction']) for row in targets if not row['training'])
        records.append({'numerator': numerator, 'r_offset': offset, 'near_pair_threshold': str(constant),
                        'training_passed': fitted, 'held_out_passed': held})
    return {'models_scored': len(records), 'targets': targets,
            'target_origin': 'Exact index scaling; dimensions two and one from bulk and finite prime-density averaging. Universal convergence is a separate proof.',
            'survivors': [row for row in records if row['held_out_passed']]}


def main():
    start = time.monotonic()
    largest = 2 ** 19
    primes, g = prime_data(largest)
    rows, density = [], []
    for k in range(8, 20):
        N, X = 2 ** k, 2 ** (k - 1)
        n = np.arange(1, N + 1, dtype=float)
        for sigma in (0.5, 2 / 3, 0.4):
            w = np.zeros(N + 1)
            w[1:] = g[1:N + 1] * n ** (-sigma)
            c, cb = correlation(w), correlation(w[X:])
            ds, db = np.arange(1, len(c), dtype=float), np.arange(1, len(cb), dtype=float)
            rr = (2, 3, 4, 5) if sigma == 0.5 else ((1,) if sigma > 0.5 else (3,))
            for r in rr:
                prefix = float(2 * np.dot(c[1:], ds ** (-r * sigma)))
                block = float(2 * np.dot(cb[1:], db ** (-r * sigma)))
                rows.append({'r': r, 'sigma': sigma, 'input_cutoff': N, 'balanced_block_start': X,
                             'finite_prefix_energy': prefix, 'finite_balanced_block_energy': block,
                             'block_times_log_X': block * math.log(X),
                             'block_times_log_X_squared': block * math.log(X) ** 2})
        density.append(density_certificate(primes, X))
        print('Gap endpoint exploration', N, 'r2/r3:', [(row['r'], row['finite_prefix_energy']) for row in rows if row['input_cutoff'] == N and row['sigma'] == 0.5 and row['r'] in (2, 3)], flush=True)
    # The double-precision energy is exploratory; this check detects indexing
    # mistakes against a direct finite sum and does not certify infinite sums.
    _, small = prime_data(128)
    w = np.zeros(129)
    w[1:] = small[1:] / np.sqrt(np.arange(1, 129, dtype=float))
    direct = sum(2 * w[a] * w[b] / (b - a) ** 1.5 for a in range(2, 129) for b in range(a + 1, 129))
    fft_ok = bool(abs(energy(w, 3, 0.5) - direct) < 1e-12)
    grammar = scaling_grammar()
    out = {'scaling_threshold_grammar': grammar, 'endpoint_energy_profiles': rows,
           'finite_prime_density_certificates': density, 'small_direct_FFT_calibration_passed': fft_ok,
           'numerical_energy_is_double_precision_exploration_only': True,
           'empirical_log_decay_is_not_a_proved_prime_pair_asymptotic': True,
           'all_passed': fft_ok and len(grammar['survivors']) == 1 and all(row['finite_count_inequality_passed'] for row in density),
           'seconds': time.monotonic() - start}
    dest = BASE / 'gap-results'
    dest.mkdir(exist_ok=True)
    (dest / 'gap_endpoint_probe.json').write_text(json.dumps(out, indent=2) + '\n')
    print('Gap threshold grammar:', grammar['survivors'], 'seconds', out['seconds'], flush=True)
    assert out['all_passed']


if __name__ == '__main__':
    main()

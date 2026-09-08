#!/usr/bin/env python3
"""Audit further prime removal without losing the unit/source term.

Floating-point exploration only; no zero bound is inferred. The complete
integer decomposition is checked before applying complex powers. At the
cutoff 2*u the rough model includes primes, prime powers, semiprimes, and
three-prime products. All have their literal rough-number coefficients.
Every physical endpoint and every Gram cross term is retained.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy

from probe_eta_coprime_products import (
    arithmetic_arrays, check_close, high_product_coefficients, positive_integer,
    window_prefix,
)


def pair(z):
    return [float(z.real), float(z.imag)]


def scale_arrays(u):
    maximum = 2 * u ** 4
    mu, least, _ = arithmetic_arrays(maximum)
    b = high_product_coefficients(mu, u ** 3, maximum)
    omega = np.zeros(maximum + 1, dtype=np.int8)
    primes = list(sympy.primerange(2, maximum + 1))
    for p in primes:
        power = p
        while power <= maximum:
            omega[power::power] += 1
            power *= p
    return mu, least, b, omega, primes


def coefficient_split(u, threshold, arrays):
    maximum, cutoff = 2 * u ** 4, u ** 3
    mu, least, b, omega, primes = arrays
    outside = np.zeros(maximum + 1, dtype=bool)
    for p in primes:
        if p > threshold:
            outside[p::p] = True
    n = np.arange(maximum + 1)
    rough = (n > 1) & (n % 2 == 1) & (least > threshold)
    if np.any(omega[rough] > 3):
        raise ArithmeticError('More than three rough prime factors, counted with multiplicity')
    model_parts = []
    for k in [1, 2, 3]:
        selected = np.flatnonzero(rough & (omega == k))
        coefficients = np.zeros(maximum + 1, dtype=np.int64)
        coefficients[selected] = -1
        coefficients[2 * selected[selected <= maximum // 2]] += 2
        model_parts.append(coefficients)
    model = sum(model_parts)
    low = np.zeros(maximum + 1, dtype=np.int64)
    for d in np.flatnonzero(outside[:cutoff + 1] & (mu[:cutoff + 1] != 0)):
        q = np.arange(1, maximum // d + 1)
        low[d::d] += np.where(q % 2, 1, -1) * int(mu[d])
    large = np.where(outside, b, 0)
    if not np.array_equal(large - model, -low):
        raise ArithmeticError('Whole growing-cutoff rough-model coefficient identity failed')
    complementary = b - large
    coprime_eta = np.where((n > 0) & ((least == 0) | (least > threshold)),
                           np.where(n % 2, 1, -1), 0)
    core = coprime_eta.copy()
    core[2::2] -= coprime_eta[1:maximum // 2 + 1]
    source = np.zeros(maximum + 1, dtype=np.int64)
    source[1], source[2] = 1, -2
    if not np.array_equal(model + core, source):
        raise ArithmeticError('Unit/source term was lost in the rough model')
    return b, large, model, low, complementary, core, coprime_eta, model_parts


def probe(u, zero_indices, real_parts):
    start, maximum = u ** 4, 2 * u ** 4
    arrays = scale_arrays(u)
    n = np.arange(1, maximum + 1)
    endpoints = np.arange(start, 2 * start)
    for threshold in sorted({2 * u, 2 * u ** 2}):
        b, large, model, low, complementary, core, coprime_eta, parts = coefficient_split(u, threshold, arrays)
        for zero_index in zero_indices:
            zero = mp.zetazero(zero_index)
            for sigma in real_parts:
                s_mp = mp.mpc(sigma, zero.imag)
                s = complex(s_mp)
                alpha = 1 - 2 * 2 ** (-s)
                powers = np.exp(-s * np.log(n))
                full_values = window_prefix(b[1:] * powers, start)
                large_values = window_prefix(large[1:] * powers, start)
                low_values = window_prefix(low[1:] * powers, start)
                core_values = window_prefix(core[1:] * powers, start)
                channels = np.array([window_prefix(part[1:] * powers, start) for part in parts] +
                                    [window_prefix(complementary[1:] * powers, start)])
                model_values = channels[:3].sum(axis=0)
                paired_values = channels.sum(axis=0)
                source_remainder = channels[3] - core_values
                check_close(large_values - model_values, -low_values, 'every rough-model physical error')
                check_close(paired_values - full_values, low_values, 'every paired physical prefix')
                check_close(model_values + core_values, alpha, 'every physical unit/source identity')
                check_close(paired_values - alpha, source_remainder, 'every source-sensitive signed remainder')
                eta_prefix = np.r_[0j, np.cumsum(coprime_eta[1:] * powers)]
                check_close(core_values, eta_prefix[endpoints] - 2 ** (-s) * eta_prefix[endpoints // 2],
                            'complete coprime eta representation of the rough core')
                gram = channels @ channels.conj().T / start / abs(alpha) ** 2
                energy = float(np.mean(abs(paired_values / alpha) ** 2))
                check_close(gram.sum(), energy, 'all rough-factor and complementary Gram entries')
                yield dict(
                    status='floating-point exploration, not a Lean theorem or zero bound',
                    u=u, threshold=threshold, physical_start=start, physical_length=start,
                    divisor_cutoff=u ** 3, zero_index=zero_index, sampled_s=pair(s),
                    sample_is_on_critical_line=(sigma == 0.5),
                    numerical_zeta_absolute=float(abs(mp.zeta(s_mp))),
                    integer_coefficient_reconstruction_passed=True,
                    integer_unit_source_identity_passed=True,
                    rough_prime_factor_counts_include_multiplicity=True,
                    full_first_mean_over_source=pair(np.mean(full_values) / alpha),
                    model_first_mean_over_source=pair(np.mean(model_values) / alpha),
                    complete_rough_core_mean_over_source=pair(np.mean(core_values) / alpha),
                    low_large_prime_mean_over_source=pair(np.mean(low_values) / alpha),
                    complementary_mean_over_source=pair(np.mean(channels[3]) / alpha),
                    paired_first_mean_over_source=pair(np.mean(paired_values) / alpha),
                    source_remainder_first_mean_over_source=pair(np.mean(source_remainder) / alpha),
                    source_projection_gap=1 - float((np.mean(paired_values) / alpha).real),
                    channel_labels=['one_rough_prime_factor', 'two_rough_prime_factors',
                                    'three_rough_prime_factors', 'complementary_original_products'],
                    channel_first_means_over_source=[pair(z) for z in channels.mean(axis=1) / alpha],
                    complete_gram_real=gram.real.tolist(), complete_gram_imag=gram.imag.tolist(),
                    paired_energy_over_source_square=energy,
                    diagonal_energy=float(np.trace(gram).real),
                    all_cross_terms=energy - float(np.trace(gram).real),
                )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scales', nargs='+', type=positive_integer, default=[4, 8, 16, 32])
    parser.add_argument('--zeros', nargs='+', type=positive_integer, default=[1, 2])
    parser.add_argument('--real-parts', nargs='+', type=float, default=[0.5, 0.75])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if min(args.scales) < 2 or any(not 0 < s < 1 for s in args.real_parts):
        parser.error('Scales must be >=2 and real parts strictly between zero and one')
    mp.mp.dps = 40
    records = []
    for u in sorted(set(args.scales)):
        for record in probe(u, args.zeros, args.real_parts):
            records.append(record)
            print(json.dumps({k: record[k] for k in (
                'u', 'threshold', 'sampled_s', 'model_first_mean_over_source',
                'complete_rough_core_mean_over_source', 'complementary_mean_over_source',
                'paired_first_mean_over_source', 'paired_energy_over_source_square',
            )}, allow_nan=False), flush=True)
    if args.output:
        args.output.write_text(json.dumps(dict(
            status='floating-point exploration, not a Lean theorem or zero bound',
            off_critical_samples_are_not_zeros=True, records=records,
        ), indent=2, allow_nan=False) + '\n')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Check the actual large-prime/composite split on full quartic windows.

Floating-point diagnostics are not a theorem or a zero bound. Integer
coefficient reconstruction is checked before computing any complex powers.
The selected primes exceed 2*u^2. Their entire product group differs from
the explicit prime/twice-prime model by the negative low-divisor selection.
The model remains coupled to all complementary products in the full Gram.
Real parts other than 1/2 are NOT zeros; their zeta values are recorded.
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


def coefficient_split(u):
    start, cutoff, maximum = u ** 4, u ** 3, 2 * u ** 4
    threshold = 2 * u ** 2
    mu, _, _ = arithmetic_arrays(maximum)
    b = high_product_coefficients(mu, cutoff, maximum)
    selected = list(sympy.primerange(threshold + 1, maximum + 1))
    multiplicity = np.zeros(maximum + 1, dtype=np.int8)
    model = np.zeros(maximum + 1, dtype=np.int64)
    for p in selected:
        multiplicity[p::p] += 1
        model[p] -= 1
        if 2 * p <= maximum:
            model[2 * p] += 2
    if np.any(multiplicity > 1):
        raise ArithmeticError('Selected large-prime product classes overlap')
    has_large_prime = multiplicity == 1
    low = np.zeros(maximum + 1, dtype=np.int64)
    for d in np.flatnonzero(has_large_prime[:cutoff + 1] & (mu[:cutoff + 1] != 0)):
        q = np.arange(1, maximum // d + 1)
        low[d::d] += np.where(q % 2, 1, -1) * int(mu[d])
    large = np.where(has_large_prime, b, 0)
    if not np.array_equal(large - model, -low):
        raise ArithmeticError('Exact whole large-prime coefficient identity failed')
    complementary = b - large
    return b, large, model, low, complementary, has_large_prime


def probe(u, zero_indices, real_parts):
    start, cutoff, maximum = u ** 4, u ** 3, 2 * u ** 4
    b, large, model, low, complementary, mask = coefficient_split(u)
    n = np.arange(1, maximum + 1)
    ramp = np.maximum(0, start - np.maximum(0, n - start)) / start
    for zero_index in zero_indices:
        zero = mp.zetazero(zero_index)
        for sigma in real_parts:
            s_mp = mp.mpc(sigma, zero.imag)
            s = complex(s_mp)
            alpha = 1 - 2 * 2 ** (-s)
            powers = np.exp(-s * np.log(n))
            full_values = window_prefix(b[1:] * powers, start)
            large_values = window_prefix(large[1:] * powers, start)
            model_values = window_prefix(model[1:] * powers, start)
            low_values = window_prefix(low[1:] * powers, start)
            complementary_values = window_prefix(complementary[1:] * powers, start)
            check_close(large_values - model_values, -low_values, 'all physical large-prime errors')
            check_close(large_values + complementary_values, full_values, 'all original products')
            paired_values = model_values + complementary_values
            check_close(paired_values - full_values, low_values, 'complete paired candidate')
            check_close(np.mean(paired_values), np.sum(ramp * (model[1:] + complementary[1:]) * powers),
                        'paired first mean literal ramp')
            channels = np.array([model_values, complementary_values])
            gram = channels @ channels.conj().T / start / abs(alpha) ** 2
            paired_energy = float(np.mean(abs(paired_values / alpha) ** 2))
            check_close(gram.sum(), paired_energy, 'complete model/complementary Gram')
            yield dict(
                status='floating-point exploration, not a Lean theorem or zero bound',
                u=u, physical_start=start, physical_length=start, divisor_cutoff=cutoff,
                large_prime_threshold=2 * u ** 2, zero_index=zero_index, sampled_s=pair(s),
                sample_is_on_critical_line=(sigma == 0.5),
                numerical_zeta_absolute=float(abs(mp.zeta(s_mp))),
                integer_coefficient_identity_passed=True,
                selected_prime_classes_are_disjoint=True,
                full_first_mean_over_source=pair(np.mean(full_values) / alpha),
                large_prime_group_mean_over_source=pair(np.mean(large_values) / alpha),
                prime_model_mean_over_source=pair(np.mean(model_values) / alpha),
                joint_large_prime_error_over_source=pair(np.mean(large_values - model_values) / alpha),
                low_large_prime_mean_over_source=pair(np.mean(low_values) / alpha),
                complementary_group_mean_over_source=pair(np.mean(complementary_values) / alpha),
                paired_first_mean_over_source=pair(np.mean(paired_values) / alpha),
                full_energy_over_source_square=float(np.mean(abs(full_values / alpha) ** 2)),
                paired_energy_over_source_square=paired_energy,
                model_energy=float(gram[0, 0].real), complementary_energy=float(gram[1, 1].real),
                model_complementary_cross=2 * float(gram[0, 1].real),
                complete_gram_real=gram.real.tolist(), complete_gram_imag=gram.imag.tolist(),
                large_prime_product_count=int(np.count_nonzero(mask[1:])),
            )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scales', nargs='+', type=positive_integer, default=[4, 8, 16, 32])
    parser.add_argument('--zeros', nargs='+', type=positive_integer, default=[1, 2])
    parser.add_argument('--real-parts', nargs='+', type=float, default=[0.5, 0.75])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if min(args.scales) < 2 or any(not 0 < sigma < 1 for sigma in args.real_parts):
        parser.error('Scales must be >=2 and real parts strictly between zero and one')
    mp.mp.dps = 40
    records = []
    for u in sorted(set(args.scales)):
        for record in probe(u, args.zeros, args.real_parts):
            records.append(record)
            print(json.dumps({k: record[k] for k in (
                'u', 'sampled_s', 'joint_large_prime_error_over_source',
                'prime_model_mean_over_source', 'complementary_group_mean_over_source',
                'paired_first_mean_over_source', 'paired_energy_over_source_square',
            )}, allow_nan=False), flush=True)
    if args.output:
        args.output.write_text(json.dumps(dict(
            status='floating-point exploration, not a Lean theorem or zero bound',
            off_critical_samples_are_not_zeros=True, records=records,
        ), indent=2, allow_nan=False) + '\n')


if __name__ == '__main__':
    main()

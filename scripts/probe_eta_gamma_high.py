#!/usr/bin/env python3
"""Inspect the actual signed Mobius terms inside a gamma-smoothed divisor band.

Floating-point exploration only. The omitted divisor tail has a separate
Lean bound; these numerical values and truncation comparisons are not
certificates. Off-critical samples at known zero ordinates are not zeros.
The reported norms are norms of complex first means, not mean squares of
the original physical carrier. All divisor and prime-factor channels are
added with their original signs and phases.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp
import numpy as np

from probe_eta_coprime_products import (
    arithmetic_arrays, check_close, high_product_coefficients, positive_integer,
)


def pair(z):
    return [float(z.real), float(z.imag)]


def survival(x):
    return np.exp(-x) * (1 + x + x * x / 2)


def eta(s):
    return (1 - mp.power(2, 1 - s)) * mp.zeta(s)


def low_eta_coefficients(s, terms):
    coefficients = [complex(eta(s)), 0j, 0j]
    coefficients.extend(complex((-1) ** n * (n - 1) * (n - 2) * eta(s - n) /
                                (2 * mp.factorial(n))) for n in range(3, terms + 1))
    return coefficients


def probe(u, zero_indices, real_parts, product_scale):
    scale, lower = u ** 6, u ** 5
    upper = int(np.ceil(2 * scale * (1 + 2 * np.log(scale))))
    maximum = max(product_scale * scale, upper + 20 * scale)
    mu, _, odd_count = arithmetic_arrays(maximum)
    n = np.arange(1, maximum + 1)
    d = n[lower:]
    x = d / scale
    factor_count = odd_count[lower + 1:] + (d % 2 == 0)
    product_coefficients = high_product_coefficients(mu, lower, maximum)
    log_n = np.log(n)
    product_survival = survival(n / scale)
    edges = sorted({lower, upper, maximum} |
                   {int(scale * y) for y in [0.5, 1, 2, 4, 8, 16, 32]
                    if lower < int(scale * y) < upper})

    for zero_index in zero_indices:
        ordinate = mp.zetazero(zero_index).imag
        for sigma in real_parts:
            s_mp = mp.mpc(sigma, ordinate)
            s = complex(s_mp)
            alpha = 1 - 2 * 2 ** (-s)
            source = survival(1 / scale) - 2 * 2 ** (-s) * survival(2 / scale)
            powers = np.exp(-s * log_n)
            kernel = np.zeros(len(d), dtype=np.complex128)
            for q in range(1, maximum // (lower + 1) + 1):
                length = maximum // q - lower
                kernel[:length] += ((1 if q % 2 else -1) * q ** (-s) *
                                    survival(q * x[:length]))
            values = mu[lower + 1:] * powers[lower:] * kernel
            full_high = np.sum(values)
            by_products = np.sum(product_coefficients[1:] * powers * product_survival)
            check_close(full_high, by_products, 'independent integer product reconstruction')

            coefficients = low_eta_coefficients(s_mp, 60)
            low_x = n[:lower] / scale
            low_kernel = np.polynomial.polynomial.polyval(low_x, coefficients)
            short_kernel = np.polynomial.polynomial.polyval(low_x, coefficients[:46])
            low = np.sum(mu[1:lower + 1] * powers[:lower] * low_kernel)
            short_low = np.sum(mu[1:lower + 1] * powers[:lower] * short_kernel)
            check_close(low, short_low, 'low Taylor truncation comparison')
            check_close(full_high, source - low, 'complete physical source and divisor split')

            band_values = values[:upper - lower]
            band = np.sum(band_values)
            tail = np.sum(values[upper - lower:])
            check_close(full_high, band + tail, 'upper divisor tail retained')
            factor_channels = [np.sum(band_values[factor_count[:upper - lower] == k])
                               for k in [1, 2, 3]]
            factor_channels.append(np.sum(band_values[factor_count[:upper - lower] >= 4]))
            check_close(band, sum(factor_channels), 'all signed prime-factor channels retained')

            # Completion chi cancels when dividing by the original source chi*alpha.
            tail_allowance = (16 * scale * upper ** (-sigma) *
                              np.exp(-upper / (2 * scale)) / abs(alpha))
            if abs(tail / alpha) > tail_allowance + 2e-8:
                raise ArithmeticError('The measured divisor tail exceeds its analytic envelope')
            channel_mass = sum(abs(z / alpha) for z in factor_channels)
            bands = [dict(lower=a, upper=b, x_interval=[a / scale, b / scale],
                          mean_over_source=pair(np.sum(values[a - lower:b - lower]) / alpha))
                     for a, b in zip(edges, edges[1:])]
            yield dict(
                status='floating-point exploration; no new zero bound',
                u=u, scale=scale, lower_divisor=lower, upper_divisor=upper,
                product_cutoff=maximum, zero_index=zero_index, sampled_s=pair(s),
                sample_is_numerical_zero=(sigma == 0.5),
                numerical_zeta_absolute=float(abs(mp.zeta(s_mp))),
                original_source_over_source=pair(source / alpha),
                low_mean_over_source=pair(low / alpha),
                full_high_mean_over_source=pair(full_high / alpha),
                finite_band_mean_over_source=pair(band / alpha),
                omitted_divisor_tail_over_source=pair(tail / alpha),
                analytic_divisor_tail_allowance_over_source=float(tail_allowance),
                source_split_discrepancy=float(abs(full_high + low - source)),
                product_reconstruction_discrepancy=float(abs(full_high - by_products)),
                low_taylor_truncation_comparison=float(abs(low - short_low)),
                factor_channel_labels=['one_prime', 'two_distinct_primes',
                                       'three_distinct_primes', 'at_least_four_distinct_primes'],
                factor_channel_means_over_source=[pair(z / alpha) for z in factor_channels],
                sum_factor_channel_norms_over_source=float(channel_mass),
                whole_mean_norm_over_source=float(abs(band / alpha)),
                signed_cancellation_ratio=float(abs(band / alpha) / channel_mass),
                divisor_bands=bands,
            )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scales', nargs='+', type=positive_integer, default=[2, 3, 4, 6])
    parser.add_argument('--zeros', nargs='+', type=positive_integer, default=[1, 2])
    parser.add_argument('--real-parts', nargs='+', type=float, default=[0.5, 0.75])
    parser.add_argument('--product-scale', type=positive_integer, default=80)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if min(args.scales) < 2 or args.product_scale < 40 or any(not 0 < s < 1 for s in args.real_parts):
        parser.error('Scales must be >=2, product scale >=40, and real parts in (0,1)')
    mp.mp.dps = 50
    records = []
    for u in sorted(set(args.scales)):
        for record in probe(u, args.zeros, args.real_parts, args.product_scale):
            records.append(record)
            print(json.dumps({k: record[k] for k in [
                'u', 'sampled_s', 'finite_band_mean_over_source',
                'factor_channel_means_over_source', 'sum_factor_channel_norms_over_source',
                'signed_cancellation_ratio', 'analytic_divisor_tail_allowance_over_source',
            ]}, allow_nan=False), flush=True)
    if args.output:
        args.output.write_text(json.dumps(dict(
            status='Numerical exploration; the finite central arithmetic bound remains open.',
            off_critical_samples_are_not_zeros=True, records=records,
        ), indent=2, allow_nan=False) + '\n')


if __name__ == '__main__':
    main()

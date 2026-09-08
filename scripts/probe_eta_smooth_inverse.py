#!/usr/bin/env python3
"""Audit the smooth-divisor candidate against its actual inverse-zeta defect.

Floating-point exploration only, with no zero bound inferred. The signed
eta error retains every original physical endpoint. The optional input
from probe_eta_rough_model.py checks it against the full product carrier.
The Buchstab expression is a leading asymptotic model, not an error bound.
Off-critical samples at known zero ordinates are not zeros.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy

from probe_eta_coprime_products import arithmetic_arrays, check_close, positive_integer


def pair(z):
    return [float(z.real), float(z.imag)]


def smooth_arrays(u):
    maximum = 2 * u ** 3
    mu, _, _ = arithmetic_arrays(maximum)
    largest = np.zeros(maximum + 1, dtype=np.int64)
    for p in sympy.primerange(2, maximum + 1):
        largest[p::p] = p
    return mu, largest


def divided_prefix_means(start, cutoff, s):
    """Exact block counts for all floor(M/d), before complex evaluation."""
    q = np.arange(1, 2 * start)
    eta = np.where(q % 2, 1, -1) * np.exp(-s * np.log(q))
    prefix = np.r_[0j, np.cumsum(eta)]
    prefix_sum = np.cumsum(prefix)
    d = np.arange(1, cutoff + 1)
    first, last = start // d, (2 * start - 1) // d
    trim_left, trim_right = start - d * first, d * (last + 1) - 2 * start
    counts = d * (last - first + 1) - trim_left - trim_right
    if not np.all(counts == start):
        raise ArithmeticError('A physical endpoint was lost in a divided window')
    return (d * (prefix_sum[last] - prefix_sum[first - 1]) -
            trim_left * prefix[first] - trim_right * prefix[last]) / start


def buchstab_slope(v):
    if 1 < v < 2:
        return -1 / v ** 2
    if 2 <= v <= 3:
        return (v / (v - 1) - 1 - mp.log(v - 1)) / v ** 2
    raise ValueError('This diagnostic uses only the first two Buchstab intervals')


def buchstab_band_model(cutoff, threshold, s):
    """Abel transform of x*omega'(log(x)/log(y))/log(y)^2 on (D,2D]."""
    log_y = mp.log(threshold)
    v0, v1 = mp.log(cutoff) / log_y, mp.log(2 * cutoff) / log_y
    scaled = (mp.power(2, 1 - s) * buchstab_slope(v1) - buchstab_slope(v0) +
              s * mp.quad(lambda z: mp.power(z, -s) *
                          buchstab_slope(v0 + mp.log(z) / log_y), [1, 2]))
    return scaled, (v0, v1)


def key(record):
    return record['u'], record['threshold'], record['zero_index'], record['sampled_s'][0]


def probe(u, zero_indices, real_parts, reference=None):
    start, cutoff = u ** 4, u ** 3
    mu, largest = smooth_arrays(u)
    d = np.arange(1, cutoff + 1)
    band_n = np.arange(cutoff + 1, 2 * cutoff + 1)
    for zero_index in zero_indices:
        ordinate = mp.zetazero(zero_index).imag
        for sigma in real_parts:
            s_mp, s = mp.mpc(sigma, ordinate), complex(sigma, ordinate)
            alpha = 1 - 2 * 2 ** (-s)
            zeta = complex(mp.zeta(s_mp))
            eta_value = alpha * zeta
            means = divided_prefix_means(start, cutoff, s)
            powers = np.exp(-s * np.log(d))
            band_powers = np.exp(-s * np.log(band_n))
            for threshold in [2 * u, 2 * u ** 2]:
                selected = largest[1:cutoff + 1] <= threshold
                coefficients = mu[1:cutoff + 1] * selected
                inverse_prefix = np.sum(coefficients * powers)
                low = np.sum(coefficients * powers * means)
                centered = np.sum(coefficients * powers * (means - eta_value))
                defect = 1 - zeta * inverse_prefix
                joint = 1 - low / alpha
                check_close(joint, defect - centered / alpha, 'complete inverse-defect identity')
                band_mu = mu[cutoff + 1:] * (largest[cutoff + 1:] <= threshold)
                band = np.sum(band_mu * band_powers)
                band_scale = complex(mp.power(cutoff, 1 - s_mp) / mp.log(threshold) ** 2)
                scaled_model, ratios = buchstab_band_model(cutoff, threshold, s_mp)
                record = dict(
                    status='floating-point exploration, not a Lean theorem or zero bound',
                    u=u, threshold=threshold, zero_index=zero_index, sampled_s=pair(s),
                    physical_start=start, physical_length=start, divisor_cutoff=cutoff,
                    sample_is_on_critical_line=(sigma == 0.5), numerical_zeta_absolute=abs(zeta),
                    all_divided_window_integer_counts_passed=True,
                    inverse_prefix=pair(inverse_prefix), inverse_defect=pair(defect),
                    zeta_times_inverse_prefix=pair(zeta * inverse_prefix),
                    smooth_low_mean_over_source=pair(low / alpha),
                    centered_eta_error_mean_over_source=pair(centered / alpha),
                    reconstructed_joint_mean_over_source=pair(joint),
                    signed_smooth_moebius_band=int(np.sum(band_mu)),
                    complex_smooth_band=pair(band),
                    scaled_complex_smooth_band=pair(band / band_scale),
                    scaled_buchstab_abel_model=pair(scaled_model),
                    buchstab_model_is_not_an_error_bound=True,
                    smoothness_ratio_interval=[float(v) for v in ratios],
                )
                if reference is not None:
                    original = reference[key(record)]
                    check_close(joint, complex(*original['paired_first_mean_over_source']),
                                'full product mean from independently grouped divisors')
                    record['whole_product_carrier_comparison_passed'] = True
                yield record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scales', nargs='+', type=positive_integer, default=[4, 8, 16, 32])
    parser.add_argument('--zeros', nargs='+', type=positive_integer, default=[1, 2])
    parser.add_argument('--real-parts', nargs='+', type=float, default=[0.5, 0.75])
    parser.add_argument('--rough-records', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if min(args.scales) < 4 or any(not 0 < s < 1 for s in args.real_parts):
        parser.error('Scales must be >=4 and real parts strictly between zero and one')
    mp.mp.dps = 40
    reference = None
    if args.rough_records:
        reference = {key(r): r for r in json.loads(args.rough_records.read_text())['records']}
    records = []
    for u in sorted(set(args.scales)):
        for record in probe(u, args.zeros, args.real_parts, reference):
            records.append(record)
            print(json.dumps({k: record[k] for k in (
                'u', 'threshold', 'sampled_s', 'inverse_defect',
                'centered_eta_error_mean_over_source', 'reconstructed_joint_mean_over_source',
                'scaled_complex_smooth_band', 'scaled_buchstab_abel_model',
            )}, allow_nan=False), flush=True)
    if args.output:
        args.output.write_text(json.dumps(dict(
            status='floating-point exploration, not a Lean theorem or zero bound',
            off_critical_samples_are_not_zeros=True,
            external_buchstab_model_source='https://arxiv.org/abs/2207.04777',
            records=records,
        ), indent=2, allow_nan=False) + '\n')


if __name__ == '__main__':
    main()

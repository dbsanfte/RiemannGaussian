#!/usr/bin/env python3
"""Test full cutoff mixtures after removing the finite inverse-defect shift.

Floating-point diagnostic only. Centering subtracts the genuine eta value
from each finite eta prefix. It leaves every column unchanged at an actual
zero; at other points it is a different carrier, not a fabricated zero.
Both complete complex Gram matrices, their common covariance, and the
combined-divisor coefficient budget are retained. No zero bound is inferred.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp
import numpy as np

from probe_eta_coprime_products import arithmetic_arrays, check_close, positive_integer, window_prefix
from probe_eta_cutoff_mixture import coefficient_columns, mixture_record, pair


def fit_family(u, sigma, columns, original, divisor_indicator):
    start, cutoff = u ** 4, u ** 3
    gram = columns.conj().T @ columns / start
    means = columns.mean(axis=0)
    centered_columns = columns - means
    covariance = centered_columns.conj().T @ centered_columns / start
    check_close(gram, covariance + np.outer(means.conj(), means), 'full covariance/mean decomposition')
    differences = columns[:, 1:] - columns[:, [0]]
    solution, _, rank, singular = np.linalg.lstsq(differences, -columns[:, 0], rcond=1e-12)
    free = np.r_[1 - solution.sum(), solution]
    equal = np.ones(columns.shape[1], dtype=complex) / columns.shape[1]
    sizes = np.arange(1, cutoff + 1)
    cost = lambda w: float(np.dot(sizes, abs(divisor_indicator @ w))) / cutoff ** 2
    budget = max(1.0, u ** (2 * sigma - 1))
    base, fitted = cost(equal), cost(free)
    fraction = 1.0 if fitted <= budget else (budget - base) / (fitted - base)
    clipped = (1 - fraction) * equal + fraction * free
    if not 0 <= fraction <= 1 or cost(clipped) > budget + 2e-8:
        raise ArithmeticError('The centered fit exceeded its complete divisor budget')
    records = [mixture_record(label, w, columns, gram, original, u ** (2 - 4 * sigma), divisor_indicator)
               for label, w in [('unconstrained_affine', free), ('equal_affine', equal),
                                ('overlap_budget_clipped_affine', clipped)]]
    return dict(
        column_means=[pair(z) for z in means],
        full_gram_real=gram.real.tolist(), full_gram_imag=gram.imag.tolist(),
        full_covariance_real=covariance.real.tolist(), full_covariance_imag=covariance.imag.tolist(),
        affine_difference_rank=int(rank), affine_difference_singular_values=singular.tolist(),
        normalized_divisor_budget=budget, overlap_clipped_fraction=fraction, mixtures=records,
    ), covariance


def probe(u, count, zeros, real_parts):
    start, cutoff, maximum = u ** 4, u ** 3, 2 * u ** 4
    thresholds, high, integer_columns, indicator = coefficient_columns(u, count)
    mu, _, _ = arithmetic_arrays(cutoff)
    n = np.arange(1, maximum + 1)
    for zero_index in zeros:
        ordinate = mp.zetazero(zero_index).imag
        for sigma in real_parts:
            s_mp, s = mp.mpc(sigma, ordinate), complex(sigma, ordinate)
            zeta = complex(mp.zeta(s_mp))
            alpha = 1 - 2 * 2 ** (-s)
            powers = np.exp(-s * np.log(n))
            low_inverse_terms = mu[1:] * powers[:cutoff]
            inverse_prefixes = indicator.T @ low_inverse_terms
            shifts = zeta * inverse_prefixes
            original = window_prefix(high[1:] * powers, start) / alpha
            raw = np.array([window_prefix(c[1:] * powers, start) / alpha for c in integer_columns]).T
            centered = raw + shifts
            centered_original = original + zeta * low_inverse_terms.sum()
            raw_record, raw_cov = fit_family(u, sigma, raw, original, indicator)
            centered_record, centered_cov = fit_family(u, sigma, centered, centered_original, indicator)
            check_close(raw_cov, centered_cov, 'centering preserves every covariance cross term')
            raw_mean = raw.mean(axis=0)
            raw_gram = raw.conj().T @ raw / start
            centered_gram = centered.conj().T @ centered / start
            update = (np.outer(raw_mean.conj(), shifts) + np.outer(shifts.conj(), raw_mean) +
                      np.outer(shifts.conj(), shifts))
            check_close(centered_gram, raw_gram + update, 'full complex Gram centering update')
            transfers = []
            for fitted_on, family in [('raw', raw_record), ('centered', centered_record)]:
                for fit in family['mixtures']:
                    weights = np.array([complex(*z) for z in fit['weights']])
                    raw_values, centered_values = raw @ weights, centered @ weights
                    shift = np.dot(shifts, weights)
                    check_close(centered_values - raw_values, shift, 'every mixed physical centering shift')
                    transfers.append(dict(
                        fitted_on=fitted_on, mixture=fit['mixture'],
                        raw_rms=float(np.mean(abs(raw_values) ** 2) ** 0.5),
                        centered_rms=float(np.mean(abs(centered_values) ** 2) ** 0.5),
                        normalized_inverse_shift=pair(shift),
                    ))
            yield dict(
                status='floating-point diagnostic; off-critical centering changes the carrier',
                u=u, physical_start=start, physical_length=start, divisor_cutoff=cutoff,
                thresholds=thresholds, zero_index=zero_index, sampled_s=pair(s),
                sample_is_on_critical_line=(sigma == 0.5), zeta_value=pair(zeta),
                selected_inverse_prefixes=[pair(z) for z in inverse_prefixes],
                normalized_centering_shifts=[pair(z) for z in shifts],
                maximum_covariance_change=float(np.max(abs(raw_cov - centered_cov))),
                coefficient_identities_checked_with_integers=True,
                centered_equals_original_at_actual_zero=True,
                theorem_budget_requires_actual_zero=True,
                raw=raw_record, centered=centered_record, coefficient_transfers=transfers,
            )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scales', nargs='+', type=positive_integer, default=[4, 8, 16, 32])
    parser.add_argument('--cutoffs', type=positive_integer, default=7)
    parser.add_argument('--zeros', nargs='+', type=positive_integer, default=[1, 2])
    parser.add_argument('--real-parts', nargs='+', type=float, default=[0.5, 0.75])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if min(args.scales) < 2 or args.cutoffs < 2 or any(not 0 < s < 1 for s in args.real_parts):
        parser.error('Scales and cutoff count must be >=2; real parts must be in the open unit interval')
    mp.mp.dps = 40
    records = []
    for u in sorted(set(args.scales)):
        for record in probe(u, args.cutoffs, args.zeros, args.real_parts):
            records.append(record)
            print(json.dumps(dict(u=u, s=record['sampled_s'], transfers=record['coefficient_transfers']),
                             allow_nan=False), flush=True)
    if args.output:
        args.output.write_text(json.dumps(dict(
            status='floating-point exploration; centering is not a new zero hypothesis',
            records=records,
        ), indent=2, allow_nan=False) + '\n')


if __name__ == '__main__':
    main()

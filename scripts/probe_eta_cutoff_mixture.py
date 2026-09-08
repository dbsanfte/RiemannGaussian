#!/usr/bin/env python3
"""Test joint cutoff mixtures with their source-transport costs retained.

Floating-point exploration only. Every column includes both its rough
model and complementary original products; all physical Gram entries are
used. The coefficient identities are checked with integers. Off-critical
samples at known zero ordinates are not zeros. Budget shapes omit the
zero-dependent theorem constant and are not certified error bounds.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy

from probe_eta_coprime_products import (
    arithmetic_arrays, check_close, high_product_coefficients, positive_integer, window_prefix,
)


def pair(z):
    return [float(z.real), float(z.imag)]


def coefficient_columns(u, count):
    maximum, cutoff = 2 * u ** 4, u ** 3
    mu, least, _ = arithmetic_arrays(maximum)
    high = high_product_coefficients(mu, cutoff, maximum)
    largest = np.zeros(maximum + 1, dtype=np.int64)
    for p in sympy.primerange(2, maximum + 1):
        largest[p::p] = p
    thresholds = sorted({2 * u, 2 * u ** 2} |
                        {round(2 * u * u ** (j / (count - 1))) for j in range(count)})
    source = np.zeros(maximum + 1, dtype=np.int64)
    source[1], source[2] = 1, -2
    n = np.arange(maximum + 1)
    selected_low = np.zeros(maximum + 1, dtype=np.int64)
    previous = -1
    columns = []
    for threshold in thresholds:
        for d in np.flatnonzero((mu[:cutoff + 1] != 0) &
                               (largest[:cutoff + 1] > previous) &
                               (largest[:cutoff + 1] <= threshold)):
            q = np.arange(1, maximum // d + 1)
            selected_low[d::d] += int(mu[d]) * np.where(q % 2, 1, -1)
        rough = np.flatnonzero((n > 1) & (n % 2 == 1) & (least > threshold))
        model = np.zeros(maximum + 1, dtype=np.int64)
        model[rough] = -1
        model[2 * rough[rough <= maximum // 2]] += 2
        paired = model + np.where(largest <= threshold, high, 0)
        if not np.array_equal(paired, source - selected_low):
            raise ArithmeticError('A full cutoff column lost a product or a source coefficient')
        columns.append(paired)
        previous = threshold
    divisor_indicator = np.array([largest[1:cutoff + 1] <= y for y in thresholds],
                                 dtype=np.float64).T
    return thresholds, high, columns, divisor_indicator


def mixture_record(label, weights, columns, gram, original, budget_unit, divisor_indicator):
    values = columns @ weights
    energy = float(np.mean(abs(values) ** 2))
    means = columns.mean(axis=0)
    original_mean = np.mean(original)
    transported = np.dot(weights, means - original_mean)
    triangle_cost = float(np.dot(abs(weights), abs(means - original_mean)))
    check_close(weights.sum(), 1, 'affine cutoff normalization')
    check_close(energy, np.vdot(weights, gram @ weights), 'full mixed Gram energy')
    check_close(np.mean(values) - original_mean, transported, 'full signed transport mean')
    rms = energy ** 0.5
    if abs(original_mean) > rms + abs(transported) + 2e-8:
        raise ArithmeticError('Mean/energy transport inequality failed')
    source_error = abs(np.mean(values) - 1)
    if rms + source_error < 1 - 2e-8:
        raise ArithmeticError('The complete measured source error was omitted')
    l1 = float(np.sum(abs(weights)))
    cutoff = len(divisor_indicator)
    effective_weights = divisor_indicator @ weights
    overlap_mass = float(np.dot(np.arange(1, cutoff + 1), abs(effective_weights)))
    overlap_unit = overlap_mass / cutoff ** 2
    if overlap_unit > l1 + 2e-8:
        raise ArithmeticError('Combining overlapping divisor selections increased the coarse budget')
    return dict(
        mixture=label, weights=[pair(z) for z in weights], weight_l1=l1,
        full_energy_over_source_square=energy, rms_over_source=rms,
        first_mean_over_source=pair(np.mean(values)),
        full_signed_transport_mean_over_source=pair(transported),
        measured_transport_triangle_over_source=triangle_cost,
        rms_plus_measured_transport=rms + abs(transported),
        rms_plus_measured_transport_triangle=rms + triangle_cost,
        measured_source_error_over_source=float(source_error),
        rms_plus_measured_source_error=float(rms + source_error),
        rms_plus_all_measured_transport_costs=float(rms + abs(transported) + abs(original_mean - 1)),
        theorem_budget_shape_without_constant=budget_unit * l1,
        effective_divisor_mass=overlap_mass,
        effective_divisor_mass_over_cutoff_square=overlap_unit,
        overlap_budget_shape_without_constant=budget_unit * overlap_unit,
    )


def probe(u, count, zeros, real_parts):
    start, maximum = u ** 4, 2 * u ** 4
    thresholds, high, integer_columns, divisor_indicator = coefficient_columns(u, count)
    n = np.arange(1, maximum + 1)
    for zero_index in zeros:
        ordinate = mp.zetazero(zero_index).imag
        for sigma in real_parts:
            s_mp, s = mp.mpc(sigma, ordinate), complex(sigma, ordinate)
            alpha = 1 - 2 * 2 ** (-s)
            powers = np.exp(-s * np.log(n))
            original = window_prefix(high[1:] * powers, start) / alpha
            columns = np.array([window_prefix(c[1:] * powers, start) / alpha
                                for c in integer_columns]).T
            gram = columns.conj().T @ columns / start
            check_close(gram, gram.conj().T, 'Hermitian full physical Gram')
            differences = columns[:, 1:] - columns[:, [0]]
            solution, _, rank, singular_values = np.linalg.lstsq(differences, -columns[:, 0], rcond=1e-12)
            free_weights = np.r_[1 - solution.sum(), solution]
            budget_unit = u ** (2 - 4 * sigma)
            ridge = budget_unit
            ones = np.ones(len(thresholds), dtype=complex)
            regularized = np.linalg.solve(gram + ridge * np.eye(len(thresholds)), ones)
            regularized /= np.vdot(ones, regularized)
            equal = ones / len(thresholds)
            coefficient_budget = max(1.0, u ** (2 * sigma - 1))
            free_mass = float(np.sum(abs(free_weights)))
            clip_fraction = (min(1.0, (coefficient_budget - 1) / (free_mass - 1))
                             if free_mass > 1 else 1.0)
            clipped = (1 - clip_fraction) * equal + clip_fraction * free_weights
            if np.sum(abs(clipped)) > coefficient_budget + 2e-8:
                raise ArithmeticError('Clipped affine coefficients exceed their explicit norm budget')
            divisor_sizes = np.arange(1, u ** 3 + 1)
            overlap_mass = lambda w: float(np.dot(divisor_sizes, abs(divisor_indicator @ w))) / u ** 6
            free_overlap, base_overlap = overlap_mass(free_weights), overlap_mass(equal)
            overlap_fraction = (1.0 if free_overlap <= coefficient_budget else
                                (coefficient_budget - base_overlap) / (free_overlap - base_overlap))
            overlap_clipped = (1 - overlap_fraction) * equal + overlap_fraction * free_weights
            if not 0 <= overlap_fraction <= 1 or overlap_mass(overlap_clipped) > coefficient_budget + 2e-8:
                raise ArithmeticError('Overlap-aware clipping exceeded the full divisor budget')
            cases = [mixture_record(label, w, columns, gram, original, budget_unit, divisor_indicator)
                     for label, w in [('unconstrained_affine', free_weights),
                                      ('ridge_affine', regularized), ('equal_affine', equal),
                                      ('budget_clipped_affine', clipped),
                                      ('overlap_budget_clipped_affine', overlap_clipped)]]
            objective = lambda w: float(np.vdot(w, (gram + ridge * np.eye(len(w))) @ w).real)
            if objective(regularized) > objective(equal) + 2e-8:
                raise ArithmeticError('Regularized affine solve failed its feasible comparison')
            yield dict(
                status='floating-point exploration, not a theorem or zero bound',
                u=u, divisor_cutoff=u ** 3, physical_start=start, physical_length=start,
                thresholds=thresholds, zero_index=zero_index, sampled_s=pair(s),
                sample_is_on_critical_line=(sigma == 0.5),
                numerical_zeta_absolute=float(abs(mp.zeta(s_mp))),
                every_integer_column_identity_passed=True,
                original_mean_over_source=pair(np.mean(original)),
                column_means_over_source=[pair(z) for z in columns.mean(axis=0)],
                full_gram_real=gram.real.tolist(), full_gram_imag=gram.imag.tolist(),
                affine_difference_rank=int(rank), affine_difference_singular_values=singular_values.tolist(),
                ridge_parameter=ridge, coefficient_l1_budget=coefficient_budget,
                clipped_fraction=clip_fraction,
                overlap_clipped_fraction=overlap_fraction,
                first_mean_theorem_allowance_requires_actual_zero_hypothesis=True,
                mixtures=cases,
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
        parser.error('Scales and cutoff count must be >=2; real parts must be between zero and one')
    mp.mp.dps = 40
    records = []
    for u in sorted(set(args.scales)):
        for r in probe(u, args.cutoffs, args.zeros, args.real_parts):
            records.append(r)
            print(json.dumps(dict(u=u, s=r['sampled_s'], mixtures=[
                {k: c[k] for k in ['mixture', 'rms_over_source', 'weight_l1',
                                  'rms_plus_measured_source_error', 'theorem_budget_shape_without_constant',
                                  'overlap_budget_shape_without_constant']}
                for c in r['mixtures']]), allow_nan=False), flush=True)
    if args.output:
        args.output.write_text(json.dumps(dict(
            status='floating-point exploration, not a theorem or zero bound',
            off_critical_samples_are_not_zeros=True, records=records,
        ), indent=2, allow_nan=False) + '\n')


if __name__ == '__main__':
    main()

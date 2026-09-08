#!/usr/bin/env python3
"""Separate the coprime energy by least odd prime, retaining factor-count signs.

Floating-point exploration only; this supplies no Lean theorem or zero bound.
Uses the literal coefficients and complete cubic physical window from
probe_eta_coprime_products.py. Computes the sum of the Gram matrices WITHIN
each least-prime family, and the contribution BETWEEN different families.
The latter may have either sign. All energies are divided by the source square.

Example:
  python scripts/probe_eta_least_prime_groups.py --scale 128 --zeros 1 2 \
      --thresholds 1 7 128 --output /tmp/eta-least-prime-groups.json

Requirements: numpy, sympy, mpmath. The sampled zeros are on the critical
line; the cutoffs do not implement the formal growing-sieve schedule.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp
import numpy as np

from probe_eta_coprime_products import (
    arithmetic_arrays, check_close, energy, high_product_coefficients,
    positive_integer, window_prefix,
)


def probe(u, zero_indices, thresholds):
    cutoff, start, maximum = u ** 2, u ** 3, 2 * u ** 3
    mu, least, counts = arithmetic_arrays(maximum)
    b = high_product_coefficients(mu, cutoff, maximum)
    active_n = np.flatnonzero(b)
    # Stable sorting keeps each family's product endpoints increasing.
    n = active_n[np.argsort(least[active_n], kind="stable")]
    primes, factors = least[n], counts[n]
    if np.any(primes == 0):
        raise ArithmeticError("Unexpected nonzero pure dyadic coefficient")
    new_group = np.r_[True, primes[1:] != primes[:-1]]
    starts = np.flatnonzero(new_group)
    groups = np.cumsum(new_group) - 1
    ends = np.r_[starts[1:] - 1, len(n) - 1]
    # An event at n contributes to exactly this fraction of the physical window.
    kernel = np.minimum(1, np.maximum(0, (2 * start - n) / start))
    next_n = np.r_[n[1:], 2 * start]
    next_n[ends] = 2 * start
    durations = np.maximum(0, np.minimum(next_n, 2 * start) - np.maximum(n, start))
    levels = np.unique(factors)

    for zero_index in zero_indices:
        zero = mp.zetazero(zero_index)
        s = complex(zero)
        source_square = abs(1 - 2 * np.exp(-s * np.log(2))) ** 2
        weights = b[n] * np.exp(-s * np.log(n))
        before = []
        for level in levels:
            cumulative = np.r_[0j, np.cumsum(np.where(factors == level, weights, 0))]
            before.append(cumulative[:-1] - cumulative[starts[groups]])
        cumulative = np.r_[0j, np.cumsum(weights)]
        after = cumulative[1:] - cumulative[starts[groups]]
        for threshold in sorted(set(thresholds)):
            keep = primes > threshold
            within = np.zeros((len(levels), len(levels)), dtype=complex)
            for jindex, j in enumerate(levels):
                wj = np.where(keep & (factors == j), weights, 0)
                for kindex, k in enumerate(levels):
                    wk = np.where(keep & (factors == k), weights, 0)
                    # Jump in F_j*conj(F_k), integrated over all later endpoints.
                    within[jindex, kindex] = np.sum(kernel * (
                        wj * np.conj(before[kindex]) +
                        before[jindex] * np.conj(wk) + wj * np.conj(wk)
                    )) / source_square
            # Independent integration of each family's sparse step function.
            same_prime_energy = float(np.sum(durations[keep] * abs(after[keep]) ** 2)
                                      / start / source_square)
            check_close(within.sum(), same_prime_energy, "least-prime step integration")
            natural_weights = np.zeros(maximum, dtype=complex)
            natural_weights[n[keep] - 1] = weights[keep]
            full_energy = energy(window_prefix(natural_weights, start), source_square)
            yield dict(
                status="floating-point exploration, not a Lean theorem or zero bound",
                u=u, divisor_cutoff=cutoff, physical_start=start, physical_length=start,
                zero_index=zero_index, sampled_s=[s.real, s.imag],
                numerical_zeta_residual=float(abs(mp.zeta(zero))),
                threshold=threshold, distinct_odd_factor_counts=levels.tolist(),
                surviving_over_source=full_energy,
                same_least_prime_energy=same_prime_energy,
                different_least_prime_cross=full_energy - same_prime_energy,
                same_least_prime_group_diagonal=float(np.trace(within).real),
                same_least_prime_factor_cross=float((within.sum() - np.trace(within)).real),
                same_least_prime_factor_gram_real=within.real.tolist(),
                same_least_prime_factor_gram_imag=within.imag.tolist(),
            )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scale", type=positive_integer, default=128)
    parser.add_argument("--zeros", nargs="+", type=positive_integer, default=[1, 2])
    parser.add_argument("--thresholds", nargs="+", type=positive_integer, default=[1, 7, 128])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.scale < 2:
        parser.error("The original cubic probe requires u >= 2")
    mp.mp.dps = 35
    records = []
    for record in probe(args.scale, args.zeros, args.thresholds):
        records.append(record)
        print(json.dumps(record, allow_nan=False), flush=True)
    if args.output:
        args.output.write_text(json.dumps(dict(
            critical_line_samples_only=True,
            uses_formal_growing_sieve_schedule=False,
            records=records,
        ), indent=2, allow_nan=False) + "\n")


if __name__ == "__main__":
    main()

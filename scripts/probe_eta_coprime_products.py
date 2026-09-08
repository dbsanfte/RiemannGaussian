#!/usr/bin/env python3
"""Explore the actual coprime product energy; floating-point output is not proof.

Uses b_D(n) = sum_{q*d=n, d>D} (-1)^(q+1) mu(d), D=u^2,
and every physical endpoint M in [u^3,2*u^3). Retains all mixed terms.
The common completion factor cancels in energy / source-square ratios.
Only critical-line zeros supplied by mpmath are sampled. These finite
cutoffs do not implement the cofinal schedule in EtaMoebiusCoprimeGrowth.

Requirements: numpy, sympy, mpmath.
Example:
  python scripts/probe_eta_coprime_products.py --scales 32 64 128 \
      --zeros 1 2 --odd-factor-gram --output /tmp/eta-coprime-products.json

The factor-count Gram includes products with repeated odd prime factors.
Its (j,k) entry is mean(F_j * conjugate(F_k)) / source-square, where F_j
keeps products with exactly j distinct odd prime factors. Summing EVERY
entry recovers the surviving energy. Entrywise absolute values do not.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy


def arithmetic_arrays(maximum):
    """Integer Möbius coefficients, least odd prime, and distinct odd-factor count."""
    mu = np.ones(maximum + 1, dtype=np.int8)
    mu[0] = 0
    least_odd_prime = np.zeros(maximum + 1, dtype=np.int64)
    odd_factor_count = np.zeros(maximum + 1, dtype=np.int8)
    for p in sympy.primerange(2, maximum + 1):
        mu[p::p] *= -1
        if p * p <= maximum:
            mu[p * p::p * p] = 0
        if p != 2:
            slot = least_odd_prime[p::p]
            slot[slot == 0] = p
            odd_factor_count[p::p] += 1
    return mu, least_odd_prime, odd_factor_count


def high_product_coefficients(mu, cutoff, maximum):
    """Exact integer product grouping, iterating the short quotient variable."""
    coefficients = np.zeros(maximum + 1, dtype=np.int64)
    for q in range(1, maximum // (cutoff + 1) + 1):
        coefficients[q * (cutoff + 1)::q] += (
            (1 if q % 2 else -1) * mu[cutoff + 1:maximum // q + 1]
        )
    return coefficients


def window_prefix(weights, start):
    """All literal inclusive prefixes at start <= M < 2*start."""
    return np.r_[0j, np.cumsum(weights)][start:2 * start]


def energy(values, source_square):
    return float(np.mean(np.abs(values) ** 2) / source_square)


def check_close(left, right, label):
    if not np.allclose(left, right, rtol=2e-8, atol=2e-8):
        raise ArithmeticError(f"Failed numerical reconstruction: {label}")


def probe_scale(u, zeros, thresholds, arrays, include_gram):
    mu, least_odd_prime, odd_factor_count = arrays
    cutoff, start, maximum = u ** 2, u ** 3, 2 * u ** 3
    b = high_product_coefficients(mu, cutoff, maximum)
    n = np.arange(1, maximum + 1, dtype=np.int64)
    least = least_odd_prime[1:maximum + 1]
    counts = odd_factor_count[1:maximum + 1]
    odd_part = n // (n & -n)
    prime_ray = (odd_part > 1) & (least_odd_prime[odd_part] == odd_part)
    if np.any(b[1:][odd_part == 1]):
        raise ArithmeticError("Unexpected nonzero pure dyadic coefficient")
    if not np.array_equal(b[cutoff + 1:2 * cutoff + 1], mu[cutoff + 1:2 * cutoff + 1]):
        raise ArithmeticError("First product band disagrees with Möbius coefficients")
    # Check a direct divisor definition, independent of quotient-array slicing.
    for product in sorted({1, 2, cutoff, cutoff + 1, 2 * cutoff, start, maximum - 1}):
        direct = sum((1 if (product // d) % 2 else -1) * int(mu[d])
                     for d in sympy.divisors(product) if d > cutoff)
        if int(b[product]) != direct:
            raise ArithmeticError(f"Divisor check failed at n={product}")
    active = b[1:] != 0
    cuts = sorted(set(thresholds + [u, 2 * u, 4 * u]))
    for zero_index in zeros:
        zero = mp.zetazero(zero_index)
        s = complex(zero)
        weights = b[1:] * np.exp(-s * np.log(n))
        full = window_prefix(weights, start)
        source = 1 - 2 * np.exp(-s * np.log(2))
        source_square = abs(source) ** 2
        for threshold in cuts:
            keep = (least > threshold) | (least == 0)
            surviving = window_prefix(np.where(keep, weights, 0), start)
            single = window_prefix(np.where(keep & prime_ray, weights, 0), start)
            other = surviving - single
            removed = full - surviving
            surviving_energy = energy(surviving, source_square)
            removed_energy = energy(removed, source_square)
            single_energy = energy(single, source_square)
            other_energy = energy(other, source_square)
            single_other = float(2 * np.mean((single * np.conj(other)).real) / source_square)
            surviving_removed = float(2 * np.mean((surviving * np.conj(removed)).real) / source_square)
            check_close(surviving_energy, single_energy + other_energy + single_other,
                        "prime-ray split")
            check_close(energy(full, source_square),
                        surviving_energy + removed_energy + surviving_removed,
                        "surviving/removed split")
            record = dict(
                u=u, divisor_cutoff=cutoff, physical_start=start, physical_length=start,
                zero_index=zero_index, sampled_s=[s.real, s.imag],
                numerical_zeta_residual=float(abs(mp.zeta(zero))),
                threshold=threshold,
                active_product_fraction=float(np.count_nonzero(keep & active) / np.count_nonzero(active)),
                full_over_source=energy(full, source_square),
                surviving_over_source=surviving_energy,
                removed_over_source=removed_energy,
                surviving_removed_cross=surviving_removed,
                triangle_ratio=float(np.sqrt(surviving_energy) + np.sqrt(removed_energy)),
                single_odd_prime_ray_energy=single_energy,
                other_odd_part_energy=other_energy,
                single_other_cross=single_other,
            )
            if include_gram:
                sectors = sorted(int(k) for k in np.unique(counts[keep & active]))
                prefixes = np.asarray([
                    window_prefix(np.where(keep & (counts == k), weights, 0), start)
                    for k in sectors
                ])
                if sectors:
                    gram = prefixes @ prefixes.conj().T / start / source_square
                    check_close(prefixes.sum(axis=0), surviving, "factor-count prefixes")
                    check_close(gram.sum(), surviving_energy, "full factor-count Gram")
                else:
                    gram = np.empty((0, 0), dtype=complex)
                    check_close(surviving_energy, 0, "empty surviving family")
                record.update(
                    distinct_odd_factor_counts=sectors,
                    factor_gram_real=gram.real.tolist(),
                    factor_gram_imag=gram.imag.tolist(),
                    factor_gram_diagonal=float(np.trace(gram).real),
                    factor_gram_off_diagonal=float((gram.sum() - np.trace(gram)).real),
                )
            yield record


def positive_integer(text):
    value = int(text)
    if value < 1:
        raise argparse.ArgumentTypeError("Must be a positive integer")
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scales", nargs="+", type=positive_integer, default=[32, 64, 128])
    parser.add_argument("--zeros", nargs="+", type=positive_integer, default=[1, 2])
    parser.add_argument("--thresholds", nargs="+", type=positive_integer, default=[1, 3, 5, 7, 11, 17, 31, 63])
    parser.add_argument("--odd-factor-gram", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if min(args.scales) < 2:
        parser.error("The original cubic probe requires u >= 2")
    mp.mp.dps = 35
    arrays = arithmetic_arrays(2 * max(args.scales) ** 3)
    records = []
    for u in sorted(set(args.scales)):
        for record in probe_scale(u, args.zeros, args.thresholds, arrays, args.odd_factor_gram):
            records.append(record)
            print(json.dumps(record, allow_nan=False), flush=True)
    if args.output:
        args.output.write_text(json.dumps(dict(
            status="floating-point exploration, not a Lean theorem or zero bound",
            critical_line_samples_only=True,
            uses_formal_growing_sieve_schedule=False,
            versions=dict(numpy=np.__version__, sympy=sympy.__version__, mpmath=mp.__version__),
            records=records,
        ), indent=2, allow_nan=False) + "\n")


if __name__ == "__main__":
    main()

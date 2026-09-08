#!/usr/bin/env python3
"""Test exact prime weights against the full actual quartic Moebius carrier.

Floating-point exploration only, not a theorem or a zero bound. The density
weights minimize the complete-period quadratic form for prime divisibility:
H=sum_p 1/(p-1), w_p=p/((p-1)*(1+H)), minimum=1/(1+H).
The code separately evaluates the actual complex first mean and the whole
physical mean square, including all cross terms between prime classes.

Every physical endpoint A<=M<2*A is used, with A=u^4 and D=u^3. Samples at
real parts other than 1/2 are NOT zeros; their zeta values are recorded.
The finite prime cutoffs are exploratory and need not equal the formal
growing cutoff. The completion factor cancels in source-normalized ratios.
"""

import argparse
from fractions import Fraction
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


def exact_density_weights(primes):
    """Exact rational normal-equation and minimum checks, before any floats."""
    h = sum((Fraction(1, p - 1) for p in primes), Fraction(0))
    weights = [Fraction(p, p - 1) / (1 + h) for p in primes]
    gram = [[Fraction(1, int(sympy.ilcm(p, q))) for q in primes] for p in primes]
    for p, row in zip(primes, gram):
        if sum((a * w for a, w in zip(row, weights)), Fraction(0)) != Fraction(1, p):
            raise ArithmeticError("Exact density normal equation failed")
    quadratic = 1 - 2 * sum((w / p for w, p in zip(weights, primes)), Fraction(0))
    quadratic += sum((weights[i] * gram[i][j] * weights[j]
                      for i in range(len(primes)) for j in range(len(primes))), Fraction(0))
    if quadratic != 1 / (1 + h) or any(w < 0 or w > 1 for w in weights):
        raise ArithmeticError("Exact density minimum or weight bound failed")
    return h, weights, gram


def single_prime_ray_formula(u, s, primes):
    """Independent prime-only formula for the full ray mean, valid for u>=3.

    This uses the exact coefficients on p and its dyadic companions, rather
    than the Moebius array. The eventual PNT main term is recorded separately;
    finite scales need not approximate it and it is not a numerical bound.
    """
    start, cutoff = u ** 4, u ** 3

    def weighted_sum(products):
        ramp = np.maximum(0, start - np.maximum(0, products - start)) / start
        return np.sum(ramp * np.exp(-s * np.log(products)))

    large = primes[primes > cutoff]
    large_pair = -weighted_sum(large) + 2 * weighted_sum(2 * large)
    middle = primes[(2 * primes > cutoff) & (primes <= cutoff)]
    middle_dyadic = 0j
    factor = 2
    while len(middle) and factor * int(middle[0]) < 2 * start:
        middle_dyadic += (1 if factor == 2 else -1) * weighted_sum(factor * middle)
        factor *= 2
    z = 1 - s
    leading_constant = np.log(2) * (2 ** (z + 1) - 1) / (z * (z + 1))
    eventual_main = leading_constant * start ** z / np.log(start) ** 2
    return large_pair, middle_dyadic, eventual_main


def probe(u, zero_indices, real_parts, thresholds):
    start, cutoff, maximum = u ** 4, u ** 3, 2 * u ** 4
    mu, least_odd_prime, odd_factor_count = arithmetic_arrays(maximum)
    b = high_product_coefficients(mu, cutoff, maximum)
    n = np.arange(1, maximum + 1)
    ramp = np.maximum(0, start - np.maximum(0, n - start)) / start
    single_odd_prime = odd_factor_count[1:] == 1
    odd_prime_product = least_odd_prime[1:] == n
    odd_primes = n[odd_prime_product]
    odd_part = n // (n & -n)
    higher_single_prime_power = single_odd_prime & (odd_part != least_odd_prime[1:])
    if np.any(b[1:][odd_factor_count[1:] == 0]):
        raise ArithmeticError("Unexpected high coefficient on a pure dyadic product")
    if u >= 3 and np.any(b[1:][higher_single_prime_power]):
        raise ArithmeticError("Unexpected higher single-prime-power coefficient on a quartic window")
    endpoint_cuts = {int(mp.floor(mp.power(u, 2 * sigma - 1))) for sigma in real_parts}
    prime_sets = {r: list(sympy.primerange(3, r + 1))
                  for r in sorted(set(thresholds) | endpoint_cuts) if r <= u}
    all_primes = sorted(set(p for ps in prime_sets.values() for p in ps))

    for zero_index in zero_indices:
        zero = mp.zetazero(zero_index)
        for sigma in real_parts:
            s_mp = mp.mpc(sigma, zero.imag)
            s = complex(s_mp)
            alpha = 1 - 2 * np.exp(-s * np.log(2))
            alpha_square = abs(alpha) ** 2
            terms = b[1:] * np.exp(-s * np.log(n))
            full = window_prefix(terms, start)
            prime_channel = window_prefix(np.where(odd_prime_product, terms, 0), start)
            companion_channel = window_prefix(np.where(single_odd_prime & ~odd_prime_product,
                                                        terms, 0), start)
            ray_formula = single_prime_ray_formula(u, s, odd_primes) if u >= 3 else None
            if ray_formula is not None:
                check_close(ray_formula[0] + ray_formula[1],
                            np.mean(prime_channel + companion_channel), 'exact prime-only ray formula')
            full_mean = np.mean(full)
            check_close(full_mean, np.sum(ramp * terms), "full first mean/ramp")
            prime_prefixes = {}
            for p in all_primes:
                selected = np.zeros_like(terms)
                selected[p - 1::p] = terms[p - 1::p]
                prime_prefixes[p] = window_prefix(selected, start)

            for threshold, primes in prime_sets.items():
                h, rational_weights, density_gram = exact_density_weights(primes)
                weights = np.array([float(w) for w in rational_weights])
                vectors = np.array([prime_prefixes[p] for p in primes], dtype=complex)
                vectors = vectors.reshape((len(primes), start))
                prime_means = np.mean(vectors, axis=1)
                gram = vectors @ vectors.conj().T / start / alpha_square
                mixed = vectors @ full.conj() / start / alpha_square
                removed = weights @ vectors
                surviving = full - removed
                residual = np.ones(maximum)
                for p, weight in zip(primes, weights):
                    residual[p - 1::p] -= weight
                if np.any(residual[single_odd_prime & (b[1:] != 0)] != 1):
                    raise ArithmeticError("The small-prime sieve changed an active single-prime ray")
                check_close(np.mean(surviving), np.sum(ramp * terms * residual),
                            "weighted first mean/product multiplier")
                full_energy = float(np.mean(abs(full) ** 2) / alpha_square)
                energy = float(np.mean(abs(surviving) ** 2) / alpha_square)
                diagonal = float(np.dot(weights ** 2, np.diag(gram).real))
                selected_energy = float((weights @ gram @ weights).real)
                check_close(energy, full_energy - 2 * np.dot(weights, mixed.real)
                            + selected_energy, "all physical Gram cross terms")

                density_minimum = 1 / (1 + h)
                finite_density = 1 - 2 * sum(w * (maximum // p) / maximum
                                           for w, p in zip(weights, primes))
                finite_density += sum(weights[i] * weights[j]
                                      * (maximum // int(sympy.ilcm(p, q))) / maximum
                                      for i, p in enumerate(primes) for j, q in enumerate(primes))
                check_close(finite_density, np.mean(residual ** 2),
                            "exact finite divisibility count formula")
                cauchy = float(np.sqrt(np.sum(abs(terms) ** 2)
                                      * np.sum((ramp * residual) ** 2)) / abs(alpha))
                multiple_channel = window_prefix(np.where(odd_factor_count[1:] >= 2,
                                                           terms * residual, 0), start)
                channels = np.array([prime_channel, companion_channel, multiple_channel])
                check_close(channels.sum(axis=0), surviving, "all prime/composite physical channels")
                channel_gram = channels @ channels.conj().T / start / alpha_square
                check_close(channel_gram.sum(), energy, "complete prime/composite Gram")
                channel_means = np.mean(channels, axis=1) / alpha
                check_close(channel_means.sum(), np.mean(surviving) / alpha,
                            "prime/composite first means")
                ray_energy = float(channel_gram[:2, :2].sum().real)
                multiple_energy = float(channel_gram[2, 2].real)
                ray_multiple_mixed = channel_gram[:2, 2].sum()
                yield dict(
                    status="floating-point exploration, not a Lean theorem or zero bound",
                    u=u, physical_start=start, physical_length=start, divisor_cutoff=cutoff,
                    zero_index=zero_index, sampled_s=pair(s),
                    sample_is_on_critical_line=(sigma == 0.5),
                    numerical_zeta_absolute=float(abs(mp.zeta(s_mp))), threshold=threshold,
                    formal_prime_cutoff=int(mp.floor(mp.power(u, sigma - 0.5))),
                    harmonic_endpoint_cutoff=int(mp.floor(mp.power(u, 2 * sigma - 1))),
                    uses_harmonic_endpoint_cutoff=(threshold == int(mp.floor(mp.power(u, 2 * sigma - 1)))),
                    primes=primes, weights_exact=[str(w) for w in rational_weights],
                    density_minimum_exact=str(density_minimum),
                    density_mean_square=float(finite_density),
                    full_first_mean_over_source=pair(full_mean / alpha),
                    surviving_first_mean_over_source=pair(np.mean(surviving) / alpha),
                    weighted_prime_mean_over_source=pair(np.dot(weights, prime_means) / alpha),
                    sum_prime_mean_norms_over_source=float(np.sum(abs(prime_means)) / abs(alpha)),
                    full_energy_over_source_square=full_energy,
                    surviving_energy_over_source_square=energy,
                    selected_energy_diagonal=diagonal,
                    selected_energy_cross=selected_energy - diagonal,
                    selected_full_mixed=pair(np.dot(weights, mixed)),
                    cauchy_allowance_over_source=cauchy,
                    channel_labels=["odd_prime_products", "one_prime_companions",
                                    "at_least_two_distinct_odd_primes"],
                    channel_first_means_over_source=[pair(z) for z in channel_means],
                    channel_gram_real=channel_gram.real.tolist(),
                    channel_gram_imag=channel_gram.imag.tolist(),
                    single_prime_ray_energy=ray_energy,
                    multiple_prime_energy=multiple_energy,
                    single_multiple_cross=2 * float(ray_multiple_mixed.real),
                    single_multiple_coherence=(pair(ray_multiple_mixed / np.sqrt(
                        ray_energy * multiple_energy)) if ray_energy > 0 and multiple_energy > 0 else None),
                    sieve_preserves_active_single_prime_rays=True,
                    higher_single_prime_powers_have_zero_coefficient=bool(
                        np.all(b[1:][higher_single_prime_power] == 0)),
                    prime_only_ray_formula_over_source=(pair((ray_formula[0] + ray_formula[1]) / alpha)
                                                        if ray_formula is not None else None),
                    large_prime_pair_first_mean_over_source=(pair(ray_formula[0] / alpha)
                                                            if ray_formula is not None else None),
                    middle_prime_dyadic_first_mean_over_source=(pair(ray_formula[1] / alpha)
                                                               if ray_formula is not None else None),
                    eventual_pnt_ray_main_term_over_source=(pair(ray_formula[2] / alpha)
                                                           if ray_formula is not None else None),
                    eventual_pnt_main_term_is_not_a_finite_bound=True,
                )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scales", nargs="+", type=positive_integer, default=[8, 16, 24, 32])
    parser.add_argument("--zeros", nargs="+", type=positive_integer, default=[1, 2])
    parser.add_argument("--real-parts", nargs="+", type=float, default=[0.5, 0.75])
    parser.add_argument("--thresholds", nargs="+", type=positive_integer, default=[3, 7, 13, 31])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if min(args.scales) < 2 or any(not 0 < sigma < 1 for sigma in args.real_parts):
        parser.error("Scales must be >=2, and real parts must lie strictly between zero and one")
    mp.mp.dps = 40
    records = []
    for u in sorted(set(args.scales)):
        for record in probe(u, args.zeros, args.real_parts, sorted(set(args.thresholds))):
            records.append(record)
            print(json.dumps({key: record[key] for key in (
                "u", "sampled_s", "threshold", "density_mean_square",
                "surviving_first_mean_over_source", "surviving_energy_over_source_square",
                "cauchy_allowance_over_source",
            )}, allow_nan=False), flush=True)
    if args.output:
        args.output.write_text(json.dumps(dict(
            status="floating-point exploration, not a Lean theorem or zero bound",
            off_critical_samples_are_not_zeros=True,
            finite_thresholds_are_exploratory=True,
            records=records,
        ), indent=2, allow_nan=False) + "\n")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Audit quartic first means and complete quotient shells; floats are not proof.

Uses the actual integer Moebius coefficients on A=u^4, D=u^3. Complete
quotient fibres and their clipped boundary are counted over EVERY integer
M in [A,2*A). An independent fixed-product ramp sum checks the high mean.
The optional odd-prime exclusion is imposed on both arithmetic factors.

The comparison model replaces the weighted coprime Moebius prefix by
kappa_P*log(x), with kappa_P=1/(zeta'(rho)*prod_{p|P}(1-p^(-rho))).
It is a diagnostic model, not an estimate for the actual Moebius sequence.
Only numerical critical-line zeros are sampled. Finite test cutoffs do not
implement the formal growing-modulus schedule.

Example:
  python scripts/probe_eta_first_mean_shells.py --scales 8 16 24 32 \
      --zeros 1 2 --thresholds 1 3 7 --output /tmp/eta-first-mean-shells.json
"""

import argparse
import json
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy

from probe_eta_coprime_products import (
    arithmetic_arrays, check_close, high_product_coefficients, positive_integer,
)


def pair(z):
    return [float(z.real), float(z.imag)]


def probe_model(u, zero_index, threshold):
    """The explicit logarithmic model at large quotient caps; no Moebius array."""
    s = complex(mp.zetazero(zero_index))
    derivative = complex(mp.diff(mp.zeta, mp.zetazero(zero_index)))
    source = 1 - 2 * np.exp(-s * np.log(2))
    start, cutoff = u ** 4, u ** 3
    q = np.arange(1, (2 * start - 1) // (cutoff + 1) + 1, dtype=np.int64)
    primes = list(sympy.primerange(3, threshold + 1))
    keep = np.ones(q.shape, dtype=bool)
    for p in primes:
        keep &= q % p != 0
    eta_prefix = np.cumsum(np.where(keep, np.where(q % 2, 1, -1)
                                    * np.exp(-s * np.log(q)), 0))
    euler_factor = np.prod([1 - np.exp(-s * np.log(p)) for p in primes])
    kappa = 1 / (derivative * euler_factor)
    window = np.maximum(0, start - np.maximum(0, q * (cutoff + 1) - start)) / start
    value = kappa * np.sum(eta_prefix * np.log1p(1 / q) * window) / source
    return dict(u=u, zero_index=zero_index, threshold=threshold,
                logarithmic_model_over_source=pair(value))


def probe(u, zero_indices, thresholds, arrays):
    mu, least_odd_prime, _ = arrays
    start, cutoff, maximum = u ** 4, u ** 3, 2 * u ** 4
    qmax = (maximum - 1) // (cutoff + 1)
    b = high_product_coefficients(mu, cutoff, maximum)
    n = np.arange(1, maximum + 1, dtype=np.int64)
    product_window = np.maximum(0, start - np.maximum(0, n - start)) / start
    qindices = np.arange(1, qmax + 1, dtype=np.int64)
    quotient_window = np.maximum(
        0, start - np.maximum(0, qindices * (cutoff + 1) - start)
    ) / start
    for zero_index in zero_indices:
        zero = mp.zetazero(zero_index)
        s = complex(zero)
        derivative = complex(mp.diff(mp.zeta, zero))
        source = 1 - 2 * np.exp(-s * np.log(2))
        mu_weight = mu[1:maximum + 1] * np.exp(-s * np.log(n))
        product_weight = b[1:] * np.exp(-s * np.log(n)) * product_window
        eta_terms = np.where(qindices % 2, 1, -1) * np.exp(-s * np.log(qindices))
        for threshold in thresholds:
            primes = list(sympy.primerange(3, threshold + 1))
            keep_n = ((least_odd_prime[1:maximum + 1] > threshold)
                      | (least_odd_prime[1:maximum + 1] == 0))
            keep_q = ((least_odd_prime[qindices] > threshold)
                      | (least_odd_prime[qindices] == 0))
            eta_prefix = np.cumsum(np.where(keep_q, eta_terms, 0))
            euler_factor = np.prod([1 - np.exp(-s * np.log(p)) for p in primes])
            kappa = 1 / (derivative * euler_factor)
            high_components, complete_components = [], []
            for q in qindices:
                # The half-open integer intersection [A,2*A) intersect
                # [q*d,(q+1)*d) counts exact occurrences of this fibre.
                d = np.arange(start // (q + 1) + 1, (maximum - 1) // q + 1)
                upper = np.minimum(maximum, (q + 1) * d)
                lower = np.maximum(start, q * d)
                full_lower = np.maximum(lower, q * (cutoff + 1))
                high_count = np.where(d > cutoff, np.maximum(0, upper - lower), 0)
                complete_count = np.maximum(0, upper - full_lower)
                weights = np.where(keep_n[d - 1], mu_weight[d - 1], 0)
                high_components.append(eta_prefix[q - 1] * np.dot(weights, high_count) / start)
                complete_components.append(eta_prefix[q - 1] * np.dot(weights, complete_count) / start)
            high_components = np.asarray(high_components)
            complete_components = np.asarray(complete_components)
            product_mean = np.sum(product_weight[keep_n])
            check_close(high_components.sum(), product_mean, "quotient/product first means")
            # For this model a complete fibre's weighted Moebius mass is
            # exactly kappa*log((q+1)/q), at every physical endpoint.
            model_components = kappa * eta_prefix * np.log1p(1 / qindices) * quotient_window
            shells = []
            for j in range(int(qmax).bit_length()):
                selection = (qindices >= 2 ** j) & (qindices < 2 ** (j + 1))
                actual = complete_components[selection].sum() / source
                model = model_components[selection].sum() / source
                shells.append(dict(
                    first_quotient=2 ** j,
                    last_quotient=min(qmax, 2 ** (j + 1) - 1),
                    actual_complete_over_source=pair(actual),
                    logarithmic_model_over_source=pair(model),
                ))
            yield dict(
                u=u, physical_start=start, physical_length=start, divisor_cutoff=cutoff,
                zero_index=zero_index, sampled_s=pair(s), threshold=threshold,
                excluded_odd_primes=primes,
                numerical_zeta_residual=float(abs(mp.zeta(zero))),
                kappa=pair(kappa),
                high_first_mean_over_source=pair(product_mean / source),
                complete_first_mean_over_source=pair(complete_components.sum() / source),
                added_boundary_over_source=pair((complete_components.sum() - product_mean) / source),
                logarithmic_model_over_source=pair(model_components.sum() / source),
                sum_complete_shell_norms_over_source=float(sum(
                    abs(complex(*item['actual_complete_over_source'])) for item in shells)),
                shells=shells,
            )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scales', nargs='+', type=positive_integer, default=[8, 16, 24, 32])
    parser.add_argument('--zeros', nargs='+', type=positive_integer, default=[1, 2])
    parser.add_argument('--thresholds', nargs='+', type=positive_integer, default=[1, 3, 7])
    parser.add_argument('--model-scales', nargs='+', type=positive_integer, default=[])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if min(args.scales) < 2:
        parser.error('The quartic probe requires u >= 2')
    if any(u < 2 or 2 * u ** 4 >= np.iinfo(np.int64).max for u in args.model_scales):
        parser.error('Model scales must be >=2 with 2*u^4 fitting in int64')
    mp.mp.dps = 40
    arrays = arithmetic_arrays(2 * max(args.scales) ** 4)
    records = []
    for u in sorted(set(args.scales)):
        for record in probe(u, args.zeros, sorted(set(args.thresholds)), arrays):
            records.append(record)
            print(json.dumps({key: record[key] for key in (
                'u', 'zero_index', 'threshold', 'high_first_mean_over_source',
                'complete_first_mean_over_source', 'logarithmic_model_over_source',
                'sum_complete_shell_norms_over_source',
            )}, allow_nan=False), flush=True)
    models = [probe_model(u, zero, threshold)
              for u in args.model_scales for zero in args.zeros for threshold in args.thresholds]
    for record in models:
        print(json.dumps(dict(model_only=True, **record), allow_nan=False), flush=True)
    if args.output:
        args.output.write_text(json.dumps(dict(
            status='floating-point exploration, not a Lean theorem or zero bound',
            critical_line_samples_only=True,
            uses_formal_growing_sieve_schedule=False,
            logarithmic_prefix_model_is_not_actual_moebius=True,
            versions=dict(numpy=np.__version__, sympy=sympy.__version__, mpmath=mp.__version__),
            records=records,
            model_records=models,
        ), indent=2, allow_nan=False) + '\n')


if __name__ == '__main__':
    main()

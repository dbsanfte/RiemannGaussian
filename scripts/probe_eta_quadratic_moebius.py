#!/usr/bin/env python3
"""Audit the full Heath--Brown quadratic eta kernel; floats are not proof.

The K=2 identity uses the literal truncated Moebius coefficients at
U=ceil(sqrt(2*A)). It retains every integer endpoint A<=M<2*A and every
pair a,b<=U. Optional odd-prime exclusion applies to every factor.
The exact integer identity is checked separately from complex evaluation.

The smooth pole is rank one, proportional to (sum mu(a)/a)^2.
The analytic constant is a separate complex rank-one term. Subtracting
them does not assert that the remaining matrix is positive or small.
Real symmetric eigenvalues test source-directed sign proposals for ALL
real input vectors, not just the actual Moebius vector.

Reference for the arithmetic identity: Helfgott and Thompson,
"Summing mu(n): a faster elementary algorithm", Section 2, identity 2.1,
https://doi.org/10.1007/s40993-022-00408-8 .
"""

import argparse
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy

from probe_eta_coprime_products import arithmetic_arrays, check_close, positive_integer


def pair(z):
    return [float(z.real), float(z.imag)]


def prepare(u, threshold):
    start, maximum = u ** 4, 2 * u ** 4 - 1
    upper = math.isqrt(maximum) + 1
    mu, least, _ = arithmetic_arrays(maximum)
    keep = (least > threshold) | (least == 0)
    small = np.where(keep[1:upper + 1], mu[1:upper + 1], 0).astype(np.int64)
    square = np.zeros(maximum + 1, dtype=np.int64)
    for a in range(1, upper + 1):
        if small[a - 1]:
            top = min(upper, maximum // a)
            square[a:a * top + 1:a] += small[a - 1] * small[:top]
    convolved = np.zeros(maximum + 1, dtype=np.int64)
    for r in range(1, maximum + 1):
        if keep[r]:
            convolved[r::r] += square[1:maximum // r + 1]
    reconstructed = -convolved
    reconstructed[1:upper + 1] += 2 * small
    target = np.where(keep, mu, 0)
    if not np.array_equal(reconstructed[1:], target[1:]):
        raise ArithmeticError('The integer Heath--Brown identity failed')
    divisors = np.zeros(maximum + 1, dtype=np.int64)
    for d in range(1, maximum + 1):
        divisors[d::d] += 1
    eta_zeta = divisors.copy()
    eta_zeta[2::2] -= 2 * divisors[1:maximum // 2 + 1]
    eta_zeta[~keep] = 0
    return start, maximum, upper, small, eta_zeta, keep


def averaged_divided_prefix(prefix, start, products):
    """Exact counts of every floor(M/k), using an antiderivative of the prefix."""
    primitive = np.r_[0j, np.cumsum(prefix)]

    def through(length):
        q, r = np.divmod(length, products)
        return products * primitive[q] + r * prefix[q]

    return (through(2 * start) - through(start)) / start


def probe(u, zero_index, sigma, threshold):
    start, maximum, upper, small, eta_zeta, keep = prepare(u, threshold)
    zero = mp.zetazero(zero_index)
    s = complex(sigma, float(zero.imag))
    zeta = complex(mp.zeta(mp.mpc(s.real, str(zero.imag))))
    source = 1 - 2 * np.exp(-s * np.log(2))
    primes = list(sympy.primerange(3, threshold + 1))
    euler = np.prod([1 - np.exp(-s * np.log(p)) for p in primes])
    density = np.prod([1 - 1 / p for p in primes])
    n = np.arange(1, maximum + 1, dtype=np.int64)
    powers = np.exp(-s * np.log(n))
    eta_prefix = np.r_[0j, np.cumsum(np.where(keep[1:], np.where(n % 2, 1, -1) * powers, 0))]
    convolution_prefix = np.r_[0j, np.cumsum(eta_zeta[1:] * powers)]
    # Extra endpoint 2*A may occur in the counting primitive only with zero remainder.
    eta_prefix = np.r_[eta_prefix, eta_prefix[-1]]
    convolution_prefix = np.r_[convolution_prefix, convolution_prefix[-1]]
    active = np.flatnonzero(small) + 1
    moebius = small[active - 1].astype(float)
    products = active[:, None] * active[None, :]
    product_powers = np.exp(-s * np.log(products))
    kernel = product_powers * averaged_divided_prefix(convolution_prefix, start, products)
    low = np.sum(moebius * np.exp(-s * np.log(active)) *
                 averaged_divided_prefix(eta_prefix, start, active))
    quadratic = moebius @ kernel @ moebius
    check_close(quadratic, 2 * low - source, 'whole complex quadratic/source identity')
    physical = np.arange(start, 2 * start, dtype=np.int64)
    polar_coefficient = (density ** 2 * np.log(2) / (1 - s)
                         * np.mean(np.exp((1 - s) * np.log(physical))))
    pole_kernel = polar_coefficient / products
    analytic_kernel = source * (euler * zeta) ** 2 * product_powers
    remainder = kernel - pole_kernel - analytic_kernel
    pole_value = moebius @ pole_kernel @ moebius
    analytic_value = moebius @ analytic_kernel @ moebius
    remainder_value = moebius @ remainder @ moebius
    check_close(quadratic, pole_value + analytic_value + remainder_value,
                'pole/analytic/remainder decomposition')
    harmonic = np.sum(moebius / active)
    check_close(pole_value, polar_coefficient * harmonic ** 2, 'polar rank-one factor')
    complex_prefix = np.sum(moebius * np.exp(-s * np.log(active)))
    check_close(analytic_value, source * (euler * zeta * complex_prefix) ** 2,
                'analytic rank-one factor')
    projected = (remainder / source).real
    eigenvalues = np.linalg.eigvalsh(projected)
    diagonal = np.sum(moebius ** 2 * np.diag(projected))
    value = float(moebius @ projected @ moebius)
    check_close(value, (remainder_value / source).real, 'source projection')
    # A second eta factor removes the smooth pole by an exact dyadic difference.
    # On the even window A=u^4, each cutoff in [A/2,A) occurs exactly twice.
    eta_square = None
    if start % 2 == 0:
        square_coefficient = eta_zeta.copy()
        square_coefficient[2::2] -= 2 * eta_zeta[1:maximum // 2 + 1]
        square_prefix = np.r_[0j, np.cumsum(square_coefficient[1:] * powers)]
        square_prefix = np.r_[square_prefix, square_prefix[-1]]
        square_kernel = product_powers * averaged_divided_prefix(square_prefix, start, products)
        half_kernel = product_powers * averaged_divided_prefix(convolution_prefix, start // 2, products)
        dyadic = 2 * np.exp(-s * np.log(2))
        check_close(square_kernel, kernel - dyadic * half_kernel, 'second eta dyadic matrix')
        low_half = np.sum(moebius * np.exp(-s * np.log(active)) *
                          averaged_divided_prefix(eta_prefix, start // 2, active))
        square_value = moebius @ square_kernel @ moebius
        check_close(square_value, 2 * (low - dyadic * low_half) - source ** 2,
                    'second eta whole source identity')
        square_analytic = source ** 2 * (euler * zeta) ** 2 * product_powers
        square_remainder = square_kernel - square_analytic
        square_projected = (square_remainder / source ** 2).real
        square_eigenvalues = np.linalg.eigvalsh(square_projected)
        square_diagonal = float(np.sum(moebius ** 2 * np.diag(square_projected)))
        square_projected_value = float(moebius @ square_projected @ moebius)
        inverse_defect_square = (1 - euler * zeta * complex_prefix) ** 2
        linear_tail_error = (2 * (low - dyadic * low_half
                                 - source ** 2 * euler * zeta * complex_prefix) / source ** 2)
        check_close((moebius @ square_remainder @ moebius) / source ** 2,
                    -inverse_defect_square + linear_tail_error,
                    'literal inverse-prefix defect square')
        eta_square = dict(
            quadratic_over_source_square=pair(square_value / source ** 2),
            remainder_over_source_square=pair((moebius @ square_remainder @ moebius) / source ** 2),
            projected_diagonal=square_diagonal,
            projected_cross=square_projected_value - square_diagonal,
            projected_min_eigenvalue=float(square_eigenvalues[0]),
            projected_max_eigenvalue=float(square_eigenvalues[-1]),
            projected_operator_bound=float(max(abs(square_eigenvalues[0]), abs(square_eigenvalues[-1])))
                                     * float(np.sum(moebius ** 2)),
            inverse_prefix_defect_square=pair(inverse_defect_square),
            linear_tail_error=pair(linear_tail_error),
        )
    # Independent direct floor enumeration validates selected matrix entries.
    for i, j in [(0, 0), (0, len(active) - 1), (len(active) - 1, len(active) - 1)]:
        k = int(products[i, j])
        direct = np.exp(-s * np.log(k)) * np.mean(convolution_prefix[physical // k])
        check_close(kernel[i, j], direct, 'direct physical matrix entry')
    return dict(
        u=u, physical_start=start, short_cutoff=upper, active_factors=len(active),
        zero_index=zero_index, sigma=sigma, threshold=threshold,
        sampled_s=pair(s), zeta_abs=float(abs(zeta)),
        all_integer_coefficients_checked=maximum,
        quadratic_over_source=pair(quadratic / source),
        low_over_source=pair(low / source),
        pole_over_source=pair(pole_value / source),
        analytic_over_source=pair(analytic_value / source),
        remainder_over_source=pair(remainder_value / source),
        projected_diagonal=float(diagonal), projected_cross=float(value - diagonal),
        projected_min_eigenvalue=float(eigenvalues[0]),
        projected_max_eigenvalue=float(eigenvalues[-1]),
        projected_operator_bound=float(max(abs(eigenvalues[0]), abs(eigenvalues[-1])))
                                 * float(np.sum(moebius ** 2)),
        eta_square=eta_square,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scales', nargs='+', type=positive_integer, default=[4, 8, 12, 16])
    parser.add_argument('--zeros', nargs='+', type=positive_integer, default=[1, 2])
    parser.add_argument('--sigmas', nargs='+', type=float, default=[0.5, 0.75])
    parser.add_argument('--thresholds', nargs='+', type=positive_integer, default=[1, 3, 7])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if min(args.scales) < 2:
        parser.error('Scales must be at least two')
    if any(not 0 < s < 1 for s in args.sigmas):
        parser.error('Real parts must lie strictly between zero and one')
    mp.mp.dps = 50
    records = []
    for u in args.scales:
        for index in args.zeros:
            for sigma in args.sigmas:
                for threshold in args.thresholds:
                    record = probe(u, index, sigma, threshold)
                    records.append(record)
                    print(json.dumps(record, allow_nan=False), flush=True)
    if args.output:
        args.output.write_text(json.dumps(dict(
            status='floating-point exploration; no theorem or zero bound',
            off_critical_samples_are_not_zeta_zeros=True,
            no_matrix_positivity_or_arithmetic_decay_assumed=True,
            versions=dict(numpy=np.__version__, mpmath=mp.__version__, sympy=sympy.__version__),
            records=records,
        ), indent=2, allow_nan=False) + '\n')


if __name__ == '__main__':
    main()

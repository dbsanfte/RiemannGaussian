#!/usr/bin/env python3
"""Optional finite arithmetic probe of the all-count Riesz second moment.

This uses the actual integer Mobius coefficients and Euler totients, with
floating logarithms and arithmetic. It is not a certificate, a prime-density
model, or a bound for the source-normalized masked Riesz carrier. It is never
part of the ordinary build or exhaustive certificate workflow.
"""
import argparse
import json
import math

import numpy as np


def arithmetic(limit):
    prime = np.ones(limit + 1, dtype=bool)
    prime[:2] = False
    mu = np.ones(limit + 1, dtype=np.int8)
    mu[0] = 0
    phi = np.arange(limit + 1, dtype=np.int64)
    for p in range(2, limit + 1):
        if not prime[p]:
            continue
        prime[2*p::p] = False
        mu[p::p] *= -1
        phi[p::p] -= phi[p::p] // p
        if p*p <= limit:
            mu[p*p::p*p] = 0
    return mu, phi


def diagonal(weights, phi):
    reciprocal = np.zeros_like(weights)
    reciprocal[1:] = weights[1:] / np.arange(1, len(weights))
    return float(sum(phi[g] * float(reciprocal[g::g].sum())**2
                     for g in range(1, len(weights))))


def row(r, half_period):
    mu, phi = arithmetic(r)
    logs = np.zeros(r + 1)
    logs[1:] = np.log(r / np.arange(1, r + 1, dtype=float))
    weights = mu * logs
    logarithmic = diagonal(weights, phi)
    sharp = diagonal(mu.astype(float), phi)
    # Keep the exact two-cutoff signed difference before squaring.
    difference = diagonal(mu * np.minimum(logs, half_period), phi)
    length = min(4*r*r, 1_000_000)
    response = np.zeros(length + 1)
    sharp_response = np.zeros(length + 1, dtype=np.int32)
    difference_response = np.zeros(length + 1)
    difference_weights = mu * np.minimum(logs, half_period)
    for d in range(1, r + 1):
        response[d::d] += weights[d]
        sharp_response[d::d] += int(mu[d])
        difference_response[d::d] += difference_weights[d]
    actual = float(np.dot(response[1:], response[1:]))
    # These retain the finite counting floors, including when r^2 > X.
    sharp_actual = int(np.dot(sharp_response[1:].astype(np.int64),
                              sharp_response[1:].astype(np.int64)))
    difference_actual = float(np.dot(difference_response[1:], difference_response[1:]))
    return {
        "cutoff": r,
        "logarithmic_quadratic": logarithmic,
        "quadratic_over_log_cutoff": logarithmic / math.log(r),
        "proved_quadratic_upper_evaluated": 196 * (1 + math.log(r)),
        "sharp_slope_quadratic": sharp,
        "two_cutoff_difference_quadratic": difference,
        "difference_over_half_period_squared": difference / half_period**2,
        "coefficient_mass_over_cutoff": float(np.abs(weights).sum()) / r,
        "population_length": length,
        "literal_integer_second_moment": actual,
        "literal_sharp_second_moment_over_X": sharp_actual / length,
        "literal_difference_second_moment_over_X_h_squared":
            difference_actual / (length * half_period**2),
        "second_moment_over_X_log_cutoff": actual / (length * math.log(r)),
        "proved_second_moment_upper_evaluated":
            196 * length * (1 + math.log(r)) + 16 * r*r,
        "cutoff_squared_at_most_population": r*r <= length,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cutoffs", nargs="+", type=int,
                        default=[32, 100, 320, 1000, 3200, 10000, 32000])
    parser.add_argument("--height", type=float, default=54.)
    args = parser.parse_args()
    if min(args.cutoffs) < 2 or args.height == 0:
        parser.error("Cutoffs must be at least two and height must be nonzero")
    h = math.pi / abs(args.height)
    print(json.dumps({"scope": __doc__.strip(), "half_period": h,
                      "rows": [row(r, h) for r in args.cutoffs]}, indent=2))


if __name__ == "__main__":
    main()

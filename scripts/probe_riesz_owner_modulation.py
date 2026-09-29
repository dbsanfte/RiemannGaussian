#!/usr/bin/env python3
"""Optional allocation-only diagnostic for joint radial coefficient variation.

Retains the exact unpaid factorial orders and the radial kernel, sampled at
prime half periods. This does not compute a prime sum or any changing physical
prime mask. Sampled variation is not a certified upper bound. No source-scale
or zero-free claim follows, and ordinary CI does not run this probe.
"""

import argparse
import json
import math

import numpy as np
from scipy.stats import binom


def probe(order, height, samples):
    n = order
    unpaid = [k for k in range(n + 2)
              if n + 1 < 8 * k < 7 * (n + 1) and 32 * k <= 15 * n + 64
              and not 13 * n // 32 + 1 <= k <= (15 * n + 64) // 32
              and not 4 * n <= 5 * (n + 1 - k)]
    # Check the literal definitions at every probed order. Lean independently
    # proves this equality in ZetaRieszOwnerMaximal.unpaidOrders_eq.
    assert unpaid == list(range(n // 5 + 2, 13 * n // 32 + 1))
    half_period = math.pi / abs(height)
    periods = np.arange(math.floor(1.95 * n / half_period) + 1,
                        math.floor(2.03 * n / half_period) + 1)
    totals = periods * half_period
    log_weight = -(totals - 2 * n) / 2 + (n + 1) * np.log(totals / (2 * n))
    radial = np.exp(log_weight - log_weight.max())
    radial_norm = float(np.linalg.norm(radial))
    previous = None
    variation = 0.
    max_norm = 0.
    max_period_variation = 0.
    max_abel_budget = 0.
    for cofactor_log in np.linspace(0., 1.3 * n, samples):
        share = cofactor_log / totals
        allocated = (binom.cdf(unpaid[-1], n + 1, share)
                     - binom.cdf(unpaid[0] - 1, n + 1, share))
        owner = 1 - allocated
        period_variation = float(np.abs(np.diff(owner)).sum())
        max_period_variation = max(max_period_variation, period_variation)
        max_abel_budget = max(max_abel_budget, abs(float(owner[-1])) + period_variation)
        # The alternating sign of each fixed period leaves these vector
        # norms unchanged. It is not replaced by an absolute prime phase.
        vector = (-1.)**periods * radial * owner
        max_norm = max(max_norm, float(np.linalg.norm(vector)))
        if previous is not None:
            variation += float(np.linalg.norm(vector - previous))
        previous = vector
    return {
        "N": n,
        "height": height,
        "periods": len(periods),
        "unpaidOrders": [unpaid[0], unpaid[-1]],
        "cofactorLogOverNInterval": [0., 1.3],
        "samples": samples,
        "sampledVectorVariation": variation,
        "radialCoefficientNorm": radial_norm,
        "sampledVariationOverRadialNorm": variation / radial_norm,
        "maximumVectorNormOverRadialNorm": max_norm / radial_norm,
        "maximumSampledPeriodVariation": max_period_variation,
        "maximumSampledAbelBudget": max_abel_budget,
        "provedUniversalPeriodVariationBound": 2.,
        "provedUniversalAbelBudget": 3.,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", nargs="+", type=int,
                        default=[256, 640, 1536, 4096, 8192])
    parser.add_argument("--height", type=float, default=54.)
    parser.add_argument("--samples", type=int, default=2001)
    args = parser.parse_args()
    if min(args.orders) < 32 or args.height == 0 or args.samples < 2:
        parser.error("Orders must be at least 32, height nonzero, and samples at least two")
    print(json.dumps({"scope": __doc__.strip(),
                      "rows": [probe(n, args.height, args.samples) for n in args.orders]}, indent=2))


if __name__ == "__main__":
    main()

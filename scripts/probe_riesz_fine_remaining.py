#!/usr/bin/env python3
"""Optional actual-integer probe of the signed rest after the two new payments.

Reuse the existing transcription of the original core, physical primes,
moving length, owner allocation and factorial kernel. Factor uniformly
sampled integer labels; never generate labels from a prime-density model.
Keep the unit incidence and all nonunit incidences with their common phase.

Monte Carlo, floating endpoints and the Python mask transcription are not
certificates. These small orders are not the cofinal schedule and usually
fail the eventual length hypothesis. A covariance is evidence for a next
experiment, not an independently proved source-scale floor.
"""

import argparse
from collections import Counter, defaultdict
import json
import math
import random
import time

import numpy as np
from sympy import factorint, isprime

from probe_riesz_canonical_joint import (
    allocation, core_mask, parameters, subset_rows,
)


CHANNELS = (
    "owned_core", "paid_large_owner", "paid_fine_closed", "remaining",
    "unit_remaining", "nonunit_remaining", "small_nonunit",
    "saturation_boundary", "outer_log_boundary", "other_boundary",
)


def incidence_channels(n, label, factors, pars, ceiling):
    mask = core_mask(n, label, factors, pars, ceiling)
    if mask != "core":
        return np.zeros(len(CHANNELS)), mask, 0.0
    primes = sorted(factors)
    p = primes[-1]
    a = label // p
    total = math.log(label)
    owner_log = math.log(p)
    eligible_owner = n * n < p < pars["physical"]
    owned = 1.0 - (allocation(n, pars["orders"], 1-owner_log/total)
                   if eligible_owner else 0.0)
    amplitude = math.exp(
        (n+1)*math.log(10001/20000) - 1.5*total
        + (n+1)*math.log(total) - math.lgamma(n+1)
    ) / pars["length"] * owned
    vals = np.zeros(len(CHANNELS))
    cofactor = {q: 1 for q in primes[:-1]}
    for b, _count, sign in subset_rows(cofactor):
        d = a // b
        outer_log = owner_log + math.log(b)
        hinge = max(outer_log-pars["length"], 0.0) - max(
            math.log(b)-pars["length"], 0.0)
        contribution = sign * hinge
        vals[0] += contribution
        if owner_log >= 1.215*n:
            vals[1] += contribution
            continue
        eligible_fine = (
            eligible_owner and b > 1 and hinge != 0.0
            and outer_log <= 1.949*n
            and 2.03*n <= owner_log+pars["length"]
        )
        if eligible_fine:
            lower = math.ceil(math.exp(1.95*n-outer_log))
            upper = math.floor(math.exp(2.03*n-outer_log))
            if lower <= d <= upper:
                vals[2] += contribution
                continue
        vals[3] += contribution
        if d == 1:
            vals[4] += contribution
            continue
        vals[5] += contribution
        if math.log(d) < n/1000:
            vals[6] += contribution
        elif owner_log+pars["length"] < 2.03*n:
            vals[7] += contribution
        elif outer_log > 1.949*n:
            vals[8] += contribution
        else:
            vals[9] += contribution
    # Independent divisor computation checks the exact outer sign convention.
    riesz = sum(sign*max(pars["length"]-math.log(b), 0.0)
                for b, _, sign in subset_rows(factors))
    error = max(
        abs(vals[0]+riesz),
        abs(vals[0]-vals[1]-vals[2]-vals[3]),
        abs(vals[3]-vals[4]-vals[5]),
        abs(vals[5]-sum(vals[6:])),
    )
    assert error <= 1e-8*max(1.0, abs(riesz), float(np.max(abs(vals))))
    return vals*amplitude, mask, error


def run(n, seed, samples, bins, heights, ceiling):
    start = time.monotonic()
    pars = parameters(n, bins)
    sums = np.zeros((len(heights), len(CHANNELS)))
    squares = np.zeros((len(heights), len(CHANNELS), len(CHANNELS)))
    masks, counts = Counter(), Counter()
    count_sums = defaultdict(lambda: np.zeros_like(sums))
    error = 0.0
    for i in range(samples):
        rng = random.Random((seed << 48)+(n << 32)+i)
        cell = rng.randrange(bins)
        low, high = pars["edges"][cell:cell+2]
        label = rng.randrange(low+1, high+1)
        factors = {int(p): int(e) for p, e in factorint(label).items()}
        assert math.prod(p**e for p, e in factors.items()) == label
        assert all(isprime(p) for p in factors)
        vals, mask, atom_error = incidence_channels(n, label, factors, pars, ceiling)
        phase = np.cos(np.asarray(heights)*math.log(label))
        row = phase[:, None]*vals[None, :]*bins*(high-low)
        sums += row
        squares += np.einsum("hi,hj->hij", row, row)
        masks[mask] += 1
        error = max(error, atom_error)
        if mask == "core":
            counts[len(factors)] += 1
            count_sums[len(factors)] += row
    means = sums/samples
    covariance = (squares-samples*np.einsum("hi,hj->hij", means, means))/(samples-1)
    diagnostics = {}
    for i, y in enumerate(heights):
        var_unit, var_nonunit = covariance[i, 4, 4], covariance[i, 5, 5]
        denom = math.sqrt(max(0.0, var_unit*var_nonunit))
        diagnostics[str(y)] = {
            "sourceNormalizedEstimates": dict(zip(CHANNELS, means[i].tolist())),
            "diagnosticStandardErrors": dict(zip(CHANNELS, np.sqrt(
                np.maximum(covariance[i].diagonal(), 0.0)/samples).tolist())),
            "unitNonunitCovariance": float(covariance[i, 4, 5]),
            "unitNonunitCorrelation": float(covariance[i, 4, 5])/denom if denom else None,
            "signedRestByCount": {
                str(k): dict(zip(CHANNELS, (count_sums[k][i]/samples).tolist()))
                for k in sorted(counts)
            },
        }
    return {
        "N": n, "seed": seed, "samples": samples,
        "seconds": time.monotonic()-start,
        "movingLength": pars["length"],
        "eventualLengthHypothesisMet": pars["length"] >= 11*n/8,
        "cofinalScheduleTested": False,
        "literalCountCeilingTranscription": ceiling,
        "coreMasks": dict(masks), "coreCounts": dict(counts),
        "floatingDivisorLedgerMaximumError": error,
        "heights": diagnostics,
        "floorCertified": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="+", default=[16, 20])
    parser.add_argument("--seeds", type=int, nargs="+", default=[0, 1])
    parser.add_argument("--samples", type=int, default=512)
    parser.add_argument("--bins", type=int, default=32)
    parser.add_argument("--heights", type=float, nargs="+", default=[54.0, 60.0, 100.0])
    parser.add_argument("--count-ceiling", type=int, default=64)
    args = parser.parse_args()
    if min(args.orders) < 16 or args.samples < 2 or args.bins < 1:
        parser.error("orders>=16, samples>=2 and bins>=1 required")
    for n in args.orders:
        for seed in args.seeds:
            print(json.dumps({"scope": __doc__, "result": run(
                n, seed, args.samples, args.bins, args.heights, args.count_ceiling)}), flush=True)

#!/usr/bin/env python3
"""Optional actual-integer diagnostic for the joined literal signed payments.

Sample and factor integer labels in the original total-log window. Retain
the original core, physical primes, owner allocation, moving length,
factorial weight and common complex phase. The new selection is exactly
the prior closed cones and the OwnerGapRows population, not merely d < p.

Floating endpoints, sampled labels and the Python mask transcription are
not certificates. Small orders need not satisfy the eventual length bound
and are not the cofinal schedule. All counts are joined before reporting
signed contributions. No phase cancellation or floor is inferred.
"""

import argparse
from collections import Counter
import json
import math
import random
import time

import numpy as np
import mpmath as mp
from sympy import factorint, isprime, nextprime

from probe_riesz_canonical_joint import allocation, core_mask, parameters, subset_rows


CHANNELS = (
    "owned_core", "paid_large_owner", "paid_fine_closed",
    "paid_owner_safe_closed", "paid_edge_closed", "paid_low_owner_closed",
    "paid_owner_gap_additional", "remaining", "unit_remaining", "nonunit_remaining",
)


def in_closed_row(n, outer_log, d):
    """Transcribe the same ceil/floor row, with large-integer fallback.

    Higher precision prevents floating overflow in the deterministic large
    label probes. The input logarithm is still numerical, not an enclosure.
    """
    lo, hi = 39*n/20-outer_log, 203*n/100-outer_log
    if hi < 700:
        return math.ceil(math.exp(lo)) <= d <= math.floor(math.exp(hi))
    with mp.workdps(max(80, int(max(lo, hi)/math.log(10))+32)):
        return int(mp.ceil(mp.exp(lo))) <= d <= int(mp.floor(mp.exp(hi)))


def incidence_channels(n, label, factors, pars, count_ceiling):
    mask = core_mask(n, label, factors, pars, count_ceiling)
    if mask != "core":
        return np.zeros(len(CHANNELS)), mask, 0.0, 0
    p = max(factors)
    a = label // p
    total, owner_log = math.log(label), math.log(p)
    eligible_owner = n*n < p < pars["physical"]
    allocated = allocation(n, pars["orders"], 1-owner_log/total) if eligible_owner else 0.0
    amplitude = (1-allocated)*math.exp(
        (n+1)*math.log(10001/20000) - 1.5*total
        + (n+1)*math.log(total) - math.lgamma(n+1)
    )/pars["length"]
    vals, new_incidences = np.zeros(len(CHANNELS)), Counter()
    for b, _, sign in subset_rows({q: 1 for q in factors if q != p}):
        d = a // b
        outer_log = owner_log+math.log(b)
        hinge = max(outer_log-pars["length"], 0.0)-max(math.log(b)-pars["length"], 0.0)
        contribution = sign*hinge
        vals[0] += contribution
        if owner_log >= 243*n/200:
            vals[1] += contribution
            continue
        common = (eligible_owner and b > 1 and hinge != 0.0 and outer_log <= 1949*n/1000)
        old = new = edge = low_owner = False
        if common:
            selected_row = in_closed_row(n, outer_log, d)
            old = selected_row and 203*n/100 <= owner_log+pars["length"]
            new = (selected_row and owner_log+pars["length"] < 203*n/100
                   and n/2 <= owner_log and 31*n/20 < outer_log)
        if (eligible_owner and b > 1 and hinge != 0.0
                and 1949*n/1000 < outer_log <= 3899*n/2000
                and n/2 <= owner_log and 31*n/20 < outer_log):
            edge = in_closed_row(n, outer_log, d)
        if (eligible_owner and b > 1 and hinge != 0.0
                and outer_log <= 3899*n/2000
                and owner_log+pars["length"] < 203*n/100
                and 7*n/25 <= owner_log < n/2 and 7*n/4 < outer_log):
            low_owner = in_closed_row(n, outer_log, d)
        owner_gap = (eligible_owner and b > 1 and hinge != 0.0
                     and outer_log <= 3899*n/2000
                     and 203*n/100 < outer_log+owner_log
                     and in_closed_row(n, outer_log, d))
        assert sum((old, new, edge, low_owner)) <= 1
        assert not any((old, new, edge, low_owner)) or owner_gap
        if old:
            vals[2] += contribution
        elif new:
            assert d < p
            vals[3] += contribution
            new_incidences["owner_safe"] += 1
        elif edge:
            assert d < p and d > 1
            vals[4] += contribution
            new_incidences["edge"] += 1
        elif low_owner:
            assert 1 < d < p and len(factors) >= 5
            vals[5] += contribution
            new_incidences["low_owner"] += 1
        elif owner_gap:
            assert 1 < d < p
            vals[6] += contribution
            new_incidences["owner_gap_additional"] += 1
        else:
            vals[7] += contribution
            vals[8 if d == 1 else 9] += contribution
    riesz = sum(sign*max(pars["length"]-math.log(b), 0.0)
                for b, _, sign in subset_rows(factors))
    error = max(abs(vals[0]+riesz), abs(vals[0]-sum(vals[1:8])),
                abs(vals[7]-vals[8]-vals[9]))
    assert error < 1e-8*max(1.0, abs(riesz), float(np.max(np.abs(vals))))
    return vals*amplitude, mask, error, new_incidences


def deterministic_low_owner_label(n, family="low_owner"):
    """An actual-integer diagnostic of the new, previously unselected cone.

    This is not population sampling or a Lean/nonemptiness certificate.
    SymPy primality and high-precision floating logarithms remain exploratory.
    At N=1536 the separate eventual moving-length inequality is met.
    """
    start = time.monotonic()
    with mp.workdps(max(80, int(.4*n/math.log(10))+40)):
        shares = ((.4, .345, .346, .347, .348, .214) if family == "low_owner"
                  else (.55, .52, .49, .44))
        primes = [int(nextprime(int(mp.exp(mp.mpf(str(x))*n)))) for x in shares]
    assert len(set(primes)) == len(shares) and all(isprime(p) for p in primes)
    label, factors = math.prod(primes), dict.fromkeys(primes, 1)
    cutoff = 20000**n // (10001**n*(n+1))
    physical = (cutoff+2)**2
    u = 10001/20000
    tilt = 1/(-2*math.log(u))
    log_rate = (2-2*tilt)*math.log(u)-math.log(tilt)
    with mp.workdps(80):
        trial = min(int(mp.exp(-n*log_rate/(2*(tilt+2.5)))), cutoff+1)
    from probe_riesz_fixed_count_period import unpaid_orders
    pars = dict(length=math.log(physical), physical=physical, trial=trial,
                orders=unpaid_orders(n).tolist())
    _values, mask, error, selected = incidence_channels(n, label, factors, pars, 64)
    p = max(primes)
    d = min(primes) if family == "low_owner" else primes[2]
    b = label//(p*d)
    selected_name = "low_owner" if family == "low_owner" else "owner_gap_additional"
    assert mask == "core" and selected.get(selected_name, 0) > 0
    return {
        "N": n, "family": family, "seconds": time.monotonic()-start,
        "labelDigits": len(str(label)), "coreMaskTranscription": mask,
        "count": len(primes), "normalizedLogLabel": math.log(label)/n,
        "normalizedOwnerLog": math.log(p)/n,
        "normalizedOuterLog": math.log(p*b)/n,
        "normalizedUnsignedLog": math.log(d)/n,
        "movingLengthRatio": pars["length"]/n,
        "eventualLengthHypothesisMet": pars["length"] >= 11*n/8,
        "selectedIncidences": dict(selected),
        "floatingDivisorLedgerMaximumError": error,
        "cofinalScheduleTested": False, "nonemptinessCertified": False,
        "floorCertified": False,
    }


def run(n, seed, samples, bins, heights, count_ceiling):
    start = time.monotonic()
    pars = parameters(n, bins)
    sums = np.zeros((len(heights), len(CHANNELS)), dtype=complex)
    squares = np.zeros((len(heights), len(CHANNELS)))
    paired = np.zeros((len(heights), 2, 2))
    masks, counts, new_counts = Counter(), Counter(), Counter()
    max_error, incidences = 0.0, Counter()
    for i in range(samples):
        rng = random.Random((seed << 48)+(n << 32)+i)
        cell = rng.randrange(bins)
        low, high = pars["edges"][cell:cell+2]
        label = rng.randrange(low+1, high+1)
        factors = {int(p): int(e) for p, e in factorint(label).items()}
        assert math.prod(p**e for p, e in factors.items()) == label
        assert all(isprime(p) for p in factors)
        vals, mask, error, selected = incidence_channels(n, label, factors, pars, count_ceiling)
        row = np.exp(-1j*np.asarray(heights)*math.log(label))[:, None]*vals[None, :]*bins*(high-low)
        sums += row
        squares += row.real**2
        pair = row.real[:, -2:]
        paired += np.einsum("hi,hj->hij", pair, pair)
        masks[mask] += 1
        max_error = max(max_error, error)
        if mask == "core":
            counts[len(factors)] += 1
        if selected:
            incidences.update(selected)
            new_counts[len(factors)] += 1
    means = sums/samples
    standard_errors = np.sqrt(np.maximum(
        (squares-samples*means.real**2)/(samples-1)/samples, 0.0))
    covariance = (paired-samples*np.einsum("hi,hj->hij", means.real[:, -2:],
                                         means.real[:, -2:]))/(samples-1)
    return {
        "N": n, "seed": seed, "samples": samples,
        "seconds": time.monotonic()-start, "movingLength": pars["length"],
        "eventualLengthHypothesisMet": pars["length"] >= 11*n/8,
        "cofinalScheduleTested": False, "literalCountCeilingTranscription": count_ceiling,
        "coreMasks": dict(masks), "coreCounts": dict(counts),
        "newSelectedLabelCounts": dict(new_counts), "newSelectedIncidences": dict(incidences),
        "floatingDivisorLedgerMaximumError": max_error,
        "heights": {str(y): {
            "sourceNormalizedRealEstimates": dict(zip(CHANNELS, means[i].real.tolist())),
            "sourceNormalizedImaginaryEstimates": dict(zip(CHANNELS, means[i].imag.tolist())),
            "diagnosticRealStandardErrors": dict(zip(CHANNELS, standard_errors[i].tolist())),
            "diagnosticUnitNonunitCovariance": float(covariance[i, 0, 1]),
            "diagnosticUnitNonunitCorrelation": (
                float(covariance[i, 0, 1]/math.sqrt(max(0.0,
                    covariance[i, 0, 0]*covariance[i, 1, 1])))
                if covariance[i, 0, 0]*covariance[i, 1, 1] > 0.0 else None),
        } for i, y in enumerate(heights)},
        "floorCertified": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="+", default=[20, 24])
    parser.add_argument("--seeds", type=int, nargs="+", default=[0, 1])
    parser.add_argument("--samples", type=int, default=512)
    parser.add_argument("--bins", type=int, default=32)
    parser.add_argument("--heights", type=float, nargs="+", default=[54.0, 60.0, 100.0])
    parser.add_argument("--count-ceiling", type=int, default=64)
    parser.add_argument("--witness-orders", type=int, nargs="*", default=[])
    parser.add_argument("--owner-gap-witness-orders", type=int, nargs="*", default=[])
    args = parser.parse_args()
    if min(args.orders) < 16 or args.samples < 2 or args.bins < 1:
        parser.error("orders>=16, samples>=2 and bins>=1 required")
    for n in args.witness_orders:
        print(json.dumps({"scope": __doc__, "deterministicLowOwnerLabel":
                          deterministic_low_owner_label(n)}), flush=True)
    for n in args.owner_gap_witness_orders:
        print(json.dumps({"scope": __doc__, "deterministicOwnerGapLabel":
                          deterministic_low_owner_label(n, "owner_gap")}), flush=True)
    for n in args.orders:
        for seed in args.seeds:
            print(json.dumps({"scope": __doc__, "result": run(n, seed, args.samples,
                args.bins, args.heights, args.count_ceiling)}), flush=True)

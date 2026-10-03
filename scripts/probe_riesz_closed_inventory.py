#!/usr/bin/env python3
"""Optional closed-inventory probe for the literal signed Riesz floor.

Enumerate every subset of ONE union of two disjoint eight-prime pools,
including the mixed products omitted by the earlier two-pool diagnostics.
Keep the original core masks, full factorial allocation and complex phase.
Join all labels/counts/owner shares inside each complete cutoff period
before clipping its net contribution. No profile coefficient is fitted.

Probable primes, floating logarithms/phases and interpolated large period
edges are not certified. The finite inventory is not the native population
or a density sample. Early orders use the original count ceiling K, not
the eventual K/864 crop. No cofinal saving, floor or zero exclusion follows.
This script is outside builds/CI.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
import math
from pathlib import Path
import random
import subprocess
import sys
import time

sys.dont_write_bytecode = True

import mpmath as mp
import numpy as np
from scipy.stats import binom
from sympy import isprime, nextprime

from probe_riesz_canonical_joint import core_mask
from probe_riesz_complex_null_profiles import period_edge
from probe_riesz_fixed_count_period import unpaid_orders


LEVELS = (.03, .05, .095, .17, .25, .43, .86, 1.10)
OWNER_EDGES = (.4, .525, .565, .594)
COUNT_CEILINGS = {256: 8, 640: 16}


def parameters(order):
    cutoff = 20000**order // (10001**order*(order+1))
    physical = (cutoff+2)**2
    u = mp.mpf(10001)/20000
    tilt = 1/(-2*mp.log(u))
    rate = (2-2*tilt)*mp.log(u)-mp.log(tilt)
    trial = min(int(mp.exp(-order*rate/(2*(tilt+mp.mpf('2.5'))))), cutoff+1)
    orders = unpaid_orders(order)
    assert len(orders) and np.all(np.diff(orders) == 1)
    return dict(N=order, physical=physical, length=math.log(physical),
                trial=trial, orders=orders.tolist())


def population(order, seed):
    pars, rng = parameters(order), random.Random(seed)
    primes = [int(nextprime(int(mp.exp(mp.mpf(str(order*(x+rng.uniform(-.0015, .0015))))))))
              for _ in range(2) for x in LEVELS]
    assert len(primes) == len(set(primes)) == 16 and all(isprime(p) for p in primes)
    products = [1]
    for p in primes:
        products += [p*n for n in products]
    logs = [math.log(n) for n in products]
    rows, excluded = [], Counter()
    for mask in range(1, len(products)):
        factors = [p for i, p in enumerate(primes) if mask >> i & 1]
        label, total = products[mask], logs[mask]
        status = core_mask(order, label, dict.fromkeys(factors, 1), pars,
                           COUNT_CEILINGS[order])
        if status != 'core':
            excluded[status] += 1
            continue
        shares = [1-math.log(p)/total for p in factors if order**2 < p < pars['physical']]
        assigned = float(np.sum(binom.cdf(pars['orders'][-1], order+1, shares)
                              -binom.cdf(pars['orders'][0]-1, order+1, shares)))
        assert -1e-8 <= assigned <= 1+1e-8
        unassigned = max(1-assigned, 0.)
        if not unassigned:
            excluded['floating_zero_unassigned'] += 1
            continue
        log_amplitude = ((order+1)*math.log(10001/20000)-1.5*total
            +(order+1)*math.log(total)-math.lgamma(order+1)-math.log(pars['length'])
            +math.log(unassigned))
        cohort = 0 if mask < 256 else 1 if mask & 255 == 0 else 2
        owner_share = math.log(max(factors))/total
        rows.append(dict(mask=mask, label=label, total=total, count=len(factors),
            cohort=cohort, ownerShare=owner_share, log_amplitude=log_amplitude))
    assert rows and any(row['cohort'] == 2 for row in rows)
    return pars, products, logs, primes, rows, excluded


def subset_masks(mask):
    """All divisors, including the empty divisor and whole label."""
    sub = mask
    while True:
        yield sub
        if not sub:
            break
        sub = (sub-1) & mask


def experiment(order, seed, heights):
    started = time.monotonic()
    pars, products, logs, primes, rows, excluded = population(order, seed)
    counts = sorted({row['count'] for row in rows})
    count_index = {count: i for i, count in enumerate(counts)}
    owner_start = 4+len(counts)
    channels = owner_start+5
    scale = max(row['log_amplitude'] for row in rows)
    weights = -np.exp([row['log_amplitude']-scale for row in rows])[None, :]*np.exp(
        -1j*np.asarray(heights)[:, None]*np.asarray([row['total'] for row in rows])[None, :])
    endpoint = max(row['label'] for row in rows)
    events = defaultdict(lambda: np.zeros((len(heights), channels), dtype=complex))
    literal = np.zeros(len(heights), dtype=complex)
    owner_counts, cohort_counts = Counter(), Counter()
    for i, row in enumerate(rows):
        bucket = int(np.searchsorted(OWNER_EDGES, row['ownerShare'], side='right'))
        axes = [0, 1+row['cohort'], 4+count_index[row['count']], owner_start+bucket]
        owner_counts[bucket] += 1
        cohort_counts[row['cohort']] += 1
        response = []
        for sub in subset_masks(row['mask']):
            divisor, sign = products[sub], (-1)**sub.bit_count()
            if divisor < pars['physical']:
                response.append(sign*(pars['length']-logs[sub]))
            if divisor < endpoint:
                events[divisor][:, axes] += sign*weights[:, i, None]
        literal += weights[:, i]*math.fsum(response)
    points = sorted({1, pars['physical'], endpoint, *events})
    prefix = np.zeros((len(heights), channels), dtype=complex)
    grouped = [defaultdict(lambda: np.zeros(channels, dtype=complex)) for _ in heights]
    for left, right in zip(points, points[1:]):
        prefix += events.get(left, 0)
        # The unit-log corrected profile is EXACTLY flat below the hinge.
        if left < pars['physical']:
            continue
        lo, hi = math.log(left), math.log(right)
        for ih, height in enumerate(heights):
            unit = 2*math.pi/height
            cursor, period = lo, math.floor(lo/unit)
            while cursor < hi:
                edge = min(hi, period_edge(period, unit))
                if edge <= cursor:
                    period += 1
                    continue
                grouped[ih][period] -= prefix[ih]*(edge-cursor)
                cursor, period = edge, period+1
    cases = []
    for ih, height in enumerate(heights):
        data = np.asarray([grouped[ih][key].real for key in sorted(grouped[ih])])
        all_periods = data[:, 0]
        total = float(all_periods.sum())
        tolerance = 1e-7*max(1., float(np.abs(all_periods).sum()))
        assert abs(total-literal[ih].real) <= tolerance
        for axis in (data[:, 1:4], data[:, 4:owner_start], data[:, owner_start:]):
            assert np.max(np.abs(axis.sum(axis=1)-all_periods)) <= tolerance
        def price(a):
            return float(np.maximum(-a, 0).sum())
        joint_cost = price(all_periods)
        split_count = price(data[:, 4:owner_start])
        split_owner = price(data[:, owner_start:])
        split_cohort = price(data[:, 1:4])
        assert joint_cost <= min(split_count, split_owner, split_cohort)+tolerance
        old_cost = price(data[:, 1]+data[:, 2])
        cases.append(dict(height=height, allCountsJoined=True, periods=len(data),
            wholeSignedReal=total, wholeSignedImaginary=float(literal[ih].imag),
            joinedPeriodCost=joint_cost, splitCountCost=split_count,
            splitOwnerCost=split_owner, splitCohortCost=split_cohort,
            oldPurePoolsCost=old_cost, addedMixedPoolsCost=price(data[:, 3]),
            netCountCancellation=split_count-joint_cost,
            netOwnerCancellation=split_owner-joint_cost,
            netCohortCancellation=split_cohort-joint_cost,
            countResidualFraction=joint_cost/split_count if split_count else None,
            ownerResidualFraction=joint_cost/split_owner if split_owner else None,
            mixedClosureReducesOldCost=joint_cost < old_cost,
            literalIdentityError=abs(total-literal[ih].real),
            nativePopulationOrFloorCertified=False))
    return dict(N=order, seed=seed, primes=[str(p) for p in primes],
        everyUnionSubsetEnumerated=True, mixedPoolLabelsRetained=True,
        selectedLabels=len(rows), cohortCounts=dict(cohort_counts),
        counts=counts, ownerShareBins=[0, *OWNER_EDGES, .65], ownerBinCounts=dict(owner_counts),
        minimumOwnerShare=min(row['ownerShare'] for row in rows),
        maximumOwnerShare=max(row['ownerShare'] for row in rows),
        originalCountCeiling=COUNT_CEILINGS[order], eventualCountCropApplied=False,
        sourceAmplitudeLogScale=scale, excluded=dict(excluded),
        seconds=time.monotonic()-started, cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, choices=sorted(COUNT_CEILINGS), default=[256, 640])
    parser.add_argument('--seeds', nargs='+', type=int, default=[317])
    parser.add_argument('--heights', nargs='+', type=float, default=[54., 65., 100.])
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-closed-inventory/report.json'))
    args = parser.parse_args()
    if any(not math.isfinite(y) or y < 54 for y in args.heights):
        parser.error('finite heights >=54 required')
    mp.mp.dps = 100
    report = dict(schemaVersion=1, baseHead=subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], text=True).strip(), sourceSHA256=hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest(), scope=dict(
            outsideBuildsCI=True, fixedOriginalUnitLogProfile=True,
            probablePrimesAndFloatingPhase=True, largeCutoffsLogInterpolated=True,
            factorialAllocationRetained=True, everyLiteralCoreMaskRetained=True,
            originalEarlyCountCeilingNotEventualCrop=True, commonAmplitudeRescaled=True,
            nativeInventoryCoverage=False, cofinalBound=False, floorClosed=False), batches=[])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for order in args.orders:
        for seed in args.seeds:
            batch = experiment(order, seed, args.heights)
            report['batches'].append(batch)
            args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
            print(json.dumps(dict(N=order, seed=seed, labels=batch['selectedLabels'],
                ownerShareRange=[batch['minimumOwnerShare'],batch['maximumOwnerShare']],
                countResidualFractions=[c['countResidualFraction'] for c in batch['cases']],
                mixedClosureReducesOldCost=[c['mixedClosureReducesOldCost'] for c in batch['cases']],
                seconds=batch['seconds']), allow_nan=False), flush=True)


if __name__ == '__main__':
    main()

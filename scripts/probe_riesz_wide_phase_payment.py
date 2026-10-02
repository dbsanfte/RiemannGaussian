#!/usr/bin/env python3
"""Optional finite audit of the wider paid phase family.

Reuse the complete constructed prime-universe populations, literal weights
and masks of probe_riesz_joined_count_correlation. Select adverse cutoffs
ONCE on the whole population. Integrate the same signed divisor Gram on
the old remaining family, its new wide phase subset, and its complement.

This uses probable primes, common amplitude rescaling and logarithmic
interpolation. It is not a whole-core or source-budget certificate. The
Lean geometric payment, rather than these experiments, pays the new family.
"""

import argparse
from collections import defaultdict
import json
import math
from pathlib import Path
import time

import mpmath as mp
import numpy as np

from probe_riesz_joined_count_correlation import pair_gram, population
from probe_riesz_reflected_phase_gram import span


def experiment(order, seed, heights):
    started = time.monotonic()
    ceiling = {256: 8, 640: 16, 1536: 32}[order]
    pars, rows, _ = population(order, ceiling, seed)
    physical, endpoint = pars['physical'], max(row['label'] for row in rows)
    scale = max(row['log_amplitude'] for row in rows)
    amplitudes = np.exp([row['log_amplitude']-scale for row in rows])
    totals = np.array([row['total'] for row in rows])
    weights = -amplitudes[None, :]*np.cos(np.array(heights)[:, None]*totals)
    columns = np.zeros(len(rows), dtype=np.int32)
    events = defaultdict(list)
    for i, row in enumerate(rows):
        for divisor, sign in row['divisors']:
            if divisor < physical:
                columns[i] += sign
            elif divisor < endpoint:
                events[divisor].append((i, sign))
    points = sorted({physical, endpoint, *events})
    cumulative, mass = {}, np.zeros(len(heights))
    for left, right in zip(points, points[1:]):
        for i, sign in events[left]:
            columns[i] += sign
        cumulative[left] = mass.copy()
        # This is the SAME original joined adverse selection throughout.
        mass += span(left, right)*((weights @ columns) > 0)
    cumulative[endpoint] = mass.copy()
    remaining, paid, absolute_paid = (np.zeros(len(heights)) for _ in range(3))
    ordered_paid = np.zeros(len(heights), dtype=int)
    ordered_remaining = np.zeros(len(heights), dtype=int)
    for i, row in enumerate(rows):
        for j in range(i+1, len(rows)):
            other = rows[j]
            gcd = math.gcd(row['label'], other['label'])
            if math.log(gcd) > order/4096:
                continue
            gap = row['total']-other['total']
            near = abs(row['label']-other['label'])/min(row['label'], other['label']) <= math.exp(-order/1000)
            old, wide = [], []
            for height in heights:
                residue = abs(gap-2*math.pi*round(height*gap/(2*math.pi))/height)
                old.append(not near and residue > math.exp(-order/1000)/(1+abs(height)))
                wide.append(residue <= math.exp(-order/4500)/(1+abs(height)))
            old, wide = np.array(old), np.array(wide)
            if not old.any():
                continue
            gram = pair_gram(row, other, physical, endpoint, cumulative)
            contribution = 2*weights[:, i]*weights[:, j]*gram
            remaining += contribution*old
            paid += contribution*(old & wide)
            absolute_paid += np.abs(contribution)*(old & wide)
            ordered_paid += 2*(old & wide)
            ordered_remaining += 2*(old & ~wide)
    cases = []
    for i, height in enumerate(heights):
        cases.append(dict(height=height,
                          rescaledOldRemainingEnergy=float(remaining[i]),
                          rescaledNewPaidSignedEnergy=float(paid[i]),
                          rescaledNewPaidAbsoluteEnergy=float(absolute_paid[i]),
                          rescaledWideRemainingEnergy=float(remaining[i]-paid[i]),
                          newlyPaidOrderedPairs=int(ordered_paid[i]),
                          stillRemainingOrderedPairs=int(ordered_remaining[i]),
                          removingPaidFamilyIncreasesSignedRemainder=bool(paid[i] < 0)))
    return dict(N=order, seed=seed, selectedLabels=len(rows),
                originalCountCeiling=ceiling, prematurelyApplyingEventualCountCrop=False,
                sourceAmplitudeLogScale=scale, seconds=time.monotonic()-started,
                cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[256, 640])
    parser.add_argument('--seeds', nargs='+', type=int, default=[317, 919])
    parser.add_argument('--heights', nargs='+', type=float, default=[54., 65., 100.])
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-wide-phase-probe.json'))
    args = parser.parse_args()
    mp.mp.dps = 100
    report = dict(scope='all subsets in constructed probable-prime universes; not full core',
                  adverseCutoffsSelectedOnce=True, originalWeightsAndMasksRetained=True,
                  exactIntegerDivisorSteps=True, harmonicLogInterpolation=True,
                  amplitudeRescaled=True, intervalArithmetic=False, primeCertificates=False,
                  floorBudgetCompared=False, cofinalBoundCertified=False,
                  energyMonotonicityAsserted=False,
                  cases=[experiment(n, seed, args.heights) for n in args.orders for seed in args.seeds])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    for batch in report['cases']:
        print(json.dumps({k: v for k, v in batch.items() if k != 'cases'}))
        for case in batch['cases']:
            print(json.dumps(case))


if __name__ == '__main__':
    main()

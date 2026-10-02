#!/usr/bin/env python3
"""Optional finite-population and exact-rational rate audit.

Retain every literal weight/mask in constructed prime universes, select
adverse cutoffs once, and integrate the old remaining energy and its new
disjoint phase neighbourhood. This is not the full core or a certified
source budget. Probable primes, common rescaling and log interpolation
remain exploratory. The Lean theorem proves the geometric payment.
"""

import argparse
from collections import defaultdict
from fractions import Fraction
import json
import math
from pathlib import Path
import time

import mpmath as mp
import numpy as np

from probe_riesz_joined_count_correlation import pair_gram, population
from probe_riesz_reflected_phase_gram import span


def rate_audit():
    source_upper = 2*Fraction(1, 10000)
    new_upper = source_upper-Fraction(1, 4900)
    certified = -Fraction(1, 250000)
    assert new_upper <= certified < 0
    return dict(sourceLogUpper=str(source_upper),
                removedDivisorExponent=str(Fraction(3, 262144)),
                oldWidthExponent='-1/4500', newWidthExponent='-1/4900',
                newEnergyExponentUpper=str(new_upper),
                certifiedEnergyExponent=str(certified),
                certifiedPriceExponent='-1/500000',
                finiteDivisorMass='(1+log(X))^4',
                energyConstant='20480*U^2*B^2*phaseCount(y)',
                energyPolynomialDegree=8, pricePolynomialDegree=5,
                criticalDenominatorFromSourceUpper=5000,
                widthRatioExponent=str(Fraction(1, 4500)-Fraction(1, 4900)))


def divisor_regression(limit):
    """Exact finite rational check of the harmonic bound, outside CI."""
    counts = [0]*(limit+1)
    for d in range(1, limit+1):
        for n in range(d, limit+1, d):
            counts[n] += 1
    mass, harmonic = Fraction(), Fraction()
    for n in range(1, limit+1):
        mass += Fraction(counts[n]**2, n)
        harmonic += Fraction(1, n)
        assert mass <= harmonic**4
    return dict(limit=limit, exactRational=True,
                finiteMassFloat=float(mass), harmonicPowerFloat=float(harmonic**4))


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
        mass += span(left, right)*((weights @ columns) > 0)
    cumulative[endpoint] = mass.copy()
    remaining, paid, absolute_paid = (np.zeros(len(heights)) for _ in range(3))
    ordered_paid = np.zeros(len(heights), dtype=int)
    ordered_remaining = np.zeros(len(heights), dtype=int)
    for i, row in enumerate(rows):
        for j in range(i+1, len(rows)):
            other = rows[j]
            if math.log(math.gcd(row['label'], other['label'])) > order/4096:
                continue
            gap = row['total']-other['total']
            near_label = (abs(row['label']-other['label'])/min(row['label'], other['label'])
                          <= math.exp(-order/1000))
            old, new = [], []
            for height in heights:
                residue = abs(gap-2*math.pi*round(height*gap/(2*math.pi))/height)
                old.append(not near_label and residue > math.exp(-order/4500)/(1+abs(height)))
                new.append(residue <= math.exp(-order/4900)/(1+abs(height)))
            old, new = np.array(old), np.array(new)
            if not old.any():
                continue
            gram = pair_gram(row, other, physical, endpoint, cumulative)
            contribution = 2*weights[:, i]*weights[:, j]*gram
            remaining += contribution*old
            paid += contribution*(old & new)
            absolute_paid += np.abs(contribution)*(old & new)
            ordered_paid += 2*(old & new)
            ordered_remaining += 2*(old & ~new)
    cases = []
    for i, height in enumerate(heights):
        cases.append(dict(height=height,
                          rescaledOldRemainingEnergy=float(remaining[i]),
                          rescaledNewPaidSignedEnergy=float(paid[i]),
                          rescaledNewPaidAbsoluteEnergy=float(absolute_paid[i]),
                          rescaledNewRemainingEnergy=float(remaining[i]-paid[i]),
                          newlyPaidOrderedPairs=int(ordered_paid[i]),
                          stillRemainingOrderedPairs=int(ordered_remaining[i]),
                          removingPaidFamilyIncreasesSignedRemainder=bool(paid[i] < 0)))
    return dict(N=order, seed=seed, selectedLabels=len(rows),
                originalCountCeiling=ceiling, prematurelyApplyingEventualCountCrop=False,
                sourceAmplitudeLogScale=scale, seconds=time.monotonic()-started, cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[256, 640])
    parser.add_argument('--seeds', nargs='+', type=int, default=[317, 919])
    parser.add_argument('--heights', nargs='+', type=float, default=[54., 65., 100.])
    parser.add_argument('--divisor-limit', type=int, default=256)
    parser.add_argument('--rates-only', action='store_true')
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-finite-phase-probe.json'))
    args = parser.parse_args()
    mp.mp.dps = 100
    report = dict(scope='constructed all-subset probable-prime universes, not full core',
                  adverseCutoffsSelectedOnce=True, originalWeightsAndMasksRetained=True,
                  exactIntegerDivisorSteps=True, harmonicLogInterpolation=True,
                  amplitudeRescaled=True, intervalArithmetic=False, primeCertificates=False,
                  floorBudgetCompared=False, cofinalBoundCertified=False,
                  energyMonotonicityAsserted=False, rates=rate_audit(),
                  divisorRegression=divisor_regression(args.divisor_limit),
                  cases=[] if args.rates_only else
                  [experiment(n, seed, args.heights) for n in args.orders for seed in args.seeds])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report['rates']))
    print(json.dumps(report['divisorRegression']))
    for batch in report['cases']:
        print(json.dumps({k: v for k, v in batch.items() if k != 'cases'}))
        for case in batch['cases']:
            print(json.dumps(case))


if __name__ == '__main__':
    main()

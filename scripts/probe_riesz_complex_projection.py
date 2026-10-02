#!/usr/bin/env python3
"""Optional full-cutoff real/imaginary projection test.

All constructed squarefree labels, original masks, allocation weights and
phases remain. Assemble both signed prefix columns before a single Gram
calculation. The complete matrix is positive semidefinite; an adverse-only
matrix cannot use the whole carrier's vanishing imaginary part.

These finite universes are not the full arithmetic core. Common amplitude
rescaling and harmonic log interpolation prohibit a source-budget claim.
In particular, the imaginary carrier in a finite subset is NOT assumed zero.
"""

import argparse
from collections import defaultdict
import json
import math
from pathlib import Path
import time

import mpmath as mp
import numpy as np

from probe_riesz_joined_count_correlation import population
from probe_riesz_reflected_phase_gram import span


def least_positive_cost(real, imag, bound):
    """Numerical minimum of a complete piecewise-linear joined cost.

    One bounded direction is chosen for ALL entries. Each breakpoint has
    a nonnegative slope jump; no sector chooses its own direction. This
    floating-point diagnostic is not an interval or source-scale proof.
    """
    bound = abs(bound)
    nonzero = imag != 0
    roots = real[nonzero]/imag[nonzero]
    jumps = np.abs(imag[nonzero])
    inside = (roots > -bound) & (roots < bound)
    roots, jumps = roots[inside], jumps[inside]
    ordering = np.argsort(roots)
    roots, jumps = roots[ordering], jumps[ordering]
    slope = -float(np.sum(imag[real+bound*imag > 0]))
    direction = -bound
    if slope < 0:
        cumulative = np.cumsum(jumps)
        reached = np.flatnonzero(cumulative >= -slope)
        direction = float(roots[reached[0]]) if len(reached) else bound
    cost = float(np.sum(np.maximum(real-direction*imag, 0.)))
    # Keep an explicit zero candidate despite rounding at a breakpoint.
    old = float(np.sum(np.maximum(real, 0.)))
    if old < cost:
        direction, cost = 0., old
    return direction, cost


def complete_period_columns(prefix, log_widths, points, height):
    """Join entire logarithmic phase periods, retaining both end clips."""
    grouped = defaultdict(lambda: np.zeros(2))
    if height <= 0:
        grouped[0] = prefix.T @ log_widths
    else:
        unit = 2*math.pi/height
        for vector, left, right in zip(prefix, points, points[1:]):
            lo, hi = math.log(left), math.log(right)
            period = math.floor(lo/unit)
            while lo < hi:
                edge = min(hi, (period+1)*unit)
                if edge <= lo:
                    period += 1
                    continue
                grouped[period] += vector*(edge-lo)
                lo, period = edge, period+1
    columns = np.array(list(grouped.values()))
    assert np.allclose(columns.sum(axis=0), prefix.T @ log_widths,
                       rtol=1e-9, atol=1e-7)
    return columns


def experiment(order, seed, heights, projection_bound):
    started = time.monotonic()
    ceiling = {256: 8, 640: 16, 1536: 32}[order]
    pars, rows, _ = population(order, ceiling, seed)
    physical, endpoint = pars['physical'], max(row['label'] for row in rows)
    scale = max(row['log_amplitude'] for row in rows)
    amplitude = np.exp([row['log_amplitude']-scale for row in rows])
    phase = np.array(heights)[:, None]*np.array([row['total'] for row in rows])
    weights = np.stack((-amplitude*np.cos(phase), amplitude*np.sin(phase)), axis=1)
    columns = np.zeros(len(rows), dtype=np.int32)
    events = defaultdict(list)
    for i, row in enumerate(rows):
        for divisor, sign in row['divisors']:
            if divisor < physical:
                columns[i] += sign
            elif divisor < endpoint:
                events[divisor].append((i, sign))
    points = sorted({physical, endpoint, *events})
    full = np.zeros((len(heights), 2, 2))
    adverse = np.zeros_like(full)
    carrier = np.zeros((len(heights), 2))
    adverse_carrier = np.zeros_like(carrier)
    adverse_width = np.zeros(len(heights))
    prefix_rows, log_widths, harmonic_widths = [], [], []
    for left, right in zip(points, points[1:]):
        for i, sign in events[left]:
            columns[i] += sign
        phi = weights @ columns
        mass = span(left, right)
        width = math.log(right)-math.log(left)
        prefix_rows.append(phi.copy())
        log_widths.append(width)
        harmonic_widths.append(mass)
        matrix = np.einsum('hi,hj->hij', phi, phi)
        full += mass*matrix
        bad = phi[:, 0] > 0
        adverse += mass*matrix*bad[:, None, None]
        carrier -= width*phi
        adverse_carrier -= width*phi*bad[:, None]
        adverse_width += width*bad
    riesz = np.array([math.fsum(sign*max(pars['length']-math.log(d), 0.)
                               for d, sign in row['divisors']) for row in rows])
    literal = weights @ riesz
    assert np.allclose(carrier, literal, rtol=1e-9, atol=1e-7)
    profile = math.log(endpoint)-pars['length']
    prefix_rows = np.array(prefix_rows)
    log_widths = np.array(log_widths)
    harmonic_widths = np.array(harmonic_widths)
    # Fixed bounded directions include zero: the least cost can NEVER
    # exceed the old cost. No native/full-core imaginary limit is assumed.
    directions = projection_bound*np.array([-1., -.5, -.25, -.125, 0., .125, .25, .5, 1.])
    cases = []
    for i, height in enumerate(heights):
        cc, cs, ss = full[i, 0, 0], full[i, 0, 1], full[i, 1, 1]
        projection = float(np.clip(cs/ss if ss else 0., -projection_bound, projection_bound))
        projected = max(cc-2*projection*cs+projection**2*ss, 0.)
        direct_cost = math.sqrt(cc*profile)
        projected_cost = math.sqrt(projected*profile)
        corrected_cost = projected_cost+abs(projection*carrier[i, 1])
        old_cost = math.sqrt(adverse[i, 0, 0]*adverse_width[i])
        rotated = prefix_rows[:, i, 0, None]-prefix_rows[:, i, 1, None]*directions
        positive = rotated > 0
        one_sided = np.maximum(rotated, 0.).T @ log_widths
        one_sided_best = int(np.argmin(one_sided))
        atomic_original = float(one_sided[4])
        atomic_best = float(one_sided[one_sided_best])
        atomic_projection = float(directions[one_sided_best])
        energy = np.sum(harmonic_widths[:, None]*np.where(positive, rotated**2, 0.), axis=0)
        price = np.sum(log_widths[:, None]*positive, axis=0)
        directed_costs = np.sqrt(energy*price)
        directed_best = int(np.argmin(directed_costs))
        exact_direction, exact_atomic = least_positive_cost(
            prefix_rows[:, i, 0]*log_widths,
            prefix_rows[:, i, 1]*log_widths, projection_bound)
        periods = complete_period_columns(prefix_rows[:, i], log_widths, points, height)
        period_direction, period_cost = least_positive_cost(
            periods[:, 0], periods[:, 1], projection_bound)
        period_original = float(np.sum(np.maximum(periods[:, 0], 0.)))
        assert exact_atomic <= atomic_best+1e-7
        assert period_cost <= exact_atomic+1e-7
        assert period_original <= atomic_original+1e-7
        cases.append(dict(
            height=height, projection=projection,
            rescaledRealCarrier=float(carrier[i, 0]),
            rescaledImaginaryCarrier=float(carrier[i, 1]),
            rescaledAdverseImaginaryCarrier=float(adverse_carrier[i, 1]),
            rescaledCompleteRealEnergy=float(cc),
            rescaledCompleteCrossEnergy=float(cs),
            rescaledCompleteImaginaryEnergy=float(ss),
            rescaledProjectedEnergy=float(projected),
            projectedEnergyFraction=float(projected/cc) if cc else None,
            rescaledOldAdverseCost=old_cost,
            rescaledCompleteUnprojectedCost=direct_cost,
            rescaledProjectedCost=projected_cost,
            rescaledProjectedCostWithLiteralImaginaryCorrection=corrected_cost,
            projectedToOldAdverseCost=projected_cost/old_cost if old_cost else None,
            correctedToOldAdverseCost=corrected_cost/old_cost if old_cost else None,
            rescaledOldAtomicCost=atomic_original,
            rescaledBoundedDirectionAtomicCost=atomic_best,
            boundedDirectionAtomicProjection=atomic_projection,
            atomicSavingFraction=1-atomic_best/atomic_original if atomic_original else None,
            rescaledAtomicCostWithLiteralSignedImaginaryCorrection=atomic_best-atomic_projection*carrier[i, 1],
            boundedDirectionCauchyProjection=float(directions[directed_best]),
            boundedDirectionCauchyCost=float(directed_costs[directed_best]),
            boundedDirectionCauchyFraction=float(directed_costs[directed_best]/old_cost) if old_cost else None,
            leastAtomicDirection=exact_direction,
            rescaledLeastAtomicCost=exact_atomic,
            leastAtomicSavingFraction=1-exact_atomic/atomic_original if atomic_original else None,
            completePeriodCount=len(periods),
            rescaledOriginalCompletePeriodCost=period_original,
            leastWholePeriodDirection=period_direction,
            rescaledLeastWholePeriodCost=period_cost,
            wholePeriodSavingFraction=1-period_cost/period_original if period_original else None,
            rescaledWholePeriodCostWithLiteralSignedImaginaryCorrection=period_cost-period_direction*carrier[i, 1],
            noImaginaryZeroAssumedForSubset=True))
    return dict(N=order, seed=seed, selectedLabels=len(rows),
                originalCountCeiling=ceiling, sourceAmplitudeLogScale=scale,
                seconds=time.monotonic()-started, cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[256, 640])
    parser.add_argument('--seeds', nargs='+', type=int, default=[317, 919])
    parser.add_argument('--heights', nargs='+', type=float, default=[54., 65., 100.])
    parser.add_argument('--projection-bound', type=float, default=4.)
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-complex-projection-probe.json'))
    args = parser.parse_args()
    mp.mp.dps = 100
    report = dict(
        scope='complete constructed probable-prime universes, not full core',
        originalWeightsAndMasksRetained=True, fullCutoffsUsedForProjection=True,
        countClassesJoinedBeforeGram=True, amplitudeRescaled=True,
        completePeriodCostsJoinedBeforeTilt=True,
        boundedWholeTiltChosenAtPiecewiseLinearMinimum=True,
        harmonicLogInterpolation=True, intervalArithmetic=False,
        fullCoreImaginaryLimitAssumedForSubset=False, floorBudgetCompared=False,
        effectiveStartCertified=False, cofinalBoundCertified=False,
        projectionBound=args.projection_bound,
        cases=[experiment(n, seed, args.heights, args.projection_bound)
               for n in args.orders for seed in args.seeds])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    for batch in report['cases']:
        print(json.dumps({key: value for key, value in batch.items() if key != 'cases'}))
        for case in batch['cases']:
            print(json.dumps(case))


if __name__ == '__main__':
    main()

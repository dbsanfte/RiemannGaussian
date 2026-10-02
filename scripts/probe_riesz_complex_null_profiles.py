#!/usr/bin/env python3
"""Optional joined-period test of exact COMPLEX divisor-log null profiles.

Every constructed label retains the original masks, allocation and phase.
All counts and cutoff periods are joined BEFORE choosing one global vector.
The linear and quadratic divisor-log moments vanish label by label. Their
complex coefficients therefore do not alter the literal carrier. A bounded
global imaginary tilt still requires its actual whole-carrier correction.

Probable primes, amplitude rescaling and floating log interpolation make
this a diagnostic, not a full-core or source-scale floor certificate. Early
period edges use integer cutoffs; large edges use their logarithms, with the
rounding error unresolved. This script is outside all builds and CI.
"""

import argparse
from collections import defaultdict
import json
import math
from pathlib import Path
import time

import mpmath as mp
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, eye, hstack

from probe_riesz_complex_projection import least_positive_cost
from probe_riesz_joined_count_correlation import population


def optimize(columns, indices, bound, initial):
    """One convex LP for all periods; verify the returned feasible cost."""
    baseline, directions = columns[:, 0], columns[:, indices]
    groups = len(baseline)
    scale = max(float(np.max(np.abs(columns))), 1.)
    objective = np.r_[np.zeros(len(indices)), np.ones(groups)]
    constraints = hstack((csr_matrix(directions/scale), -eye(groups)), format='csr')
    result = linprog(objective, A_ub=constraints, b_ub=-baseline/scale,
                     bounds=[(-bound, bound)]*len(indices)+[(0., None)]*groups,
                     method='highs')
    if not result.success:
        raise RuntimeError(result.message)
    candidates = [np.zeros(len(indices)), np.asarray(initial), result.x[:len(indices)]]
    best = min(candidates, key=lambda v: float(np.maximum(baseline+directions@v, 0.).sum()))
    cost = float(np.maximum(baseline+directions@best, 0.).sum())
    assert np.max(np.abs(best)) <= bound+1e-8
    return dict(parameters=best.tolist(), rescaledCost=cost,
                joinedSignedTotal=float((baseline+directions@best).sum()),
                solverSuccess=True, iterations=result.nit)


def period_edge(period, unit):
    logarithm = (period+1)*unit
    # Retain integer period edges where discreteness matters most. At huge
    # cutoffs this is the old log interpolation, NOT an integer certificate.
    if logarithm < 30:
        return math.log(math.ceil(math.exp(logarithm)))
    return logarithm


def experiment(order, seed, heights, bound):
    started = time.monotonic()
    ceiling = {256: 8, 640: 16, 1536: 32}[order]
    pars, rows, _ = population(order, ceiling, seed)
    physical, endpoint = pars['physical'], max(row['label'] for row in rows)
    scale = max(row['log_amplitude'] for row in rows)
    amplitude = np.exp([row['log_amplitude']-scale for row in rows])
    phases = np.asarray(heights)[:, None]*np.array([row['total'] for row in rows])
    weights = amplitude*np.exp(-1j*phases)*(-1)
    events = defaultdict(list)
    for i, row in enumerate(rows):
        for divisor, sign in row['divisors']:
            if divisor < endpoint:
                events[divisor].append((i, sign))
    points = sorted({1, physical, endpoint, *events})
    prefix = np.zeros(len(rows), dtype=np.int32)
    grouped = [defaultdict(lambda: np.zeros(3, dtype=complex)) for _ in heights]
    totals = np.zeros((len(heights), 3), dtype=complex)
    for left, right in zip(points, points[1:]):
        for i, sign in events[left]:
            prefix[i] += sign
        phi = weights @ prefix
        lo, hi = math.log(left), math.log(right)
        base = left >= physical
        vector = np.array([-(hi-lo) if base else 0., -(hi-lo),
                           -(hi*hi-lo*lo)/(order+1)])
        totals += phi[:, None]*vector
        for ih, height in enumerate(heights):
            if height <= 0:
                grouped[ih][0] += phi[ih]*vector
                continue
            unit = 2*math.pi/height
            cursor = lo
            period = math.floor(cursor/unit)
            while cursor < hi:
                edge = min(hi, period_edge(period, unit))
                if edge <= cursor:
                    period += 1
                    continue
                widths = np.array([-(edge-cursor) if base else 0., -(edge-cursor),
                                   -(edge*edge-cursor*cursor)/(order+1)])
                grouped[ih][period] += phi[ih]*widths
                cursor, period = edge, period+1
    riesz = np.array([math.fsum(sign*max(pars['length']-math.log(d), 0.)
                               for d, sign in row['divisors']) for row in rows])
    literal = weights @ riesz
    common_moment = weights.sum(axis=1)
    assert np.allclose(totals[:, 0], literal, rtol=1e-9, atol=1e-7)
    assert np.max(np.abs(totals[:, 1:])) < 1e-6
    cases = []
    for ih, height in enumerate(heights):
        columns = np.asarray(list(grouped[ih].values()))
        assert np.allclose(columns.sum(axis=0), totals[ih], rtol=1e-8, atol=1e-7)
        # Objective = -(Re B-v Im B+Re(A Q1+B Q2)). Null moments summed
        # over every period are ZERO; only v changes the signed total.
        design = np.column_stack((-columns[:, 0].real, columns[:, 0].imag,
                                   -columns[:, 1].real, columns[:, 1].imag,
                                   -columns[:, 2].real, columns[:, 2].imag))
        tilt, tilt_cost = least_positive_cost(design[:, 0], -design[:, 1], bound)
        baseline = dict(parameters=[tilt], rescaledCost=tilt_cost)
        real = optimize(design, [1, 2, 4], bound, [tilt, 0., 0.])
        imaginary = optimize(design, [1, 3, 5], bound, [tilt, 0., 0.])
        complex_fit = optimize(design, [1, 2, 3, 4, 5], bound, [tilt, 0., 0., 0., 0.])
        moment = common_moment[ih]
        norm = abs(moment)
        orthogonal = np.array([moment.imag, moment.real])/norm if norm else np.zeros(2)
        coherent_design = np.column_stack((design[:, :2],
            design[:, 2:4]@orthogonal, design[:, 4:6]@orthogonal))
        coherent_fit = optimize(coherent_design, [1, 2, 3], bound, [tilt, 0., 0.])
        assert complex_fit['rescaledCost'] <= min(real['rescaledCost'], imaginary['rescaledCost'], tilt_cost)+1e-6
        for fit in [real, imaginary, complex_fit, coherent_fit]:
            v = fit['parameters'][0]
            fit['rescaledCostWithLiteralSignedImaginaryCorrection'] = fit['rescaledCost']-v*literal[ih].imag
            fit['savingOverTiltFraction'] = 1-fit['rescaledCost']/tilt_cost if tilt_cost else None
        cases.append(dict(height=height, periods=len(columns),
                          rescaledLiteralReal=float(literal[ih].real),
                          rescaledLiteralImaginary=float(literal[ih].imag),
                          maximumNullSumError=float(np.max(np.abs(totals[ih, 1:]))),
                          rescaledCommonMomentReal=float(moment.real),
                          rescaledCommonMomentImaginary=float(moment.imag),
                          originalTilt=baseline, realNulls=real,
                          imaginaryNulls=imaginary, complexNulls=complex_fit,
                          coherentChannelFreeNulls=coherent_fit))
    return dict(N=order, seed=seed, selectedLabels=len(rows),
                originalCountCeiling=ceiling, sourceAmplitudeLogScale=scale,
                intervals=len(points)-1, seconds=time.monotonic()-started, cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[256, 640])
    parser.add_argument('--seeds', nargs='+', type=int, default=[317, 919])
    parser.add_argument('--heights', nargs='+', type=float, default=[54., 65., 100.])
    parser.add_argument('--bound', type=float, default=4.)
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-complex-null-probe.json'))
    args = parser.parse_args()
    mp.mp.dps = 100
    report = dict(scope='complete constructed prime universes, not full core',
                  originalMasksAndWeightsRetained=True, allCountsJoined=True,
                  allCutoffsRetained=True, nullCoefficientsComplex=True,
                  subsetImaginaryZeroAssumed=False, amplitudeRescaled=True,
                  largeCutoffsLogInterpolated=True, intervalArithmetic=False,
                  floorBudgetCertified=False, cofinalBoundCertified=False, cases=[])
    for n in args.orders:
        for seed in args.seeds:
            batch = experiment(n, seed, args.heights, args.bound)
            report['cases'].append(batch)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(report, indent=2)+'\n')
            print(json.dumps(batch), flush=True)


if __name__ == '__main__':
    main()

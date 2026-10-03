#!/usr/bin/env python3
"""Optional all-count tangent-cubic diagnostic, outside ordinary builds/CI.

The cubic divisor moment is zero above count three. Its full complex total
defines an exact perpendicular direction on ALL labels, including triples.
Join it with the existing six nulls and retain every cutoff crossing.

The constructed two-pool populations, probable primes, floating phases,
common amplitude scale and interpolated large cutoffs are NOT the native
population. Exact rational LP replay certifies only the floating matrix.
This probe gives neither a cofinal floor nor an arithmetic no-go theorem.
"""

import argparse
from collections import defaultdict
from fractions import Fraction as F
import hashlib
import itertools
import json
import math
from pathlib import Path
import random
import subprocess
import time

import mpmath as mp
import numpy as np

from probe_riesz_complex_null_profiles import optimize, period_edge
from probe_riesz_joined_count_correlation import population
from probe_riesz_quantitative_null_step import exact_matrix_cost_audit, threshold_step


def self_test():
    """Rational finite-difference/complex-null regression; not prime logs."""
    rng = random.Random(4381)
    for trial in range(500):
        count = 3 + trial % 6
        shares = [F(rng.randrange(1, 50), rng.randrange(1, 20)) for _ in range(count)]
        moment = sum(((-1)**len(a)*sum((shares[i] for i in a), F())**3
                      for k in range(count+1)
                      for a in itertools.combinations(range(count), k)), F())
        expected = -6*math.prod(shares) if count == 3 else F()
        assert moment == expected
        real = [F(rng.randrange(-30, 31), 17) for _ in range(count)]
        imag = [F(rng.randrange(-30, 31), 19) for _ in range(count)]
        mr, mi = sum(real, F()), sum(imag, F())
        assert sum((mi*r-mr*i for r, i in zip(real, imag)), F()) == 0
    return dict(rationalFiniteDifferenceCases=500, counts=list(range(3, 9)),
                triplesRetained=True, perpendicularMomentRegressions=500,
                actualPrimeLogCertificate=False)


def experiment(order, seed, heights, cost_audit):
    started = time.monotonic()
    ceiling = {256: 8, 640: 16, 1536: 32}[order]
    pars, rows, excluded = population(order, ceiling, seed)
    physical, endpoint = pars['physical'], max(r['label'] for r in rows)
    amplitude_scale = max(r['log_amplitude'] for r in rows)
    weights = -np.exp([r['log_amplitude']-amplitude_scale for r in rows])[None, :]*np.exp(
        -1j*np.asarray(heights)[:, None]*np.asarray([r['total'] for r in rows])[None, :])
    higher = np.asarray([r['count'] >= 4 for r in rows])
    events = defaultdict(list)
    for i, row in enumerate(rows):
        for d, sign in row['divisors']:
            if d < endpoint:
                events[d].append((i, sign))
    points = sorted({1, physical, endpoint, *events})
    prefix = np.zeros(len(rows), dtype=np.int32)
    # Three complex old profiles, higher-count cube, WHOLE cube.
    grouped = [defaultdict(lambda: np.zeros(5, dtype=complex)) for _ in heights]
    for left, right in zip(points, points[1:]):
        for i, sign in events[left]:
            prefix[i] += sign
        phi = weights@prefix
        psi = weights[:, higher]@prefix[higher]
        lo, hi = math.log(left), math.log(right)
        for ih, height in enumerate(heights):
            unit = 2*math.pi/height
            cursor, period = lo, math.floor(lo/unit)
            while cursor < hi:
                edge = min(hi, period_edge(period, unit))
                if edge <= cursor:
                    period += 1
                    continue
                widths = np.asarray([-(edge-cursor) if left >= physical else 0.,
                    -(edge-cursor), -(edge*edge-cursor*cursor)/(order+1)])
                cube = -(edge**3-cursor**3)/(order+1)**2
                grouped[ih][period] += np.r_[phi[ih]*widths, psi[ih]*cube, phi[ih]*cube]
                cursor, period = edge, period+1
    cases = []
    for ih, height in enumerate(heights):
        data = np.asarray([grouped[ih][k] for k in sorted(grouped[ih])])
        base = np.column_stack((-data[:, 0].real, data[:, 0].imag,
            -data[:, 1].real, data[:, 1].imag, -data[:, 2].real, data[:, 2].imag))
        original = optimize(base, list(range(1, 6)), 4., [0.]*5)
        p = np.asarray(original['parameters'])
        six_design = np.column_stack((base[:, 0]+p[0]*base[:, 1],
            base[:, 2:6], -data[:, 3].real, data[:, 3].imag))
        six = optimize(six_design, list(range(1, 7)), 4., [*p[1:], 0., 0.])
        t = -(six_design[:, 0]+six_design[:, 1:]@np.asarray(six['parameters']))
        # Exact arithmetic cubic identity evaluated with floating logs.
        moment = -6*sum(weights[ih, i]*math.prod(math.log(p) for p in row['factors'])
                       for i, row in enumerate(rows) if row['count'] == 3)/(order+1)**2
        raw = data[:, 4]
        residual = float(abs(raw.sum()-moment))
        assert residual <= 1e-7*max(1., abs(moment), float(np.abs(raw).sum()))
        axis = np.asarray([moment.imag, moment.real])/abs(moment) if moment else np.zeros(2)
        common = weights[ih].sum()
        determinant = float(moment.real*common.imag-moment.imag*common.real)
        phase_sine = determinant/(abs(moment)*abs(common)) if moment and common else 0.
        v = axis[0]*raw.real-axis[1]*raw.imag
        null_residual = float(abs(v.sum()))
        assert null_residual <= 1e-7*max(1., float(np.abs(v).sum()))
        positive, negative = threshold_step(t, v), threshold_step(t, -v)
        line = max((positive, negative), key=lambda z: z['guaranteedGain'])
        seven_design = np.column_stack((six_design, -v))
        case = dict(height=height, groups=len(data), sixCost=six['rescaledCost'],
                    baselineCost=original['rescaledCost'],
                    imaginaryTiltUnchanged=float(p[0]),
                    complexTripleMoment=[float(moment.real), float(moment.imag)],
                    commonComplexMoment=[float(common.real), float(common.imag)],
                    twoMomentDeterminant=determinant,
                    normalizedPhaseSeparationSine=float(phase_sine),
                    coherentPrefixTangentCoefficient=float(-determinant/abs(moment)) if moment else 0.,
                    firstCutoffTangent=float(v[0]),
                    cubicIdentityFloatingResidual=residual, nullFloatingResidual=null_residual,
                    fixedDirectionThreshold=line,
                    rankBefore=int(np.linalg.matrix_rank(six_design[:, 1:])),
                    rankAfter=int(np.linalg.matrix_rank(seven_design[:, 1:])))
        try:
            seven = optimize(seven_design, list(range(1, 8)), 4., [*six['parameters'], 0.])
            assert seven['rescaledCost'] <= six['rescaledCost']+1e-7
            case.update(sevenCost=seven['rescaledCost'], sevenParameters=seven['parameters'],
                additionalFractionOfRemainingFiniteCost=1-seven['rescaledCost']/six['rescaledCost'],
                numericalSevenFitSucceeded=True)
            if cost_audit:
                case['exactFloatingMatrixAudit'] = exact_matrix_cost_audit(seven_design)
        except RuntimeError as error:
            case.update(numericalSevenFitSucceeded=False, numericalFailure=str(error))
        cases.append(case)
    return dict(N=order, seed=seed, labels=len(rows), originalCountCeiling=ceiling,
                eventualNativeCountCropApplied=False, sourceAmplitudeLogScale=amplitude_scale,
                exclusions=dict(excluded), seconds=time.monotonic()-started, cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', choices=[256, 640, 1536], default=[256, 640])
    parser.add_argument('--seeds', type=int, nargs='+', default=[317])
    parser.add_argument('--heights', type=float, nargs='+', default=[54., 65., 100.])
    parser.add_argument('--cost-audit', action='store_true')
    parser.add_argument('--self-test-only', action='store_true')
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-tangent-cubic/report.json'))
    args = parser.parse_args()
    if any(not math.isfinite(y) or y < 54 for y in args.heights):
        parser.error('finite heights >=54 required')
    mp.mp.dps = 100
    report = dict(schemaVersion=1, head=subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                  text=True).strip(), selfTest=self_test(), cases=[],
                  sourceSHA256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope=dict(outsideBuildsCI=True, nativeFloorProved=False, nativeCostBound=False,
                      wholeNativePopulation=False, populationDensitySample=False,
                      probablePrimes=True, floatingPhases=True, largeCutoffsInterpolated=True,
                      allSelectedCountsPeriodsRetained=True, ordinaryImaginaryTiltUnchanged=True,
                      sourceAmplitudeRescaled=True, exactReplayOnlyOfFloatingMatrix=True))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if not args.self_test_only:
        for order in args.orders:
            for seed in args.seeds:
                batch = experiment(order, seed, args.heights, args.cost_audit)
                report['cases'].append(batch)
                args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
                print(json.dumps(dict(N=order, seed=seed, labels=batch['labels'], cases=[
                    {k: c[k] for k in ('height', 'sixCost', 'numericalSevenFitSucceeded',
                        'sevenCost', 'additionalFractionOfRemainingFiniteCost') if k in c}
                    for c in batch['cases']]), allow_nan=False), flush=True)
    report['allRequestedNumericalFitsSucceeded'] = all(c['numericalSevenFitSucceeded']
        for batch in report['cases'] for c in batch['cases'])
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print(json.dumps(report['selfTest']), flush=True)


if __name__ == '__main__':
    main()

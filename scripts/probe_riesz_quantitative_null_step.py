#!/usr/bin/env python3
"""Optional quantitative cubic-null probe, after joining every selected group.

Exact rational unit inputs replay the Lean quadratic crossing inequality.
The optional --prime-probe enumerates complete constructed prime universes
using the existing literal masks/weights, and keeps all their cutoff groups.
They are a finite subpopulation, NOT the whole native core or a density sample.
Probable primes, floating phases and logarithmic interpolation are unresolved:
no native source-scale credit, numerical floor or zero exclusion is certified.
These small orders precede the eventual K/864 count crop; it is not applied
prematurely. The experiment is on the original finite-universe population.
Outside ordinary builds/CI; no claim follows from a floating optimiser.
--cost-audit adds exact rational primal/dual replay of the FLOATING input
matrix, not of the underlying primes/logarithms. It can diagnose whether
more coefficient search is useful without certifying a native bound.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import random
import subprocess
import sys
import time

sys.dont_write_bytecode = True


def exact_step(baseline, direction, threshold=0):
    from riesz_signed_block_geometry import replay
    t, v = list(map(F, baseline)), list(map(F, direction))
    threshold = F(threshold)
    if len(t) != len(v) or not t or sum(v, F()) or threshold < 0:
        raise ValueError('complete matching groups and an exact null required')
    d = sum((b for a, b in zip(t, v) if a < 0), F())
    z = sum((max(b if a < 0 else -b, F()) for a, b in zip(t, v)
             if abs(a) <= threshold), F())
    h = sum((b*b/(4*abs(a)) for a, b in zip(t, v) if abs(a) > threshold), F())
    available = max(d-z, F())
    step = available/(2*h) if h else F()
    guarantee = available*available/(4*h) if h else F()
    actual = replay(t, [[b] for b in v], [step])
    assert 0 <= guarantee <= actual['gain']
    assert actual['exactCrossingCost'] <= step*z+step*step*h
    # A second step tests the crossing bound away from its optimum.
    test_step = F(7, 3)
    other = replay(t, [[b] for b in v], [test_step])
    assert other['exactCrossingCost'] <= test_step*z+test_step*test_step*h
    return dict(step=str(step), guaranteedGain=str(guarantee),
                actualGain=str(actual['gain']), signedCorrelation=str(d),
                nearDebit=str(z), crossingPrice=str(h), threshold=str(threshold))


def self_test():
    rng = random.Random(37057705249)
    for _ in range(1000):
        n = rng.randrange(2, 14)
        t = [F(rng.randrange(-20, 21), rng.randrange(1, 10)) for _ in range(n)]
        v = [F(rng.randrange(-12, 13), rng.randrange(1, 10)) for _ in range(n-1)]
        v.append(-sum(v, F()))
        exact_step(t, v)
        exact_step(t, v, F(rng.randrange(1, 50), rng.randrange(1, 10)))
    result = exact_step([0, 0, 1, -1], [0, 0, -2, 2])
    assert result['guaranteedGain'] == '1/2' and result['actualGain'] == '1'
    coordinate_one = exact_step([0, 0, 1, -1], [1, -1, -1, 1])
    coordinate_two = exact_step([0, 0, 1, -1], [-1, 1, -1, 1])
    assert coordinate_one['guaranteedGain'] == coordinate_two['guaranteedGain'] == '0'
    assert F(coordinate_one['nearDebit'])+F(coordinate_two['nearDebit'])-F(result['nearDebit']) == 2
    assert exact_step([0, -1], [1, -1])['guaranteedGain'] == '0'
    assert exact_step([0, 0], [0, 0])['guaranteedGain'] == '0'
    tiny = F(1, 1000000)
    before = exact_step([-tiny, -1, 1], [1, 1, -2])
    after = exact_step([-tiny, -1, 1], [1, 1, -2], tiny)
    assert after['guaranteedGain'] == '1/5'
    assert F(after['guaranteedGain']) > 10000*F(before['guaranteedGain'])
    return dict(exactRationalRegressions=2000, jointZeroFaceExample=result,
                joinedZeroDebitCancellation='2', individualAxesGiveNoGuarantee=True,
                nearZeroExample=dict(unthresholded=before, thresholded=after),
                zeroGroupsNotDiscarded=True, zeroPriceHandled=True,
                scope='unit inputs, not native prime-population bounds')


def floating_step(t, v):
    """Exploration only; no rounding tolerance makes a proof of a credit."""
    import numpy as np
    adverse = t < 0
    d = float(v[adverse].sum())
    z = float(np.maximum(-v[t == 0], 0).sum())
    h = float(np.sum(v[t != 0]**2/(4*np.abs(t[t != 0]))))
    available = max(d-z, 0.)
    step = available/(2*h) if h else 0.
    guarantee = available*available/(4*h) if h else 0.
    old = float(np.maximum(-t, 0).sum())
    new = float(np.maximum(-(t+step*v), 0).sum())
    scale = max(1., old)
    assert new <= old+1e-9*scale
    assert guarantee <= old-new+1e-9*scale
    return dict(step=step, guaranteedGain=guarantee, actualGain=old-new,
                gainFractionOfFiniteBaseline=guarantee/old if old else None,
                actualGainFraction=1-new/old if old else None,
                signedCorrelation=d, zeroBlockDebit=z, crossingPrice=h,
                correctedCost=new, nativePopulationOrFloorCertified=False)


def threshold_step(t, v):
    """Charge tiny-margin groups linearly; price remaining crossings quadratically.

    Sorted cumulative sums test EVERY distinct margin threshold, without
    discarding a kink or selecting counts separately. Still floating research.
    """
    import numpy as np
    d = float(v[t < 0].sum())
    debit = np.where(t < 0, np.maximum(v, 0), np.maximum(-v, 0))
    price = np.divide(v*v, 4*np.abs(t), out=np.zeros_like(v), where=t != 0)
    margins = np.sort(np.unique(np.r_[0., np.abs(t)]))
    order = np.argsort(np.abs(t))
    mags = np.abs(t[order])
    prefix = np.r_[0., np.cumsum(debit[order])]
    # Reverse cumulative sum avoids subtracting huge near-zero prices
    # when only the large-margin groups remain.
    suffix = np.r_[np.cumsum(price[order][::-1])[::-1], 0.]
    ends = np.searchsorted(mags, margins, side='right')
    available = np.maximum(d-prefix[ends], 0.)
    gains = np.divide(available**2, 4*suffix[ends], out=np.zeros_like(available),
                      where=suffix[ends] > 0)
    i = int(np.argmax(gains))
    z, h, eta = float(prefix[ends[i]]), float(suffix[ends[i]]), float(available[i])
    step = eta/(2*h) if h else 0.
    old = float(np.maximum(-t, 0).sum())
    new = float(np.maximum(-(t+step*v), 0).sum())
    gain = float(gains[i])
    assert 0 <= gain <= old-new+1e-8*max(1., old)
    return dict(threshold=float(margins[i]), thresholdCandidates=len(margins),
                nearGroups=int(ends[i]), step=step, guaranteedGain=gain,
                actualGain=old-new, signedCorrelation=d, nearDebit=z,
                farCrossingPrice=h, correctedCost=new,
                gainFractionOfFiniteBaseline=gain/old if old else None,
                nativePopulationOrFloorCertified=False)


def rational_solve(matrix, rhs):
    """Tiny exact linear solve; None means a singular or nonsquare system."""
    size = len(rhs)
    if len(matrix) != size or any(len(row) != size for row in matrix):
        return None
    augmented = [list(map(F, row))+[F(b)] for row, b in zip(matrix, rhs)]
    for col in range(size):
        pivot = next((i for i in range(col, size) if augmented[i][col]), None)
        if pivot is None:
            return None
        augmented[col], augmented[pivot] = augmented[pivot], augmented[col]
        unit = augmented[col][col]
        augmented[col] = [value/unit for value in augmented[col]]
        for i in range(size):
            if i != col and augmented[i][col]:
                unit = augmented[i][col]
                augmented[i] = [x-unit*y for x, y in zip(augmented[i], augmented[col])]
    return [row[-1] for row in augmented]


def exact_matrix_cost_audit(columns, bound=4):
    """Certify cost bounds ONLY for rational numbers equal to input doubles.

    All periods remain in the matrix. Six fractional dual weights usually
    suffice to make the directional correlations EXACTLY zero. Such a dual
    bounds EVERY real coefficient vector, not just a numerical candidate or
    a bounded search. If exact feasibility fails, the existing box penalty
    is paid and the unrestricted conclusion is withheld.
    """
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix, eye, hstack
    started = time.monotonic()
    columns = np.asarray(columns, dtype=float)
    baseline, directions = columns[:, 0], columns[:, 1:]
    groups, dimension = directions.shape
    scale = max(float(np.max(np.abs(columns))), 1.)
    fit = linprog(np.r_[np.zeros(dimension), np.ones(groups)],
        A_ub=hstack((csr_matrix(directions/scale), -eye(groups)), format='csr'),
        b_ub=-baseline/scale,
        bounds=[(-bound, bound)]*dimension+[(0., None)]*groups, method='highs')
    if not fit.success:
        raise RuntimeError(fit.message)
    # Fraction.from_float preserves each input binary value EXACTLY.
    t = [F.from_float(float(x)) for x in baseline]
    v = [[F.from_float(float(x)) for x in row] for row in directions]
    dual = [min(F(1), max(F(), F(float(-x)).limit_denominator(10**8)))
            for x in fit.ineqlin.marginals]
    free = [i for i, h in enumerate(dual) if 0 < h < 1]
    h = dual.copy()
    if len(free) == dimension:
        fixed = [i for i, value in enumerate(h) if value == 1]
        correction = rational_solve([[v[i][j] for i in free] for j in range(dimension)],
            [-sum((v[i][j] for i in fixed), F()) for j in range(dimension)])
        if correction is not None and all(0 <= value <= 1 for value in correction):
            for i, value in zip(free, correction):
                h[i] = value
    residual = [sum((value*row[j] for value, row in zip(h, v) if value), F())
                for j in range(dimension)]
    unrestricted = not any(residual)
    lower = sum((value*x for value, x in zip(h, t) if value), F())
    if not unrestricted:
        lower -= F(bound)*sum(map(abs, residual), F())
    lower = max(lower, F())
    q = [F(float(x)).limit_denominator(10**8) for x in fit.x[:dimension]]
    exact_primal = None
    if len(free) == dimension:
        exact_primal = rational_solve([v[i] for i in free], [-t[i] for i in free])
    if exact_primal is not None and all(abs(value) <= bound for value in exact_primal):
        q = exact_primal
    assert all(abs(value) <= bound for value in q)
    upper = sum((max(x+sum((a*b for a, b in zip(q, row)), F()), F())
                 for x, row in zip(t, v)), F())
    assert 0 <= lower <= upper
    return dict(groupsRetained=groups, nullDimension=dimension,
        rationalInputMatrixEqualsBinaryFloats=True, nativeArithmeticCertified=False,
        exactPrimalUpper=str(upper), exactDualLower=str(lower),
        exactPrimalDualGap=str(upper-lower),
        relativePrimalDualGap=float((upper-lower)/upper) if upper else 0.,
        exactDualDirectionalCorrelationsZero=unrestricted,
        everyRealCoefficientVectorCovered=unrestricted,
        onlyBoxCoveredIfCorrelationsNonzero=not unrestricted,
        exactOptimumCertified=upper == lower, boxBound=bound,
        fractionalDualCoordinates=len(free), seconds=time.monotonic()-started,
        matrixSHA256=hashlib.sha256(columns.tobytes()).hexdigest())


def experiment(order, seed, heights, cost_audit=False):
    import numpy as np
    from probe_riesz_joined_count_correlation import population
    from probe_riesz_complex_null_profiles import optimize, period_edge
    started = time.monotonic()
    pars, rows, excluded = population(order, {256: 8, 640: 16, 1536: 32}[order], seed)
    physical, endpoint = pars['physical'], max(r['label'] for r in rows)
    scale = max(r['log_amplitude'] for r in rows)
    weights = -np.exp([r['log_amplitude']-scale for r in rows])[None, :]*np.exp(
        -1j*np.asarray(heights)[:, None]*np.asarray([r['total'] for r in rows])[None, :])
    higher = np.asarray([r['count'] >= 4 for r in rows])
    moment = weights[:, higher].sum(axis=1)
    norms = np.abs(moment)
    axis_re = np.divide(moment.imag, norms, out=np.zeros_like(norms), where=norms != 0)
    axis_im = np.divide(moment.real, norms, out=np.zeros_like(norms), where=norms != 0)
    events = defaultdict(list)
    for i, row in enumerate(rows):
        for d, sign in row['divisors']:
            if d < endpoint:
                events[d].append((i, sign))
    points = sorted({1, physical, endpoint, *events})
    prefix = np.zeros(len(rows), dtype=np.int32)
    grouped = [defaultdict(lambda: np.zeros(9)) for _ in heights]
    totals = np.zeros((len(heights), 3), dtype=complex)
    coherent_intervals = 0
    for left, right in zip(points, points[1:]):
        for i, sign in events[left]:
            prefix[i] += sign
        phi = weights@prefix
        psi = weights[:, higher]@prefix[higher]
        orthogonal = axis_re*psi.real-axis_im*psi.imag
        # Exact arithmetic coherence: identical integer prefixes give
        # psi = c*M. Its determinant is mathematically zero, not a norm loss.
        if not higher.any() or np.all(prefix[higher] == prefix[higher][0]):
            orthogonal[:] = 0.
            coherent_intervals += 1
        lo, hi = math.log(left), math.log(right)
        vector = np.asarray([-(hi-lo) if left >= physical else 0., -(hi-lo),
                             -(hi*hi-lo*lo)/(order+1)])
        totals += phi[:, None]*vector
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
                # The baseline optimiser below needs all three COMPLEX
                # channels. The cube is conditioned exactly as in Lean.
                cubewidth = -(edge**3-cursor**3)/(order+1)**2
                grouped[ih][period] += np.r_[
                    phi[ih].real*widths, phi[ih].imag*widths, orthogonal[ih]*cubewidth,
                    psi[ih].real*cubewidth, psi[ih].imag*cubewidth]
                cursor, period = edge, period+1
    cases = []
    for ih, height in enumerate(heights):
        keys = sorted(grouped[ih])
        data = np.asarray([grouped[ih][c] for c in keys])
        base = np.column_stack((-data[:, 0], data[:, 3], -data[:, 1], data[:, 4],
                                -data[:, 2], data[:, 5]))
        fit = optimize(base, [1, 2, 3, 4, 5], 4., [0.]*5)
        p = np.asarray(fit['parameters'])
        t = -(base[:, 0]+base[:, 1:]@p)
        v = data[:, 6]
        assert abs(float(v.sum())) <= 1e-7*max(1., float(np.abs(v).sum()))
        first = keys.index(0)
        assert v[first] == 0.
        positive, negative = floating_step(t, v), floating_step(t, -v)
        best = max([positive, negative], key=lambda r: r['guaranteedGain'])
        threshold_positive, threshold_negative = threshold_step(t, v), threshold_step(t, -v)
        threshold_best = max([threshold_positive, threshold_negative],
                             key=lambda r: r['guaranteedGain'])
        # Hold the original imaginary tilt fixed. Reoptimise all six
        # exact null coefficients jointly, including the two cubic legs.
        # Every period (including zero margins) remains in the objective.
        joint_design = np.column_stack((base[:, 0]+p[0]*base[:, 1],
            base[:, 2:6], -data[:, 7], data[:, 8]))
        joint = optimize(joint_design, list(range(1, 7)), 4., [*p[1:], 0., 0.])
        joint_t = -(joint_design[:, 0]+joint_design[:, 1:]@np.asarray(joint['parameters']))
        joint_v = joint_t-t
        assert abs(float(joint_v.sum())) <= 1e-7*max(1., float(np.abs(joint_v).sum()))
        assert joint['rescaledCost'] <= fit['rescaledCost']+1e-7
        joint_threshold = threshold_step(t, joint_v)
        joint_parameters = np.asarray(joint['parameters'])
        lower_v = -base[:, 2:6]@(joint_parameters[:4]-p[1:])
        cubic_v = data[:, 7]*joint_parameters[4]-data[:, 8]*joint_parameters[5]
        assert np.allclose(joint_v, lower_v+cubic_v, rtol=1e-9, atol=1e-8)
        near = np.abs(t) <= joint_threshold['threshold']
        def near_debit(vv):
            return float(np.where(t < 0, np.maximum(vv, 0), np.maximum(-vv, 0))[near].sum())
        lower_z, cubic_z, joint_z = map(near_debit, [lower_v, cubic_v, joint_v])
        overlap = lower_z+cubic_z-joint_z
        variation = float((np.abs(lower_v)+np.abs(cubic_v)-np.abs(lower_v+cubic_v))[near].sum()/2)
        assert abs(overlap-variation) <= 1e-7*max(1., lower_z+cubic_z)
        lower_d, cubic_d = float(lower_v[t < 0].sum()), float(cubic_v[t < 0].sum())
        audit = exact_matrix_cost_audit(joint_design) if cost_audit else None
        cases.append(dict(height=height, periods=len(keys), countsJoined=True,
            rescaledBaselineCost=fit['rescaledCost'], signedLiteralReal=float(t.sum()),
            globalBaselineParameters=p.tolist(), baselineImaginaryTiltUnchanged=True,
            cubicSumError=float(v.sum()), firstWholePeriodCorrection=float(v[first]),
            positiveDirection=positive, negativeDirection=negative,
            bestGuaranteedGain=best['guaranteedGain'],
            bestGainFraction=best['gainFractionOfFiniteBaseline'],
            correctedRescaledCost=best['correctedCost'],
            thresholdPositive=threshold_positive, thresholdNegative=threshold_negative,
            thresholdBestGainFraction=threshold_best['gainFractionOfFiniteBaseline'],
            jointNullParameters=joint['parameters'], jointImaginaryTiltFixed=float(p[0]),
            jointNullParametersAreAbsoluteProfileCoordinates=True,
            jointCorrectionParameters=np.r_[joint_parameters[:4]-p[1:],
                                            joint_parameters[4:]].tolist(),
            jointAllPeriodCost=joint['rescaledCost'],
            exactFloatingMatrixCostAudit=audit,
            jointCostGainFraction=(1-joint['rescaledCost']/fit['rescaledCost'])
                if fit['rescaledCost'] else None,
            jointNullSumError=float(joint_v.sum()),
            jointThresholdStep=joint_threshold,
            jointCancellationAudit=dict(lowerSignedMarginal=lower_d-lower_z,
                cubicSignedMarginal=cubic_d-cubic_z, nearDebitCancellation=overlap,
                joinedSignedMarginal=lower_d+cubic_d-joint_z,
                cancellationIdentityError=abs(overlap-variation),
                measuredAfterJoiningAllCountsPeriods=True, nativeEstimateCertified=False)))
    return dict(N=order, seed=seed, selectedLabels=len(rows),
                originalCountCeiling={256: 8, 640: 16, 1536: 32}[order],
                eventualCanonicalCountCropApplied=False,
                nearCriticalCountCeilingAtThisEarlyOrder=1,
                counts=sorted({r['count'] for r in rows}), excluded=dict(excluded),
                commonCoherentIntervalsKilledExactly=coherent_intervals,
                sourceAmplitudeLogScale=scale, seconds=time.monotonic()-started, cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prime-probe', action='store_true')
    parser.add_argument('--cost-audit', action='store_true',
                        help='exact primal/dual replay of joined floating matrices, not primes')
    parser.add_argument('--orders', nargs='+', type=int, choices=[256, 640, 1536], default=[256])
    parser.add_argument('--seeds', nargs='+', type=int, default=[317])
    parser.add_argument('--heights', nargs='+', type=float, default=[54., 65., 100.])
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-quantitative-null-step/report.json'))
    args = parser.parse_args()
    if any(not math.isfinite(y) or y < 54 for y in args.heights):
        parser.error('finite heights >=54 required')
    if args.cost_audit and not args.prime_probe:
        parser.error('--cost-audit requires --prime-probe')
    report = dict(schemaVersion=1, head=subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], text=True).strip(), selfTest=self_test(), cases=[],
        scope=dict(outsideBuildsCI=True, nativeFloorCertified=False,
                   wholeNativePopulationEnumerated=False, probablePrimes=True,
                   eventualCanonicalCountCropApplied=False,
                   floatingPhases=True, largeCutoffsLogInterpolated=True,
                   commonAmplitudeRescaling=True, allSelectedCountsPeriodsRetained=True))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.prime_probe:
        import mpmath as mp
        mp.mp.dps = 100
        for order in args.orders:
            for seed in args.seeds:
                batch = experiment(order, seed, args.heights, args.cost_audit)
                report['cases'].append(batch)
                args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
                print(json.dumps(batch, allow_nan=False), flush=True)
    report['sourceSHA256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print(json.dumps(dict(selfTest=report['selfTest'], finitePrimeBatches=len(report['cases'])), indent=2))


if __name__ == '__main__':
    main()

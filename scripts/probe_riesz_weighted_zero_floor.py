#!/usr/bin/env python3
"""Optional joined complex/label-dependent zero-response diagnostic.

Reuse frozen factored-integer samples and exact IntegerGap classifications.
Keep original masks, sampling weights, factorial allocation and phases in
the base carrier. Compare the previous real/tilted zero direction, both
complex directions, and label-dependent complex coefficients. All counts
and cutoff periods are joined before pricing. No resampling, population
bound, native count-crop estimate, LP certificate or cofinal rate is claimed.
"""
import argparse
from collections import defaultdict
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import mpmath as mp
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, eye, hstack

from probe_riesz_complex_null_profiles import optimize, period_edge
from probe_riesz_zero_response_floor import frozen_rows


def label_fit(columns, initial, label_bound, extra_initial=None):
    """Keep the SAME bounds on every earlier null; widen only zero labels.

    Their bound makes the complete previous two-complex-column candidate
    feasible. Reprice it explicitly; no optimality claim is needed.
    """
    base, directions = columns[:, 0], columns[:, 1:]
    size = len(base)
    scale = max(float(np.max(np.abs(columns))), 1.)
    bounds = [(-4., 4.)]*7 + [(-label_bound, label_bound)]*(directions.shape[1]-7)
    result = linprog(np.r_[np.zeros(directions.shape[1]), np.ones(size)],
        A_ub=hstack((csr_matrix(directions/scale), -eye(size)), format='csr'),
        b_ub=-base/scale, bounds=bounds+[(0., None)]*size, method='highs')
    if not result.success:
        raise RuntimeError(result.message)
    initial = np.asarray(initial)
    assert all(lo-1e-8 <= v <= hi+1e-8 for v, (lo, hi) in zip(initial, bounds))
    candidates = [initial, np.zeros(len(initial)), result.x[:len(initial)]]
    if extra_initial is not None:
        extra_initial = np.asarray(extra_initial)
        assert all(lo-1e-8 <= v <= hi+1e-8 for v, (lo, hi) in zip(extra_initial, bounds))
        candidates.append(extra_initial)
    best = min(candidates, key=lambda v: float(np.maximum(base+directions@v, 0.).sum()))
    return dict(parameters=best.tolist(),
        rescaledCost=float(np.maximum(base+directions@best, 0.).sum()),
        joinedSignedTotal=float((base+directions@best).sum()),
        labelCoefficientBound=label_bound, earlierNullCoefficientBound=4.)


def experiment(order, seed, heights, closed_tail=False, previous=None):
    pars, rows, cached = frozen_rows(order, seed)
    physical, endpoint = pars['physical'], max(r['label'] for r in rows)
    closed_events = defaultdict(list)
    for i, row in enumerate(rows):
        pp = sorted(row['primes'])
        block = pp[0]*pp[1]
        ds = [(1, 1)]
        for p in pp[2:]:
            ds += [(d*p, -mu) for d, mu in ds]
        terms = [(d*e, mu*nu) for d, mu in ds if physical <= d
                 for e, nu in [(1, 1), (pp[0], -1), (pp[1], -1), (block, 1)]]
        assert len({d for d, _ in terms}) == len(terms)
        assert all(d in {x for x, _ in row['divisors']} for d, _ in terms)
        row['closedTail'] = bool(terms)
        row['correctionSelected'] = row['closedTail'] if closed_tail else row['integerGap']
        if closed_tail:
            for d, mu in terms:
                if d < endpoint:
                    closed_events[d].append((i, mu))
    zero_labels = sorted({r['label'] for r in rows if r['correctionSelected']})
    zero_index = {n: i for i, n in enumerate(zero_labels)}
    whole_zero_mask = np.asarray([next(r['integerGap'] for r in rows if r['label']==n)
                                 for n in zero_labels])
    closed_prefix = np.zeros(len(rows), dtype=np.int32)
    amplitude = np.asarray([r['amplitude'] for r in rows])
    totals = np.asarray([r['total'] for r in rows])
    weights = -amplitude[None, :]*np.exp(-1j*np.asarray(heights)[:, None]*totals[None, :])
    zero = np.asarray([r['integerGap'] for r in rows])
    higher = np.asarray([r['count'] >= 4 for r in rows])
    events = defaultdict(list)
    for i, row in enumerate(rows):
        for d, sign in row['divisors']:
            if d < endpoint:
                events[d].append((i, sign))
    points = sorted({1, physical, endpoint, *events, *closed_events})
    prefix = np.zeros(len(rows), dtype=np.int32)
    grouped = [defaultdict(lambda: np.zeros(6, dtype=complex)) for _ in heights]
    labels = [defaultdict(lambda: np.zeros(len(zero_labels))) for _ in heights]
    for left, right in zip(points, points[1:]):
        for i, sign in events[left]:
            prefix[i] += sign
        for i, sign in closed_events[left]:
            closed_prefix[i] += sign
        phi, psi, zerophi = weights@prefix, weights[:, higher]@prefix[higher], weights[:, zero]@prefix[zero]
        # One coefficient per INTEGER label, including repeated samples.
        # The null coefficient exp(i*y*log n) undoes phase only in the
        # exact ZERO correction. The base carrier keeps its original phase.
        shapes = np.zeros(len(zero_labels))
        for i, row in enumerate(rows):
            if row['correctionSelected']:
                response = closed_prefix[i] if closed_tail else prefix[i]
                shapes[zero_index[row['label']]] -= amplitude[i]*response
        lo, hi = math.log(left), math.log(right)
        for ih, height in enumerate(heights):
            unit, cursor = 2*math.pi/height, lo
            period = math.floor(cursor/unit)
            while cursor < hi:
                edge = min(hi, period_edge(period, unit))
                if edge <= cursor:
                    period += 1
                    continue
                widths = np.asarray([-(edge-cursor) if left >= physical else 0.,
                    -(edge-cursor), -(edge**2-cursor**2)/(order+1)])
                cube = -(edge**3-cursor**3)/(order+1)**2
                grouped[ih][period] += np.r_[phi[ih]*widths, psi[ih]*cube,
                    phi[ih]*cube, zerophi[ih]*widths[0]]
                labels[ih][period] += shapes*widths[0]
                cursor, period = edge, period+1
    label_logs = np.asarray([math.log(n) for n in zero_labels])
    cases = []
    for ih, height in enumerate(heights):
        periods = sorted(grouped[ih])
        data = np.asarray([grouped[ih][p] for p in periods])
        label_columns = np.asarray([labels[ih][p] for p in periods])
        literal = sum(weights[ih, i]*r['response'] for i, r in enumerate(rows))
        tolerance = 2e-7*max(1., float(np.abs(data).sum()))
        assert abs(data[:, 0].sum()-literal) <= tolerance
        assert np.max(np.abs(label_columns.sum(axis=0))) <= tolerance
        phase = np.exp(-1j*height*label_logs)
        assert np.max(np.abs(label_columns@(phase*whole_zero_mask)-data[:, 5])) <= tolerance
        base = np.column_stack((-data[:, 0].real, data[:, 0].imag,
            -data[:, 1].real, data[:, 1].imag, -data[:, 2].real, data[:, 2].imag))
        original = optimize(base, list(range(1, 6)), 4., [0.]*5)
        p = np.asarray(original['parameters'])
        moment = -6*sum(weights[ih, i]*math.prod(math.log(p) for p in r['primes'])
            for i, r in enumerate(rows) if r['count'] == 3)/(order+1)**2
        assert abs(data[:, 4].sum()-moment) <= tolerance
        axis = np.asarray([moment.imag, moment.real])/abs(moment) if moment else np.zeros(2)
        tangent = axis[0]*data[:, 4].real-axis[1]*data[:, 4].imag
        design = np.column_stack((base[:, 0]+p[0]*base[:, 1], base[:, 2:6],
            -data[:, 3].real, data[:, 3].imag, -tangent))
        old = optimize(design, list(range(1, 8)), 4., [*p[1:], 0., 0., 0.])
        direction = data[:, 5].real-p[0]*data[:, 5].imag
        one_columns = np.column_stack((design, direction))
        one = optimize(one_columns, list(range(1, 9)), 4., [*old['parameters'], 0.])
        two_columns = np.column_stack((one_columns, data[:, 5].imag))
        two = optimize(two_columns, list(range(1, 10)), 4., [*one['parameters'], 0.])
        r, extra_imaginary = two['parameters'][-2:]
        imaginary = r*p[0]-extra_imaginary
        label_initial = (r*np.cos(height*label_logs)+imaginary*np.sin(height*label_logs))*whole_zero_mask
        full_columns = np.column_stack((design, label_columns))
        initial = np.r_[two['parameters'][:7], label_initial]
        candidate_two = two_columns[:, 0]+two_columns[:, 1:]@np.asarray(two['parameters'])
        candidate_labels = full_columns[:, 0]+full_columns[:, 1:]@initial
        assert np.max(np.abs(candidate_two-candidate_labels)) <= tolerance
        previous_initial = None
        previous_price = None
        previous_residual = None
        if previous is not None:
            prior = next(c for c in previous['cases'] if c['height']==height)
            prior_coefficients = dict(zip(previous['correctionLabels'], prior['labelCoefficients']))
            assert set(prior_coefficients) <= {str(n) for n in zero_labels}
            previous_initial = np.r_[prior['earlierRebalancedCoefficients'],
                [prior_coefficients.get(str(n), 0.) for n in zero_labels]]
            repriced = float(np.maximum(full_columns[:, 0]+full_columns[:, 1:]@previous_initial, 0.).sum())
            previous_price = prior['labelDependentZeroPrice']
            previous_residual = abs(repriced-previous_price)
            assert previous_residual <= tolerance
        fitted = label_fit(full_columns, initial, 8+4*abs(p[0]), previous_initial)
        assert fitted['rescaledCost'] <= two['rescaledCost']+tolerance
        assert two['rescaledCost'] <= one['rescaledCost']+tolerance
        cases.append(dict(height=height, completePeriods=len(data),
            previousRealZeroPrice=one['rescaledCost'], complexZeroPrice=two['rescaledCost'],
            complexZeroGain=one['rescaledCost']-two['rescaledCost'],
            labelDependentZeroPrice=fitted['rescaledCost'],
            labelDependentGain=two['rescaledCost']-fitted['rescaledCost'],
            allZeroCoefficientsFreeByExactResponse=True,
            imaginaryTiltUnchanged=float(p[0]), earlierNullBoundUnchanged=4.,
            noNativePaidOwnerPacketAppliedAtTheseSampleOrders=True,
            floatingLabelZeroResidual=float(np.max(np.abs(label_columns.sum(axis=0)))),
            literalEmbeddingResidual=float(np.max(np.abs(candidate_two-candidate_labels))),
            complexCoefficients=two['parameters'],
            labelCoefficients=fitted['parameters'][7:],
            earlierRebalancedCoefficients=fitted['parameters'][:7],
            labelCoefficientBound=fitted['labelCoefficientBound']))
        if previous_price is not None:
            cases[-1].update(previousWeightedLabelPrice=previous_price,
                previousWeightedCandidateRepricingResidual=previous_residual,
                extraClosedTailGain=previous_price-fitted['rescaledCost'])
    return dict(N=order, seed=seed, cache=cached, labels=len(rows),
        closedTailMode=closed_tail, correctionLabels=[str(n) for n in zero_labels],
        correctionLabelsWithWholeZeroResponse=int(whole_zero_mask.sum()),
        correctionIncludesNonzeroWholeResponse=closed_tail and any(
            r['correctionSelected'] and not r['integerGap'] for r in rows), cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', choices=[32, 64], default=[32, 64])
    parser.add_argument('--seeds', type=int, nargs='+', choices=[317, 919], default=[317, 919])
    parser.add_argument('--heights', type=float, nargs='+', default=[54., 65., 100.])
    parser.add_argument('--closed-tail', action='store_true', help='Use complete affine tails inside all original labels.')
    parser.add_argument('--previous', type=Path, default=Path('.lake/riesz-complex-zero/probe.json'),
                        help='Frozen earlier weighted-zero report, repriced as a feasible candidate in closed-tail mode.')
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-complex-zero/probe.json'))
    args = parser.parse_args()
    if any(not math.isfinite(y) or y < 54 for y in args.heights):
        parser.error('finite heights >=54 required')
    mp.mp.dps = 100
    prior = json.loads(args.previous.read_text()) if args.closed_tail else None
    report = dict(schemaVersion=1, cases=[], scope=dict(optionalOutsideBuildsCI=True,
        originalFrozenSamplesAndImportanceWeights=True, exactIntegerGapClassifications=True,
        allCountsPeriodsAndOriginalBasePhasesJoined=True,
        coefficientPhaseCancellationOnlyInExactZeroCorrection=True,
        earlierNullBoundsAndImaginaryTiltRetained=True,
        previousComplexFitReplayedAsFeasibleLabelCandidate=True,
        probablePrimalityFloatingPhasesEdgesAndLP=True,
        nativeCofinalPoints=False, nativeCountCropApplied=False,
        independentlyPaidNativeOwnerPacketApplied=False,
        closedTailMode=args.closed_tail, wholeResponseZeroRequired=not args.closed_tail,
        nativePricePopulationRateOrDeficitBound=False, wholeFloorProved=False))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for order in args.orders:
        for seed in args.seeds:
            previous = next(b for b in prior['cases'] if (b['N'],b['seed'])==(order,seed)) if prior else None
            batch = experiment(order, seed, args.heights,args.closed_tail,previous)
            report['cases'].append(batch)
            args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
            print(json.dumps(dict(N=order,seed=seed,correctionLabels=len(batch['correctionLabels']),
                cases=[{k:c[k] for k in ('height','previousRealZeroPrice',
                    'complexZeroPrice','complexZeroGain','labelDependentZeroPrice',
                    'labelDependentGain')} for c in batch['cases']]),allow_nan=False),flush=True)


if __name__ == '__main__':
    main()

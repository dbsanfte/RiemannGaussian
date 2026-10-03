#!/usr/bin/env python3
"""Optional exact-gap/whole-price probe, outside builds and CI.

Reuse frozen factored-integer samples. The gap test compares integers, never
floating Riesz coefficients. Keep the full original masks, allocation and
complex phase, with the existing sampling importance weights. Join every
count and every complete cutoff period before pricing. Compare both the raw
profile and the earlier complex/cubic null fit with its tilt held fixed.

Probable primality, floating phases, interpolated large cutoff edges and LP
solutions are diagnostics. These small orders are NOT native cofinal points;
no price, density, rate, deficit percentage or floor is certified.
"""
import argparse
from collections import defaultdict
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True

import mpmath as mp
import numpy as np

from probe_riesz_complex_null_profiles import optimize, period_edge
from probe_riesz_factored_population import atom, parameters


def integer_gap(physical, primes):
    """Literal IntegerGap(physical, product(primes), leastPairBlock)."""
    primes = sorted(primes)
    block = primes[0]*primes[1]
    divisors = [1]
    for p in primes[2:]:
        divisors += [d*p for d in divisors]
    return all(physical <= d or d*block <= physical for d in divisors)


def frozen_rows(order, seed):
    path = Path(f'.lake/riesz-factored-population/inputs/N{order}-seed{seed}-M512-bins16.json')
    data = json.loads(path.read_text())
    pars = parameters(order, 16)
    assert [str(e) for e in pars['edges']] == data['edges']
    rows = []
    for draw in data['draws']:
        label = int(draw['label'])
        factors = {int(p): e for p, e in draw['factors'].items()}
        assert label == math.prod(p**e for p, e in factors.items())
        low, high = pars['edges'][draw['cell']:draw['cell']+2]
        assert low < label <= high
        row, _ = atom(order, 16, pars, label, factors,
                      math.log(16)+math.log(high-low)-math.log(512))
        if row is not None:
            row['integerGap'] = integer_gap(pars['physical'], row['primes'])
            rows.append(row)
    return pars, rows, dict(path=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest())


def experiment(order, seed, heights):
    pars, rows, cached = frozen_rows(order, seed)
    physical, endpoint = pars['physical'], max(r['label'] for r in rows)
    weights = -np.asarray([r['amplitude'] for r in rows])[None, :]*np.exp(
        -1j*np.asarray(heights)[:, None]*np.asarray([r['total'] for r in rows])[None, :])
    zero = np.asarray([r['integerGap'] for r in rows])
    higher = np.asarray([r['count'] >= 4 for r in rows])
    events = defaultdict(list)
    for i, row in enumerate(rows):
        for d, sign in row['divisors']:
            if d < endpoint:
                events[d].append((i, sign))
    points = sorted({1, physical, endpoint, *events})
    prefix = np.zeros(len(rows), dtype=np.int32)
    grouped = [defaultdict(lambda: np.zeros(6, dtype=complex)) for _ in heights]
    for left, right in zip(points, points[1:]):
        for i, sign in events[left]:
            prefix[i] += sign
        phi = weights@prefix
        psi = weights[:, higher]@prefix[higher]
        zerophi = weights[:, zero]@prefix[zero]
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
                    -(edge-cursor), -(edge*edge-cursor*cursor)/(order+1)])
                cube = -(edge**3-cursor**3)/(order+1)**2
                grouped[ih][period] += np.r_[phi[ih]*widths, psi[ih]*cube,
                                            phi[ih]*cube, zerophi[ih]*widths[0]]
                cursor, period = edge, period+1
    cases = []
    for ih, height in enumerate(heights):
        data = np.asarray([grouped[ih][p] for p in sorted(grouped[ih])])
        literal = sum(weights[ih, i]*r['response'] for i, r in enumerate(rows))
        tolerance = 2e-7*max(1., float(np.abs(data).sum()))
        assert abs(data[:, 0].sum()-literal) <= tolerance
        assert abs(data[:, 5].sum()) <= tolerance
        assert float(np.max(np.abs(data[:, 1:4].sum(axis=0)))) <= tolerance
        raw = float(np.maximum(-data[:, 0].real, 0).sum())
        cleared_raw = float(np.maximum(-(data[:, 0].real-data[:, 5].real), 0).sum())
        base = np.column_stack((-data[:, 0].real, data[:, 0].imag,
            -data[:, 1].real, data[:, 1].imag, -data[:, 2].real, data[:, 2].imag))
        original = optimize(base, list(range(1, 6)), 4., [0.]*5)
        p = np.asarray(original['parameters'])
        moment = -6*sum(weights[ih, i]*math.prod(math.log(p) for p in r['primes'])
                       for i, r in enumerate(rows) if r['count'] == 3)/(order+1)**2
        assert abs(data[:, 4].sum()-moment) <= tolerance
        axis = np.asarray([moment.imag, moment.real])/abs(moment) if moment else np.zeros(2)
        tangent = axis[0]*data[:, 4].real-axis[1]*data[:, 4].imag
        assert abs(tangent.sum()) <= tolerance
        design = np.column_stack((base[:, 0]+p[0]*base[:, 1], base[:, 2:6],
            -data[:, 3].real, data[:, 3].imag, -tangent))
        fit = optimize(design, list(range(1, 8)), 4., [*p[1:], 0., 0., 0.])
        old_objective = design[:, 0]+design[:, 1:]@np.asarray(fit['parameters'])
        # Tilt and ALL old null increments remain unchanged. Only the
        # certified zero-label BASE profile is removed, matching Lean.
        zero_direction = data[:, 5].real-p[0]*data[:, 5].imag
        cleared = float(np.maximum(old_objective+zero_direction, 0).sum())
        signed_residual = float(abs(zero_direction.sum()))
        assert signed_residual <= tolerance
        kept_cost = min(fit['rescaledCost'], cleared)
        assert kept_cost <= fit['rescaledCost']+tolerance
        difference = float(fit['rescaledCost']-cleared)
        variation_difference = (float(np.abs(old_objective).sum())-
                                float(np.abs(old_objective+zero_direction).sum()))/2
        assert abs(difference-variation_difference) <= tolerance
        # A deleted zero response can be USEFUL to the earlier null fit.
        # Join its signed direction with every old null before pricing,
        # rather than fixing removal at coefficient one.
        augmented = np.column_stack((design, zero_direction))
        joined_fit = optimize(augmented, list(range(1, 9)), 4.,
                              [*fit['parameters'], 0.])
        assert joined_fit['rescaledCost'] <= fit['rescaledCost']+tolerance
        cases.append(dict(height=height, completePeriods=len(data),
            rawPeriodCost=raw, zeroClearedRawCost=cleared_raw,
            rawGain=raw-cleared_raw,
            previousComplexCubicPrice=fit['rescaledCost'],
            zeroClearedWithSameTiltAndNulls=cleared, retainedPrice=kept_cost,
            exactZeroFundingCost=0, additionalFiniteGain=fit['rescaledCost']-kept_cost,
            zeroDirectionFloatingSumResidual=signed_residual,
            signedVariationIdentityResidual=abs(difference-variation_difference),
            imaginaryTiltUnchanged=float(p[0]), forcedDeletionEarlierNullCoefficientsUnchanged=True,
            finiteCoefficients=fit['parameters'],
            joinedZeroDirectionPrice=joined_fit['rescaledCost'],
            joinedZeroDirectionGain=fit['rescaledCost']-joined_fit['rescaledCost'],
            joinedZeroDirectionCoefficients=joined_fit['parameters'],
            jointSignedNullRebalanceRequired=True,
            joinedFitKeepsEarlierNullDirectionsButRebalancesCoefficients=True))
    return dict(N=order, seed=seed, samples=512, bins=16, K=16, cache=cached,
        labels=len(rows), integerGapSelectedLabels=int(zero.sum()),
        survivors=len(rows)-int(zero.sum()),
        integerGapTestUsesNoFloatingResponse=True,
        maximumFloatingZeroResponse=max([abs(r['response']) for r in rows if r['integerGap']] or [0]),
        cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', choices=[32, 64], default=[32, 64])
    parser.add_argument('--seeds', type=int, nargs='+', choices=[317, 919], default=[317, 919])
    parser.add_argument('--heights', type=float, nargs='+', default=[54., 65., 100.])
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-zero-response/probe.json'))
    args = parser.parse_args()
    if any(not math.isfinite(y) or y < 54 for y in args.heights):
        parser.error('finite heights >=54 required')
    mp.mp.dps = 100
    report = dict(schemaVersion=1, cases=[], scope=dict(optionalOutsideBuildsCI=True,
        frozenFactoredIntegerSamples=True, samplingImportanceWeightsRetained=True,
        exactIntegerGapTests=True, exactPrimalityOracleAssumedByIdealSampler=True,
        probablePrimalityUncertified=True, floatingPhasesAndLPEstimates=True,
        largePeriodEdgesInterpolated=True, nativeCofinalPoints=False,
        deterministicPriceBound=False, cofinalRateProved=False, wholeFloorProved=False))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for order in args.orders:
        for seed in args.seeds:
            batch = experiment(order, seed, args.heights)
            report['cases'].append(batch)
            args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
            print(json.dumps(dict(N=order, seed=seed, zeros=batch['integerGapSelectedLabels'],
                cases=[{k:c[k] for k in ('height','rawGain','previousComplexCubicPrice',
                    'zeroClearedWithSameTiltAndNulls','additionalFiniteGain',
                    'joinedZeroDirectionPrice','joinedZeroDirectionGain')}
                    for c in batch['cases']]), allow_nan=False), flush=True)


if __name__ == '__main__':
    main()

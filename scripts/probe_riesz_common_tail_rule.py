#!/usr/bin/env python3
"""Optional out-of-sample common-rule test for literal closed-tail nulls.

Reuse the UNCHANGED weighted-zero probe to build the original joined
period matrices, and keep its frozen factorizations/masks/importance weights
and fixed imaginary tilt. Compare common rules with label-specific fits.
Cross-seed coefficients are replayed, never fitted on the test population.
No cofinal/native floor, primality, LP or period-edge certificate is claimed.
The sampled orders are not native dyadic points. Outside builds and CI.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import mpmath as mp
import numpy as np

import probe_riesz_weighted_zero_floor as weighted
from probe_riesz_complex_null_profiles import optimize


def price(base, directions, coefficients):
    return float(np.maximum(base+directions@np.asarray(coefficients), 0.).sum())


def capture(order, seed, heights, directory):
    """Capture matrices at the existing LP interface, without changing it."""
    matrices = []
    original = weighted.label_fit

    def observer(columns, initial, label_bound, extra_initial=None):
        matrices.append(np.asarray(columns).copy())
        return original(columns, initial, label_bound, extra_initial)

    prior_report = json.loads(Path('.lake/riesz-complex-zero/probe.json').read_text())
    prior = next(b for b in prior_report['cases'] if (b['N'],b['seed'])==(order,seed))
    weighted.label_fit = observer
    try:
        batch = weighted.experiment(order, seed, heights, True, prior)
    finally:
        weighted.label_fit = original
    _, rows, cache = weighted.frozen_rows(order, seed)
    labels = [int(n) for n in batch['correctionLabels']]
    by_label = {r['label']: r for r in rows}
    selected = [by_label[n] for n in labels]
    totals = np.asarray([r['total'] for r in selected])
    geometry = np.asarray([[1., float(r['count'] >= 4),
        5*(r['owner']-.5),
        2*math.log(math.prod(sorted(r['primes'])[:2]))/r['total'],
        (r['total']/order-1.99)/.04] for r in selected])
    assert np.max(np.abs(geometry)) <= 2.
    output = []
    for c, matrix in zip(batch['cases'], matrices):
        height = c['height']
        trig = np.column_stack((np.cos(height*totals), np.sin(height*totals)))
        features = dict(
            phaseAlignedConstant=np.ones((len(labels),1)),
            originalPhaseComplex=trig,
            countPhaseComplex=np.column_stack((trig,trig*geometry[:,1:2])),
            geometryPhaseComplex=np.column_stack([trig*geometry[:,i:i+1]
                for i in range(geometry.shape[1])]),
        )
        tail = matrix[:,8:]
        whole_zero = np.asarray([r['integerGap'] for r in selected])
        old_zero_features = np.column_stack((
            (trig[:,0]+c['imaginaryTiltUnchanged']*trig[:,1])*whole_zero,
            -trig[:,1]*whole_zero))
        old_matrix = np.column_stack((matrix[:,:8],tail@old_zero_features))
        old_directions = old_matrix[:,1:]
        old_coefficients = np.asarray(c['complexCoefficients'])
        baseline = matrix[:,0]+old_directions@old_coefficients
        assert abs(float(np.maximum(baseline,0.).sum())-c['complexZeroPrice']) < 1e-9
        out = dict(N=order,seed=seed,height=height,
            labelDependentPrice=c['labelDependentZeroPrice'],
            beforeTailPrice=price(matrix[:,0],old_directions,old_coefficients),
            tilt=c['imaginaryTiltUnchanged'],closedLabels=len(labels),
            originalEarlierCoefficients=old_coefficients.tolist(),
            signedTotal=float(baseline.sum()),rules={})
        for name, feature in features.items():
            # Fit only common tail coefficients; keep earlier nulls intact.
            direction = tail@feature
            design = np.column_stack((baseline,direction))
            fit = optimize(design,list(range(1,design.shape[1])),4.,[0.]*direction.shape[1])
            # Also join/rebalance every earlier null, with its original bounds.
            joined = np.column_stack((old_matrix,direction))
            initial = [*old_coefficients,*fit['parameters']]
            joined_fit = optimize(joined,list(range(1,joined.shape[1])),4.,initial)
            out['rules'][name] = dict(fixedEarlierPrice=fit['rescaledCost'],
                fixedEarlierCoefficients=fit['parameters'],
                joinedPrice=joined_fit['rescaledCost'],
                joinedCommonCoefficients=joined_fit['parameters'][9:],
                joinedEarlierCoefficients=joined_fit['parameters'][:9],
                nullTotalResidual=float(np.max(np.abs(direction.sum(axis=0)))))
        deterministic = trig[:,0]+c['imaginaryTiltUnchanged']*trig[:,1]
        out['deterministicTailDeletionPrice'] = price(baseline,tail,deterministic)
        archive = directory/f'N{order}-seed{seed}-y{height:g}.npz'
        np.savez_compressed(archive,matrix=matrix,oldMatrix=old_matrix,
            geometry=geometry,totals=totals,
            **features)
        out['matrixArtifact'] = dict(path=str(archive),
            sha256=hashlib.sha256(archive.read_bytes()).hexdigest())
        out['frozenInput'] = cache
        output.append(out)
    return output


def cross_seed(cases):
    """One geometry rule fitted on a different frozen population.

    The test price with its prior nulls held fixed is the strict replay.
    Separately rebalancing ONLY old nulls tests compatibility, not prediction
    of their coefficients. Both original and zero-rule candidates retained.
    """
    for test in cases:
        train = next(c for c in cases if c['N']==test['N'] and
            c['height']==test['height'] and c['seed']!=test['seed'])
        archive = np.load(test['matrixArtifact']['path'])
        matrix = archive['matrix']
        old = archive['oldMatrix'][:,1:]
        # No tail coefficient is refitted on the target population.
        for name, rule in test['rules'].items():
            coefficients = train['rules'][name]['joinedCommonCoefficients']
            correction = matrix[:,8:]@archive[name]@np.asarray(coefficients)
            before = test['beforeTailPrice']
            fixed = np.asarray(test['originalEarlierCoefficients'])
            replay = float(np.maximum(matrix[:,0]+old@fixed+correction,0.).sum())
            rebalanced = optimize(np.column_stack((matrix[:,0]+correction,old)),
                list(range(1,10)),4.,fixed.tolist())
            rule['crossSeed'] = dict(trainingSeed=train['seed'],
                commonCoefficients=coefficients,strictReplayPrice=replay,
                rebalancedEarlierPrice=rebalanced['rescaledCost'],
                retainedPrice=min(before,rebalanced['rescaledCost']),
                noTargetTailCoefficientFitting=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders',type=int,nargs='+',choices=[32,64],default=[32,64])
    parser.add_argument('--heights',type=float,nargs='+',default=[54.,65.,100.])
    parser.add_argument('--output',type=Path,default=Path('.lake/riesz-common-tail/probe.json'))
    args = parser.parse_args()
    if any(not math.isfinite(y) or y<54 for y in args.heights):
        parser.error('finite heights >=54 required')
    mp.mp.dps = 100
    directory = args.output.parent
    directory.mkdir(parents=True,exist_ok=True)
    cases = []
    for order in args.orders:
        for seed in (317,919):
            cases += capture(order,seed,args.heights,directory)
            print(json.dumps(dict(N=order,seed=seed,cases=cases[-len(args.heights):]),
                allow_nan=False),flush=True)
    cross_seed(cases)
    report = dict(schemaVersion=1,cases=cases,scope=dict(
        optionalOutsideBuildsCI=True,originalFrozenLabelsMasksAndWeights=True,
        fullOriginalBasePhasesRetained=True,commonRuleOnlyActsOnExactNull=True,
        allCountsAndCutoffPeriodsJoined=True,previousNullsRetainedAndFundedOnce=True,
        crossSeedTrainingAndTestPopulationsDistinct=True,
        probablePrimesFloatingPhasesPeriodEdgesAndLP=True,
        nativeCofinalPoints=False,nativePaidOwnerPacketApplied=False,
        cofinalPriceOrFloorProved=False))
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')


if __name__=='__main__':
    main()

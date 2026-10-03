#!/usr/bin/env python3
"""Optional exact-crossing rule for the unchanged frozen whole-floor matrices.

Here 'exact crossing' means the piecewise-linear cost formula, evaluated
in floating arithmetic; it is NOT an interval or Lean certificate. Read
the current joined sign pattern, form the already-proved signed feedback
direction, and choose a weighted median of its actual crossing roots.
Keep every zero face, previous null, phase, importance weight and base row.
No LP, per-label fit, population deletion or cofinal rate is asserted.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import mpmath as mp
import numpy as np
from scipy.linalg import null_space
from probe_riesz_zero_response_floor import frozen_rows


def checked(path, digest):
    path = Path(path)
    assert hashlib.sha256(path.read_bytes()).hexdigest() == digest
    return path


def median_step(t, direction):
    active = direction != 0
    if not active.any():
        return 0.
    roots = -t[active]/direction[active]
    weights = np.abs(direction[active])
    order = np.argsort(roots, kind='stable')
    cumulative = np.cumsum(weights[order])
    pivot = np.searchsorted(cumulative, weights.sum()/2)
    return float(roots[order[min(pivot, len(order)-1)]])


def direction_candidates(t, columns, project_near):
    yield columns, False, 0.
    if project_near:
        for fraction in (1e-10, 1e-7, 1e-5, 1e-3, 1e-2):
            tau = fraction*max(np.abs(t), default=0.)
            near = np.abs(t) <= tau
            projection = null_space(columns[near], rcond=1e-11)
            # No zero-face equality is inferred from this floating SVD.
            # The full changed-row cost below includes every residual.
            yield columns@projection, True, float(tau)


def candidate(t, columns, projected, projection_tau):
    correlation = columns.T@(t > 0)
    direction = -columns@correlation
    signed_flux = float(-direction[t > 0].sum())
    square_flux = float(np.square(correlation).sum())
    assert abs(signed_flux-square_flux) < 1e-7
    best_quad = dict(credit=0., step=0., tau=0., debit=0.)
    for tau in np.r_[0., np.geomspace(1e-8, 1e-2, 19)*max(np.abs(t), default=0.)]:
        near = np.abs(t) <= tau
        debit = float(np.where(t[near] > 0, np.maximum(-direction[near], 0.),
            np.maximum(direction[near], 0.)).sum())
        far = ~near
        quadratic = float((np.square(direction[far])/(4*np.abs(t[far]))).sum())
        available = max(signed_flux-debit, 0.)
        credit = available**2/(4*quadratic) if quadratic > 0 else 0.
        if credit > best_quad['credit']:
            best_quad = dict(credit=credit, step=available/(2*quadratic),
                tau=float(tau), debit=debit)
    middle = median_step(t, direction)
    # The exact theorem optimizes over every real step. In floats retain
    # zero/the old guaranteed step as explicit alternatives as well.
    proposals = (0., middle, best_quad['step'])
    step = min(proposals, key=lambda a: float(np.maximum(t+a*direction, 0.).sum()))
    after = t+step*direction
    old_cost = float(np.maximum(t, 0.).sum())
    new_cost = float(np.maximum(after, 0.).sum())
    actual_gain = old_cost-new_cost
    assert actual_gain+1e-10 >= best_quad['credit']
    # Exact signed identity in the cost-object sign convention.
    crossing = float(np.where(t > 0, np.maximum(-after, 0.),
        np.maximum(after, 0.)).sum())
    assert abs(actual_gain-(step*signed_flux-crossing)) < 1e-8
    # A finite numerical diagnostic for the weighted-median certificate.
    active = direction != 0
    roots = -t[active]/direction[active]
    mass = np.abs(direction[active])
    tolerance = 1e-12*max(1., abs(middle))
    lower = float(mass[roots < middle-tolerance].sum())
    upper = float(mass[roots > middle+tolerance].sum())
    assert 2*lower <= mass.sum()+1e-8 and 2*upper <= mass.sum()+1e-8
    return dict(direction=direction, after=after, actualGain=actual_gain,
        beforeCost=old_cost, afterCost=new_cost, stepSize=step,
        weightedMedian=middle, projectedNearRows=projected,
        projectionThreshold=projection_tau, retainedDirections=columns.shape[1],
        signedCorrelation=signed_flux, squaredCorrelation=square_flux,
        actualJoinedCrossingCost=crossing, priorThreshold=best_quad['tau'],
        priorNearDebit=best_quad['debit'], priorGuaranteedCredit=best_quad['credit'],
        medianLowerWeight=lower, medianUpperWeight=upper,
        medianTotalWeight=float(mass.sum()))


def experiment(case, steps, project_near, column_audit):
    path = checked(case['matrixArtifact']['path'], case['matrixArtifact']['sha256'])
    checked(case['frozenInput']['path'], case['frozenInput']['sha256'])
    archive = np.load(path)
    old = archive['oldMatrix']
    t = old[:, 0]+old[:, 1:]@np.asarray(case['originalEarlierCoefficients'])
    columns = archive['matrix'][:, 8:]
    audited_counts = None
    if column_audit:
        pars, rows, _ = frozen_rows(case['N'], case['seed'])
        labels = {r['label']: r for r in rows}
        selected = sorted(n for n, r in labels.items() if
            n//(sorted(r['primes'])[0]*sorted(r['primes'])[1]) >= pars['physical'])
        assert len(selected) == columns.shape[1]
        keep = np.asarray([labels[n]['owner'] < 60069/100000 and
            sorted(labels[n]['primes'])[1] > case['N']**3 for n in selected])
        columns = columns[:, keep]
        audited_counts = {str(k): sum(labels[n]['count'] == k for n, b in zip(selected, keep) if b)
            for k in sorted({labels[n]['count'] for n, b in zip(selected, keep) if b})}
    retained = columns.shape[1]
    norms = np.square(columns).sum(axis=0)
    active = norms > 0
    columns = columns[:, active]/np.sqrt(norms[active])
    assert np.max(np.abs(columns.sum(axis=0)), initial=0.) < 1e-7
    initial, total = float(np.maximum(t, 0.).sum()), float(t.sum())
    records = []
    for stage in range(steps):
        choices = [candidate(t, z, p, tau)
            for z, p, tau in direction_candidates(t, columns, project_near)]
        best = max(choices, key=lambda c: c['actualGain'])
        t = best.pop('after')
        best.pop('direction')
        best['stage'] = stage
        records.append(best)
        assert abs(float(t.sum())-total) < 1e-8
    final = float(np.maximum(t, 0.).sum())
    credit = sum(c['actualGain'] for c in records)
    assert abs(final+credit-initial) < 1e-8
    return dict(N=case['N'], seed=case['seed'], height=case['height'],
        projectNear=project_near, columnGeometryAudit=column_audit,
        retainedCorrectionLabels=retained, auditedCorrectionCounts=audited_counts,
        initialPrice=initial, finalPrice=final, accumulatedActualCredit=credit,
        creditFraction=credit/initial, stepCount=steps,
        priorFormulaCreditOnSameSuccessiveStates=sum(c['priorGuaranteedCredit'] for c in records),
        unavoidableSignedPrice=max(total, 0.), excessOverSignedTotal=final-max(total, 0.),
        signedTotal=total, signedTotalResidual=float(t.sum())-total,
        steps=records, matrixArtifact=case['matrixArtifact'], frozenInput=case['frozenInput'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=Path('.lake/riesz-common-tail/probe.json'))
    parser.add_argument('--steps', type=int, default=12)
    parser.add_argument('--project-near', action='store_true')
    parser.add_argument('--column-geometry-audit', action='store_true')
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-tail-median/probe.json'))
    args = parser.parse_args()
    if args.steps < 0:
        parser.error('nonnegative step count required')
    mp.mp.dps = 100
    report = json.loads(args.input.read_text())
    cases = []
    for c in report['cases']:
        case = experiment(c, args.steps, args.project_near, args.column_geometry_audit)
        cases.append(case)
        print(json.dumps({k: case[k] for k in ('N', 'seed', 'height', 'initialPrice',
            'finalPrice', 'accumulatedActualCredit', 'creditFraction')}, allow_nan=False), flush=True)
    result = dict(schemaVersion=1, cases=cases,
        input=dict(path=str(args.input), sha256=hashlib.sha256(args.input.read_bytes()).hexdigest()),
        scope=dict(optionalOutsideBuildsCI=True, originalFrozenFullBaseRetained=True,
            originalLabelsMasksImportanceWeightsAndPhasesRetained=True,
            allCountsAndPeriodsJoined=True, previousNullsAndTiltFixed=True,
            medianComputesOneWholeDirectionStep=True, newLPOrPerLabelFit=False,
            columnAuditIsNotCompleteUnpaidInventory=True,
            allZeroAndNearRowsPriced=True, approximateProjectionResidualsRetained=True,
            exactCrossingFormulaEvaluatedInFloatingArithmetic=True,
            nativeCofinalPoints=False, nativePaidOwnerBudgetApplied=False,
            actualNativeSupplyFunded=False, nativePopulationOrCofinalBound=False,
            wholeFloorProved=False))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n')


if __name__ == '__main__':
    main()

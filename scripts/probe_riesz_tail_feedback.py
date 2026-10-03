#!/usr/bin/env python3
"""Optional deterministic signed-feedback test, with every crossing paid.

Reads only frozen joined-period matrices and their verified source hashes.
The earlier nulls/tilt remain fixed. No LP, per-label fitting or countwise
price is used for the new steps. One rule reads the entire adverse aggregate,
chooses its whole feedback direction, and pays its near/far crossing cost.
Sampled orders are nonnative; floating phases, edges and factorizations are
uncertified. This is not a whole-population/cofinal floor certificate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import numpy as np
import mpmath as mp
from scipy.linalg import null_space
from probe_riesz_zero_response_floor import frozen_rows


def experiment(case, steps, project_near=False, unpaid_column_audit=False):
    path = Path(case['matrixArtifact']['path'])
    assert hashlib.sha256(path.read_bytes()).hexdigest()==case['matrixArtifact']['sha256']
    source = Path(case['frozenInput']['path'])
    assert hashlib.sha256(source.read_bytes()).hexdigest()==case['frozenInput']['sha256']
    archive = np.load(path)
    matrix, old = archive['matrix'],archive['oldMatrix']
    # Sign convention: this is minus the actual signed floor increment.
    t = old[:,0]+old[:,1:]@np.asarray(case['originalEarlierCoefficients'])
    columns = matrix[:,8:]
    audited_counts = None
    retained_labels = columns.shape[1]
    if unpaid_column_audit:
        pars,rows,_ = frozen_rows(case['N'],case['seed'])
        by_label = {r['label']:r for r in rows}
        # The exact closed-block selector is equivalent to B>=D, since
        # B is its largest divisor. Reconstruct the original column order.
        closed_labels = sorted(n for n,r in by_label.items() if
            n//(sorted(r['primes'])[0]*sorted(r['primes'])[1])>=pars['physical'])
        assert len(closed_labels)==columns.shape[1]
        selected = [by_label[n] for n in closed_labels]
        keep = np.asarray([r['owner']<60069/100000 and
            sorted(r['primes'])[1]>case['N']**3 for r in selected])
        columns = columns[:,keep]
        retained_labels = int(keep.sum())
        audited_counts = {str(k):sum(r['count']==k for r,b in zip(selected,keep) if b)
            for k in sorted({r['count'] for r,b in zip(selected,keep) if b})}
    square_norms = np.square(columns).sum(axis=0)
    active = square_norms>0
    columns = columns[:,active]/np.sqrt(square_norms[active])
    assert np.max(np.abs(columns.sum(axis=0)),initial=0.) < 1e-7
    initial_price, initial_total = float(np.maximum(t,0.).sum()),float(t.sum())
    records = []
    for s in range(steps):
        # Applied to t_signed=-t, this is the exact sum-of-squares rule in
        # adverseCorrelation_feedback_eq, with inverse squared-column norm.
        scale = max(np.abs(t))
        thresholds = np.r_[0.,np.geomspace(1e-8,1e-2,19)*scale]
        candidates = []
        for tau in thresholds:
            correlation = columns.T@(t>0)
            direction = -columns@correlation
            signed_flux = float(-direction[t>0].sum())
            squared_flux = float(np.square(correlation).sum())
            assert abs(signed_flux-squared_flux) < 1e-7
            near = np.abs(t)<=tau
            debit = float(np.where(t[near]>0,
                np.maximum(-direction[near],0.),np.maximum(direction[near],0.)).sum())
            far = ~near
            quadratic = float((np.square(direction[far])/(4*np.abs(t[far]))).sum())
            available = max(signed_flux-debit,0.)
            step = available/(2*quadratic) if quadratic>0 else 0.
            credit = available**2/(4*quadratic) if quadratic>0 else 0.
            candidates.append(dict(credit=credit,step=step,threshold=float(tau),
                debit=debit,quadratic=quadratic,direction=direction,
                squaredFlux=squared_flux,signedFlux=signed_flux,
                projected=False,retainedDirections=columns.shape[1]))
        if project_near:
            for fraction in (1e-10,1e-7,1e-5,1e-3,1e-2):
                tau = fraction*scale
                near = np.abs(t)<=tau
                # Approximate kernel projection. Its ACTUAL residual is
                # charged below; no exact near-row orthogonality is assumed.
                projection = null_space(columns[near],rcond=1e-11)
                joined = columns@projection
                correlation = joined.T@(t>0)
                direction = -joined@correlation
                signed_flux = float(-direction[t>0].sum())
                squared_flux = float(np.square(correlation).sum())
                assert abs(signed_flux-squared_flux)<1e-7
                debit = float(np.where(t[near]>0,
                    np.maximum(-direction[near],0.),np.maximum(direction[near],0.)).sum())
                far = ~near
                quadratic = float((np.square(direction[far])/(4*np.abs(t[far]))).sum())
                available = max(signed_flux-debit,0.)
                step = available/(2*quadratic) if quadratic>0 else 0.
                credit = available**2/(4*quadratic) if quadratic>0 else 0.
                candidates.append(dict(credit=credit,step=step,threshold=float(tau),
                    debit=debit,quadratic=quadratic,direction=direction,
                    squaredFlux=squared_flux,signedFlux=signed_flux,
                    projected=True,retainedDirections=projection.shape[1]))
        chosen = max(candidates,key=lambda c:c['credit'])
        credit,step,tau,debit,quadratic = [chosen[k] for k in
            ('credit','step','threshold','debit','quadratic')]
        direction = chosen['direction']
        signed_flux,squared_flux = chosen['signedFlux'],chosen['squaredFlux']
        current_price = float(np.maximum(t,0.).sum())
        updated = t+step*direction
        new_price = float(np.maximum(updated,0.).sum())
        actual_gain = current_price-new_price
        assert credit>=0 and actual_gain+1e-10>=credit
        assert abs(float(updated.sum())-initial_total)<1e-8
        records.append(dict(stepIndex=s,threshold=tau,stepSize=step,
            projectedNearRows=chosen['projected'],
            retainedFeedbackDirections=chosen['retainedDirections'],
            squaredSignedCorrelation=squared_flux,signedCorrelation=signed_flux,
            joinedNearDebit=debit,joinedFarPrice=quadratic,
            availableCorrelation=max(signed_flux-debit,0.),
            formulaCredit=credit,actualCostSaving=actual_gain,
            beforePrice=current_price,afterPrice=new_price))
        t = updated
    accumulated = sum(r['formulaCredit'] for r in records)
    final_price = float(np.maximum(t,0.).sum())
    assert accumulated+final_price<=initial_price+1e-9
    return dict(N=case['N'],seed=case['seed'],height=case['height'],
        closedLabels=case['closedLabels'],initialPrice=initial_price,
        unpaidColumnAudit=unpaid_column_audit,retainedCorrectionLabels=retained_labels,
        auditedCorrectionCounts=audited_counts,
        finalPrice=final_price,accumulatedFormulaCredit=accumulated,
        actualSaving=initial_price-final_price,formulaCreditFraction=accumulated/initial_price,
        stepCount=steps,projectNear=project_near,steps=records,
        unavoidableSignedPrice=max(initial_total,0.),
        excessOverSignedTotal=final_price-max(initial_total,0.),
        matrixArtifact=case['matrixArtifact'],
        frozenInput=case['frozenInput'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,default=Path('.lake/riesz-common-tail/probe.json'))
    parser.add_argument('--steps',type=int,default=12)
    parser.add_argument('--project-near',action='store_true',
        help='Also try joined columns with small response on near periods; charge all residuals.')
    parser.add_argument('--unpaid-column-audit',action='store_true',
        help='Restrict ONLY new columns to owner share <60069/100000 and second prime >N^3; keep the base unchanged.')
    parser.add_argument('--output',type=Path,default=Path('.lake/riesz-common-tail/feedback.json'))
    args = parser.parse_args()
    if args.steps<0:
        parser.error('nonnegative step count required')
    mp.mp.dps = 100
    source = json.loads(args.input.read_text())
    cases = [experiment(c,args.steps,args.project_near,args.unpaid_column_audit) for c in source['cases']]
    report = dict(schemaVersion=1,cases=cases,
        input=dict(path=str(args.input),sha256=hashlib.sha256(args.input.read_bytes()).hexdigest()),
        scope=dict(optionalOutsideBuildsCI=True,
            originalLabelsMasksImportanceWeightsAndBasePhasesRetained=True,
            allCountsAndPeriodsJoined=True,previousNullsAndTiltFixed=True,
            newCoefficientsFromOneSignedCorrelationRule=True,newLPOrPerLabelFit=False,
            joinedNearProjectionUsed=args.project_near,
            approximateProjectionResidualAlwaysCharged=True,
            unpaidColumnAudit=args.unpaid_column_audit,
            auditMasksDeleteBaseRows=False,
            auditedMasks='Only new columns: owner share <60069/100000; second least prime >N^3' if args.unpaid_column_audit else None,
            auditedMasksAreNotACompleteUnpaidPopulationInventory=True,
            eachSuccessiveBoundaryRepriced=True,formulaCreditIsFloatingNotCertified=True,
            probablePrimalityAndLargePeriodEdgesUncertified=True,
            nativeCofinalPoints=False,nativePaidOwnerBudgetApplied=False,
            populationOrCofinalPriceBound=False,wholeFloorProved=False))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
    for c in cases:
        print(json.dumps({k:c[k] for k in ('N','seed','height','initialPrice',
            'finalPrice','accumulatedFormulaCredit','actualSaving','formulaCreditFraction')},
            allow_nan=False),flush=True)


if __name__=='__main__':
    main()

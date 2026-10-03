#!/usr/bin/env python3
"""Probe the SIGNED Selberg split on the literal unpaid toy boundary.

All head/correction masks and actual product phases come from the frozen
low-count evaluator. Selberg is compared on the SAME support; its defect
is never norm-paid. Coefficient-sign populations are joined inside each
complete period and then across periods. No native/cofinal bound is claimed.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import numpy as np
from scipy.stats import binom
import probe_riesz_low_count_period_coupling as coupling


def encode(z):
    return dict(re=float(z.real), im=float(z.imag))


def corr(x,y):
    if len(x)<2 or np.std(x)==0. or np.std(y)==0.:
        return None
    return float(np.corrcoef(x,y)[0,1])


def cutoff_calibration():
    """Native-sized cutoff geometry ONLY, not a prime-sum computation.

The log profile uses shares .495/.505, below the literal 1.02N owner
threshold on its larger leg. Both head/correction masks are absent.
It samples the coefficient geometry, not actual prime products.
"""
    orders=[(N,None) for N in [6,7,8,9]]
    orders += [(8*(j+4)*2**(j+3),j) for j in range(8)]
    rows=[]
    for N,j in orders:
        D=20000**N//(10001**N*(N+1))
        L=2*math.log(D+2)
        ideal=-2*N*math.log(10001/20000)
        x,z=.99*N,1.01*N
        T=x+z
        def defect(length):
            R=length-max(length-x,0.)-max(length-z,0.)+max(length-T,0.)
            return -R/length+2*x*z/T**2
        rows.append(dict(N=N,nativeDyadicIndex=j,actualLengthOver2N=L/(2*N),
                         idealLengthOver2N=ideal/(2*N),
                         actualUncorrectedDefectOverT=defect(L),
                         idealUncorrectedDefectOverT=defect(ideal),
                         actualPrimeEnumeration=False,actualSignedSum=False))
    return rows


def add_selberg(data,actual_length=False):
    T=data['T']
    labels=np.rint(np.exp(T)).astype(np.int64)
    pair_indices=np.flatnonzero(data['pair']!=0.)
    pair_labels=labels[pair_indices]
    small=np.zeros(len(pair_labels),dtype=np.int64)
    top=math.isqrt(int(pair_labels.max()))
    sieve=np.ones(top+1,dtype=bool)
    sieve[:2]=False
    for p in range(2,math.isqrt(top)+1):
        if sieve[p]: sieve[p*p::p]=False
    for q in np.flatnonzero(sieve):
        hits=(small==0)&(pair_labels%q==0)
        small[hits]=q
    assert np.all(small>1)
    large=pair_labels//small
    assert np.all(small<large) and np.all(small*large==pair_labels)
    assert np.max(np.abs(np.log(large)+np.log(small)-T[pair_indices]))<1e-13
    scale=np.exp((data['N']+1)*math.log(data['u'])-1.5*T+
                 data['N']*np.log(T)-math.lgamma(data['N']+1))
    if actual_length:
        N=data['N']
        damped=20000**N//(10001**N*(N+1))
        physical=(damped+2)**2
        L=math.log(physical)
        old_L=data['L']
        assert L<=old_L, 'The old support is a superset only in these toy cases.'
        # SAME integer labels, reweighted at the exact rational floor cutoff.
        # The old support contains every central pair and all new corrections.
        x,z=np.log(large),np.log(small)
        pairT=T[pair_indices]
        pairScale=scale[pair_indices]
        central=(math.floor(math.exp(1.971*N))<pair_labels)&(
            pair_labels<=math.floor(math.exp(2.029*N)))
        riesz=L-np.maximum(L-x,0.)-np.maximum(L-z,0.)+np.maximum(L-pairT,0.)
        original=np.where(central,-pairT/L*riesz*pairScale,0.)
        correction_mask=(math.ceil(math.exp(1.02*N))<=large)&(large<=physical)
        correction=np.where(correction_mask,pairT/L*(L-x)*pairScale,0.)
        orders=np.arange(N//5+2,13*N//32+1)
        allocated=binom.pmf(orders[:,None],N+1,(z/pairT)[None,:]).sum(axis=0)
        head_mask=(math.ceil(math.exp(1.02*N))<=large)&(
            large<=math.floor(math.exp(1.25*N)))&(N*N<large)&(large<physical)&(N**3<small)
        head=np.where(head_mask,pairT/L*(L-x)*(1-allocated)*pairScale,0.)
        assert np.max(head-correction)<2e-12
        joined=original+head-correction
        assert np.max(joined)<2e-12 and np.min(joined/(pairScale*pairT))>=-1.-2e-12
        data['pair']=np.zeros(len(T))
        data['pair'][pair_indices]=joined
        prime_indices=np.flatnonzero(data['prime']!=0.)
        data['prime'][prime_indices]=-T[prime_indices]*np.minimum(L,T[prime_indices])/L*scale[prime_indices]
        data.update(L=L,physical=physical,originalHeadMass=float(head.sum()),
                    fullCorrectionMass=float(correction.sum()),dampedCutoff=damped)
    selberg_pair=np.zeros(len(T))
    selberg_pair[pair_indices]=np.where(data['pair'][pair_indices]!=0.,
        -2*np.log(small)*np.log(large)/T[pair_indices]*scale[pair_indices],0.)
    defect=data['pair']-selberg_pair
    selberg=data['prime']+selberg_pair
    joined=data['prime']+data['pair']
    assert np.max(np.abs(selberg+defect-joined))<2e-15
    data.update(selberg=selberg,defect=defect,
                defectPositive=np.maximum(defect,0.),defectNegative=np.minimum(defect,0.),
                selbergPair=selberg_pair,pairIndices=pair_indices,
                smallShares=np.log(small)/T[pair_indices])
    return data


def case(data,y):
    N,T=data['N'],data['T']
    width=2*math.pi/abs(y)
    period=np.floor(T/width).astype(np.int64)
    complete=(1.971*N<=period*width)&((period+1)*width<=2.029*N)
    indices=np.flatnonzero(complete)
    periods,inverse=np.unique(period[indices],return_inverse=True)
    phase=np.exp(-1j*y*T[indices])
    grouped={}
    for name in ['prime','pair','selberg','selbergPair','defect','defectPositive','defectNegative']:
        values=data[name][indices]*phase
        grouped[name]=(np.bincount(inverse,weights=values.real,minlength=len(periods))+
                       1j*np.bincount(inverse,weights=values.imag,minlength=len(periods)))
    joined=grouped['prime']+grouped['pair']
    reconstructed=grouped['selberg']+grouped['defect']
    assert np.max(np.abs(joined-reconstructed))<2e-14
    # Every term retains its phase. The absolute quantities below diagnose
    # finite cancellation; none becomes an arithmetic endgame allowance.
    def cancellation(x,z):
        gross=float(np.abs(x.real).sum()+np.abs(z.real).sum())
        net=float(np.abs((x+z).real).sum())
        return dict(grossReal=gross,netPeriodReal=net,
                    fraction=1-net/gross if gross>0. else 0.)
    share_rows=[]
    pair_ix=data['pairIndices']
    shares=data['smallShares']
    complete_pair=complete[pair_ix]&(data['pair'][pair_ix]!=0.)
    for left,right in zip(np.linspace(0.,.5,11)[:-1],np.linspace(0.,.5,11)[1:]):
        mask=complete_pair&(left<=shares)&(shares<right)
        chosen=pair_ix[mask]
        value=np.sum(data['defect'][chosen]*np.exp(-1j*y*T[chosen]))
        share_rows.append(dict(lower=float(left),upper=float(right),labels=int(mask.sum()),
                               signedDefect=encode(value)))
    result=dict(N=N,height=y,length=data['L'],physicalPrimeCutoff=data['physical'],
                originalHeadMass=data['originalHeadMass'],
                fullCorrectionMass=data['fullCorrectionMass'],completePeriods=len(periods),
                joined=encode(joined.sum()),selberg=encode(grouped['selberg'].sum()),
                defect=encode(grouped['defect'].sum()),
                positiveCoefficientDefect=encode(grouped['defectPositive'].sum()),
                negativeCoefficientDefect=encode(grouped['defectNegative'].sum()),
                selbergDefectPeriodCorrelation=corr(grouped['selberg'].real,grouped['defect'].real),
                defectSignPeriodCorrelation=corr(grouped['defectPositive'].real,grouped['defectNegative'].real),
                selbergPrimePairPeriodCorrelation=corr(grouped['prime'].real,grouped['selbergPair'].real),
                signedSelbergDefectOpposition=bool(grouped['selberg'].real.sum()*grouped['defect'].real.sum()<0.),
                defectSignCancellation=cancellation(grouped['defectPositive'],grouped['defectNegative']),
                selbergDefectCancellation=cancellation(grouped['selberg'],grouped['defect']),
                shareProfile=share_rows)
    old=coupling.row(data,y,False)
    assert abs(joined.sum()-coupling.decode(old['completeJoined']))<2e-12
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders',type=int,nargs='+',default=[6,7,8])
    parser.add_argument('--heights',type=float,nargs='+',default=[54.,65.,100.,142.,400.,1600.,51200.])
    parser.add_argument('--actual-length',action='store_true',
                        help='Use log((floor(u^(-N)/(N+1))+2)^2) and its strict physical cutoff.')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    frozen=json.loads(Path('.lake/riesz-low-count-signed-boundary/probe.json').read_text())
    frozen={(row['N'],row['height']):row for row in frozen['cases']}
    rows,regressions=[],0
    for N in args.orders:
        assert N in [6,7,8,9], 'Toy evaluator only; not a native certificate.'
        print(json.dumps(dict(event='prepare',N=N)),flush=True)
        data=add_selberg(coupling.low_count_data(N),args.actual_length)
        for y in args.heights:
            assert math.isfinite(y) and 54<=abs(y)
            row=case(data,y)
            if (N,y) in frozen and not args.actual_length:
                assert abs(coupling.decode(row['joined'])-
                           coupling.decode(frozen[(N,y)]['completePeriodsSigned']))<2e-12
                regressions+=1
            rows.append(row)
        print(json.dumps(dict(event='finished',N=N)),flush=True)
    summaries=[]
    for N in args.orders:
        selected=[row for row in rows if row['N']==N]
        def median(key):
            vals=[row[key] for row in selected if row[key] is not None]
            return float(np.median(vals)) if vals else None
        summaries.append(dict(N=N,heights=len(selected),
            selbergDefectOppositeTotals=sum(row['signedSelbergDefectOpposition'] for row in selected),
            medianSelbergDefectCorrelation=median('selbergDefectPeriodCorrelation'),
            medianDefectSignCorrelation=median('defectSignPeriodCorrelation'),
            medianSelbergPrimePairCorrelation=median('selbergPrimePairPeriodCorrelation'),
            maxJoinedReal=max(row['joined']['re'] for row in selected),
            maxDefectReal=max(row['defect']['re'] for row in selected)))
    root=Path(__file__).resolve().parents[1]
    paths=[Path(__file__),root/'scripts/probe_riesz_low_count_period_coupling.py',
           root/'RiemannGaussian/ZetaRieszLowCountSelbergAudit.lean',
           root/'RiemannGaussian/ZetaSquarefreeVaughanLogSource.lean',
           root/'RiemannGaussian/ZetaRieszAnnulusJoint.lean',
           root/'RiemannGaussian/ZetaVaughanCutoffBudget.lean']
    report=dict(cases=rows,summaries=summaries,oldCompletePeriodRegressions=regressions,
        exactFiniteSplit=True,allActualToyPhasesRetained=True,
        idealToyLengthAndOlderPhysicalSchedule=not args.actual_length,
        actualDampedLengthAndPhysicalCutoff=args.actual_length,
        nativeEventualTheoremsApplied=False,
        signedArithmeticBoundProved=False,defectNotNormPaid=True,
        nativeCutoffGeometryCalibration=cutoff_calibration() if args.actual_length else [],
        sourcePins=[dict(path=str(p.relative_to(root)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths])
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(cases=len(rows),regressions=regressions,summaries=summaries)))


if __name__=='__main__':
    main()

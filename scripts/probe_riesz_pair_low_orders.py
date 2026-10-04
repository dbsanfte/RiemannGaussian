#!/usr/bin/env python3
"""Optional literal-prime regression for the proved low logged-order payment.

Retain the original period/radial support, phase and factorial floors. The
sampled response uses a common positive kernel normalization, NOT source
units. Only the Lean whole-population budget is a cofinal estimate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import numpy as np
from scipy.stats import binom
import probe_riesz_pair_algebra as algebra
import probe_riesz_pair_joint as joint
import probe_riesz_pair_structure as pair


def digest(path):
    return dict(path=str(path),sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest())


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--old',type=Path,default=Path('.lake/riesz-pair-structure/scan.primes.json'))
    ap.add_argument('--new',type=Path,default=Path('.lake/riesz-pair-joint/new-primes.json'))
    ap.add_argument('--balanced',type=Path,default=Path('.lake/riesz-balanced-prime-sampling/result.primes.json'))
    ap.add_argument('--output',type=Path,default=Path('.lake/riesz-pair-low-orders/probe.json'))
    args=ap.parse_args()
    boxes=joint.prepare(args.old,args.new,args.balanced)
    rows=[]
    for b in boxes:
        N=b['N']
        L=pair.parameters(N)['L']
        M,H,K=N+1,17*N//64+1,13*N//32
        T,x,z=b['T'],b['x'],b['z']
        assert H<=K
        low=-T/L*(x*binom.cdf(H-1,M,x/T)+z*binom.cdf(H-1,M,z/T))
        physical=np.maximum(x,z)<=L
        removed=np.where(physical,low,0.)
        raw,surviving=algebra.component_profiles(N,L,x,z)
        c=b['coefficient']
        completed=-T/L*(L-np.maximum(L-x,0)-np.maximum(L-z,0)+np.maximum(L-T,0))
        radial=-np.where(c['central'],0.,completed)
        original=sum(surviving.values())+radial-c['selberg']
        remaining=(surviving['central_order_M']+surviving['central_order_M_plus_1']+
            (surviving['low_logged_order']-removed)+radial-c['selberg'])
        error=float(np.max(np.abs(original-remaining-removed)))
        assert error<1e-10*max(1.,float(np.max(np.abs(original))))
        bound=2*T*np.exp(-N/1000)
        assert np.all(np.abs(removed)<=bound+1e-10)
        y=100
        pl,_=joint.correlations.integer_height_phase(b['p'],y)
        qr,_=joint.correlations.integer_height_phase(b['q'],y)
        phase=pl[:,None]*qr[None,:]
        keep=joint.exact_period_mask(b,y)
        ref=b['ref']
        kernel=np.exp(N*np.log1p((T-ref)/ref)-1.5*(T-ref))/N
        response=lambda weight:pair.encode(complex(np.sum((weight*kernel*phase)[keep])))
        rows.append(dict(box=b['id'],N=N,seed=b['seed'],height=str(y),movingLength=L,
            loggedCutoff=H,originalLoggedCutoff=K,incidences=int(T.size),
            physicalIncidences=int(physical.sum()),retainedPhysicalIncidences=int((keep&physical).sum()),
            sourceScale=False,coefficientReplayError=error,
            originalPrefix=response(original),removedLowLogged=response(removed),remainingPrefix=response(remaining),
            retainedRadialFlag=True,retainedSelbergSubtraction=True,retainedPeriodMask=True,
            exteriorLargestPrimesUnchanged=True,
            representative=dict(primes=[str(b['p'][0]),str(b['q'][0])],
                physical=bool(physical[0,0]),coefficient=float(low[0,0]),
                totalLog=float(T[0,0]),minimumShare=float(min(x[0,0],z[0,0])/T[0,0]))))
    certificates=[]
    for N in [65536,90112,196608]:
        certificates.append(dict(N=N,
            provedBudget=float(8*np.exp(2)*(N+1)*np.exp(-N/1250)),
            worstShareTailDiagnostic=float(binom.cdf(17*N//64,N+1,7/24)),
            diagnosticIsNotProof=True))
    paths=['scripts/probe_riesz_pair_low_orders.py','scripts/probe_riesz_pair_algebra.py',
        'scripts/probe_riesz_pair_joint.py','RiemannGaussian/ZetaRieszPairLowOrderPayment.lean',
        'RiemannGaussian/ZetaRieszPairPrefixConvolution.lean',args.old,args.new,args.balanced]
    output=dict(classification='Regression of an independently proved geometric payment',
        sources=[digest(p) for p in paths],rows=rows,largeOrderBudgets=certificates,
        coverage=dict(boxes=len(boxes),incidences=sum(r['incidences'] for r in rows),
            physicalIncidences=sum(r['physicalIncidences'] for r in rows),
            retainedPhysicalIncidences=sum(r['retainedPhysicalIncidences'] for r in rows),
            orders=sorted({r['N'] for r in rows}),heights=['100'],regressionOnly=True),
        independentContributionPaymentProvedInLean=True,
        fullSignedMainBoundProved=False,floor=False,zeroExclusion=False,RH=False,
        allSamplesBelowFormal65536Threshold=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(output,indent=2,allow_nan=False)+'\n')
    print(json.dumps(dict(output=str(args.output),coverage=output['coverage'],
        maxCoefficientReplayError=max(r['coefficientReplayError'] for r in rows),floor=False)))


if __name__=='__main__':
    main()

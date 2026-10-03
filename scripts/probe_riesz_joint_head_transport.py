#!/usr/bin/env python3
"""Optional floating audit of joint head transport, not an asymptotic certificate.

Keep the complete toy balanced arithmetic sum, all counts, null columns and
the same signed prime head. Move only the head's cutoff increment by an exact
zero-total direction. The original head, phase, allocation, rough-prime mask
and radial interval are retained. Length -2N log u and orders 6/7 are TOY data;
the native moving length, schedule and full deletion masks are not tested.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import numpy as np
import probe_riesz_balanced_joint as base


def quantitative_probe(t, v):
    """Floating evaluation of the proved signed crossing-square step.

    Test both orientations. Do not snap nearly-zero blocks to zero: the
    huge inverse-margin cost is real for this floating diagnostic. This is
    neither interval arithmetic nor a native/asymptotic certificate.
    """
    before=float(np.maximum(-t,0.).sum())
    results=[]
    for orientation in [1.,-1.]:
        direction=orientation*v
        correlation=float(direction[t<0].sum())
        zero_debit=float(np.maximum(-direction[t==0],0.).sum())
        nonzero=t!=0
        crossing_price=float((direction[nonzero]**2/(4*np.abs(t[nonzero]))).sum())
        available=max(correlation-zero_debit,0.)
        step=available/(2*crossing_price) if crossing_price else 0.
        gain=available**2/(4*crossing_price) if crossing_price else 0.
        saving=before-float(np.maximum(-(t+step*direction),0.).sum())
        assert gain<=saving+1e-12
        results.append(dict(orientation=orientation,correlation=correlation,
            zeroDebit=zero_debit,crossingPrice=crossing_price,step=step,
            guaranteedGain= gain,actualFloatingSavingAtStep=saving))
    return max(results,key=lambda r:r['guaranteedGain'])


def experiment(data, y, bound, window):
    N,u,hi,L = (data[k] for k in ['N','u','hi','L'])
    events = np.zeros(hi+2, dtype=np.complex128)
    direct=0.
    count=0
    for n,ps,divisors in data['labels']:
        T=math.log(n)
        if not window[0]*N<T<=window[1]*N:
            continue
        count+=1
        magnitude=math.exp((N+1)*math.log(u)-1.5*T+
                           (N+1)*math.log(T)-math.lgamma(N+1))/L
        w=-magnitude*complex(math.cos(y*T),-math.sin(y*T))
        direct+=(w*math.fsum(sgn*max(L-math.log(d),0.) for d,sgn in divisors)).real
        for d,sgn in divisors:
            events[d]+=sgn*w
    axis=np.arange(1,hi+1)
    logs=np.log(axis)
    logs_next=np.log(axis+1)
    delta=logs_next-logs
    hinge=np.maximum(L-logs,0.)-np.maximum(L-logs_next,0.)
    # Compute the joined log-minus-hinge step without catastrophic
    # subtraction below L. Its exact analytic value there is zero.
    log_minus_hinge=np.where(logs_next<=L,0.,
        np.where(logs>=L,delta,logs_next-L))
    groups=np.floor(y*logs/(2*math.pi)).astype(int)
    size=int(groups[-1])+1
    phi=np.cumsum(events)[1:hi+1]
    raw=np.column_stack([-phi.real*log_minus_hinge,-phi.real*delta,
        -phi.imag*delta,-phi.real*(logs_next**2-logs**2)/(N+1),
        -phi.imag*(logs_next**2-logs**2)/(N+1)])
    rows=np.column_stack([np.bincount(groups,weights=raw[:,i],minlength=size)
                          for i in range(5)])
    head_events=np.zeros(hi+2)
    head_total_events=np.zeros(hi+2)
    head_quadratic_events=np.zeros(hi+2)
    H=0.
    for p,q,magnitude,T in data['headPairs']:
        c=magnitude*math.cos(y*T)
        pair=c*(L-math.log(p))
        head_events[p]+=c
        head_total_events[p*q]+=pair
        H+=pair
        mark=pair*(N+1)/(2*math.log(p)*math.log(q))
        # The divisor-log-square pairing is +2 log p log q/(N+1).
        for d,sgn in [(1,1),(p,-1),(q,-1),(p*q,1)]:
            head_quadratic_events[d]+=mark*sgn
    old=np.bincount(groups,weights=np.cumsum(head_events)[1:hi+1]*hinge,minlength=size)
    at_total=np.bincount(groups,weights=head_total_events[1:hi+1],minlength=size)
    quadratic=np.bincount(groups,
        weights=-np.cumsum(head_quadratic_events)[1:hi+1]*
          (logs_next**2-logs**2)/(N+1),minlength=size)
    assert abs(old.sum()-H)<1e-10
    assert abs(at_total.sum()-H)<1e-10
    assert abs(quadratic.sum()-H)<1e-10
    rows[:,0]-=old
    assert abs(rows[:,0].sum()-(direct-H))<1e-10
    assert np.max(np.abs(rows[:,1:].sum(axis=0)))<1e-10
    old_coeff,old_price=base.optimize(rows,bound)
    old_optimized=rows[:,0]+rows[:,1:]@old_coeff
    quadratic_direction=old-quadratic
    quantitative=dict(
        beforeOldNullOptimization=quantitative_probe(rows[:,0],quadratic_direction),
        afterOldNullOptimization=quantitative_probe(old_optimized,quadratic_direction),
        almostZeroGroupsNotRoundedAway=True)
    candidates=[]
    for name,column in [('total-label',old-at_total),('divisor-quadratic',old-quadratic),
                         ('both',np.column_stack([old-at_total,old-quadratic]))]:
        matrix=np.column_stack([rows,column])
        assert np.max(np.abs(matrix[:,5:].sum(axis=0)))<1e-10
        coeff,price=base.optimize(matrix,bound)
        # Preserve the actual old optimized choice with head coefficients zero.
        # Solver roundoff on an already-zero price is not a new saving/loss.
        fallback=np.r_[old_coeff,np.zeros(matrix.shape[1]-rows.shape[1])]
        fallback_price=float(np.maximum(-(matrix[:,0]+matrix[:,1:]@fallback),0.).sum())
        if fallback_price<price:
            coeff,price=fallback,fallback_price
        updated=matrix[:,0]+matrix[:,1:]@coeff
        joined_direction=updated-old_optimized
        signed_correlation=float(joined_direction[old_optimized<0].sum())
        crossings=float(np.where(old_optimized<0,
            np.maximum(updated,0.),np.maximum(-updated,0.)).sum())
        exact_saving=signed_correlation-crossings
        assert abs(exact_saving-(old_price-price))<1e-12
        assert abs(updated.sum()-(direct-H))<1e-10
        assert -(price+1e-10)<=direct-H
        assert price<=old_price+1e-10
        candidates.append(dict(direction=name,price=price,saving=old_price-price,
            relativeSaving=(old_price-price)/old_price if old_price>1e-16 else 0.,
            relativeSavingSuppressedAsFloatingZero=(old_price<=1e-16),
            exactSignedCrossing=dict(correlation=signed_correlation,
                crossingCost=crossings,signedCredit=exact_saving,
                originalZeroFacesAndEveryAdverseCrossingRetained=True,
                nullProfilesAndHeadDirectionJoinedBeforeCrossing=True),
            globalCoefficients=coeff.tolist()))
    baseline=base.experiment(data,y,bound,window)
    assert abs(old_price-baseline['completeJoinedCostWithNulls'])<1e-10
    return dict(N=N,height=y,window=list(window),labels=count,headPairs=len(data['headPairs']),
        signedHead=H,jointTotal=direct-H,oldPrice=old_price,candidates=candidates,
        quantitativeQuadraticDirection=quantitative,
        allFiniteSignedTotalsAndZeroColumnsVerifiedInFloatingArithmetic=True,
        sourceScaleOrCofinalFloorProved=False)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--orders',nargs='+',type=int,default=[6,7])
    ap.add_argument('--heights',nargs='+',type=float,default=[54.,65.,100.])
    ap.add_argument('--bound',type=float,default=2.)
    ap.add_argument('--output',type=Path,default=Path('.lake/riesz-joint-head-transport/probe.json'))
    args=ap.parse_args()
    rows=[]
    for N in args.orders:
        assert 3<=N<=7
        data=base.prepare(N,10001/20000)
        for y in args.heights:
            assert y>=54
            for window in [(1.95,2.03),(1.971,2.029)]:
                result=experiment(data,y,args.bound,window)
                rows.append(result)
                print(json.dumps(result,allow_nan=False),flush=True)
    source=Path(__file__)
    report=dict(schemaVersion=1,source=dict(path=str(source),
        sha256=hashlib.sha256(source.read_bytes()).hexdigest()),cases=rows,
        scope=dict(optionalOutsideBuildsCI=True,movingIntegerLength=False,
            nativeDyadicSchedule=False,fullNativeDeletionMasks=False,
            previousEventualBudgetsApplied=False,fullSignedHeadUnchanged=True,
            allCountsJoinedBeforeClipping=True,exactlyOneGlobalCoefficientPerDirection=True,
            cofinalFloorOrZeroExclusionProved=False))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')


if __name__=='__main__':
    main()

#!/usr/bin/env python3
"""Optional native-mask coefficient model, not a signed arithmetic estimate.

Integrate the EXISTING joined one-/two-prime coefficient against the pure
selected simple-zero log measure. This is a spectral-channel diagnostic,
NOT actual primes, a density transport, or a certificate. Retain the damped
length, finite allocation, original physical/head/correction masks, radial
factorial kernel and complete-period endpoints. Do not spend these numbers
as an independent floor allowance.
"""

import argparse
from functools import lru_cache
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import numpy as np
import mpmath as mp
from scipy.stats import binom, gamma


U = 10001/20000
TARGET = 399/5000


@lru_cache(maxsize=None)
def rule(order):
    return np.polynomial.legendre.leggauss(order)


def moving_length(N):
    logA = N*math.log(1/U)-math.log(N+1)
    # D=floor(A); A+1 < D+2 <= A+2. This bounds the actual floor
    # correction without enormous numerator/denominator divisions.
    lower = 2*logA
    error = 4*math.exp(-logA) if logA<740 else 0.
    return lower, logA, error


@lru_cache(maxsize=None)
def stirling_remainder(N):
    # Evaluate the EXACT log-factorial remainder at high precision first;
    # then only bounded-size differences enter the floating radial saddle.
    with mp.workdps(60):
        n=mp.mpf(N)
        return float(mp.loggamma(n+1)-n*mp.log(n)+n-
                     mp.log(2*mp.pi*n)/2)


def limiting_bands():
    # The selected channel has saddle T=N/u, not 2N. The factor 2u
    # changes the answer by more than the entire remaining source gap.
    lam=-2*U*math.log(U)
    q0=13/32
    zero=1-1/(2*lam)
    primitive=lambda q:2*q+math.log1p(-q)/lam
    low=primitive(zero)
    middle=primitive(q0)-low
    high=1-2*q0-(1/lam-1)*math.log((1-q0)/q0)
    c=math.log(32/13)/lam-math.log(19/13)
    assert abs(low+middle+high-(1-c))<2e-15
    return dict(smallerShareSignTransition=zero,allocationTransition=q0,
        lowShareDefect=low,middleShareDefect=middle,highShareDefect=high,
        totalDefect=low+middle+high,existingSource=1-c,
        coefficientOnly=True,literalPrimeBound=False)


def share_profile(N,T,L,order):
    lam=L/T
    minimum=math.log(2)/T
    transition=13/32
    sd=math.sqrt(transition*(1-transition)/(N+1))
    cuts=[minimum,.5,lam,1-lam,1-1.02*N/T,1-1.25*N/T,
          1-2*math.log(N)/T,3*math.log(N)/T]
    cuts += [transition+i*sd for i in [-10,-5,-2,0,2,5,10]]
    cuts=sorted(set(x for x in cuts if minimum<=x<=.5))
    nodes,weights=rule(order)
    joined=selberg=positive=negative=0.
    band=np.zeros(10)
    # Additional fixed share bins are only diagnostic output: no count or
    # share allowance is introduced into a mathematical ledger.
    cuts=sorted(set(cuts+[i/20 for i in range(1,10) if minimum<i/20<.5]))
    for left,right in zip(cuts,cuts[1:]):
        q=(left+right)/2+(right-left)/2*nodes
        p=1-q
        R=lam-np.maximum(lam-p,0.)-np.maximum(lam-q,0.)
        R += np.maximum(lam-1.,0.)
        correction=np.where((1.02*N<=p*T)&(p*T<=L),lam-p,0.)
        allocation=(binom.cdf(13*N//32,N+1,q)-binom.cdf(N//5+1,N+1,q))
        allocation=np.clip(allocation,0.,1.)
        head=np.where((1.02*N<=p*T)&(p*T<=1.25*N)&
            (2*math.log(N)<p*T)&(p*T<L)&(3*math.log(N)<q*T),
            (lam-p)*(1-allocation),0.)
        literal=(-R+head-correction)/lam
        sel=-2*q*p
        defect=literal-sel
        assert np.max(literal)<1e-12 and np.min(literal)>=-1.-1e-12
        measure=weights/(q*p)*(right-left)/2
        joined+=float(np.dot(measure,literal))
        selberg+=float(np.dot(measure,sel))
        # These diagnose the source-channel shape, not the prime character.
        positive+=float(np.dot(measure,np.maximum(defect,0.)))
        negative+=float(np.dot(measure,np.minimum(defect,0.)))
        bin_index=min(9,int(((left+right)/2)*20))
        band[bin_index]+=float(np.dot(measure,defect))
    assert abs(joined-selberg-positive-negative)<2e-13
    return dict(joinedPair=joined,selbergPair=selberg,
                positiveDefect=positive,negativeDefect=negative,
                defect=positive+negative,shareBins=band.tolist())


def row(j,y,order):
    N=8*(j+4)*2**(j+3)
    L,logA,Lerror=moving_length(N)
    width=2*math.pi/abs(y)
    lower=math.ceil((1.971*N)/width)*width
    upper=math.floor((2.029*N)/width)*width
    mu=(N+1)/U
    sd=math.sqrt(N+1)/U
    # Finite standardized integration range. Record the discarded mass;
    # this is numerical quadrature, never an interval certificate.
    zlo=max(-12.,(lower-mu)/sd)
    zhi=min(12.,(upper-mu)/sd)
    nodes,weights=rule(order)
    z=(zlo+zhi)/2+(zhi-zlo)/2*nodes
    T=mu+sd*z
    # Exact factorial saddle, evaluated stably rather than subtracting
    # three order N log N floating-point quantities. No freeze at T=2N.
    x=U*T
    v=(x-N)/N
    logDensity=(math.log(U)+N*(np.log1p(v)-v)-
                math.log(2*math.pi*N)/2-stirling_remainder(N))
    radial=np.exp(logDensity)*sd*weights*(zhi-zlo)/2
    pair=np.zeros(len(T));sel=np.zeros(len(T));pos=np.zeros(len(T));neg=np.zeros(len(T))
    for i,t in enumerate(T):
        r=share_profile(N,float(t),L,order)
        pair[i],sel[i],pos[i],neg[i]=[r[k] for k in
            ['joinedPair','selbergPair','positiveDefect','negativeDefect']]
    prime=float(radial.sum())
    paired=float(np.dot(radial,pair))
    defect=float(np.dot(radial,pos+neg))
    selberg=prime+float(np.dot(radial,sel))
    net=prime+paired
    assert abs(net-selberg-defect)<3e-12
    mass=gamma.cdf(upper,N+1,scale=1/U)-gamma.cdf(lower,N+1,scale=1/U)
    discarded=(gamma.cdf(mu+sd*zlo,N+1,scale=1/U)-gamma.cdf(lower,N+1,scale=1/U)+
        gamma.cdf(upper,N+1,scale=1/U)-gamma.cdf(mu+sd*zhi,N+1,scale=1/U))
    saddle=share_profile(N,N/U,L,order)
    return dict(nativeIndex=j,N=N,height=y,quadratureOrder=order,
        movingLength=L,lengthOver2N=L/(2*N),
        floorLengthRoundingErrorUpper=Lerror,
        logFloorLengthRoundingErrorUpper=math.log(4)-logA,
        floorErrorUnderflow=(Lerror==0.),
        completePeriodInterval=[lower,upper],gammaMass=prime,
        gammaCdfMass=float(mass),gammaMassQuadratureDifference=prime-float(mass),
        discardedGammaMass=float(discarded),
        selectedPrimeChannel=prime,selectedJoinedPairChannel=paired,
        selectedJoinedChannel=net,selbergChannel=selberg,
        defectChannel=defect,positiveDefectChannel=float(np.dot(radial,pos)),
        negativeDefectChannel=float(np.dot(radial,neg)),
        sourceGapToTarget=net-TARGET,saddleShareProfile=saddle,
        selectedRadialSaddleOverN=1/U,
        stableExactFactorialRemainderPrecision=60,
        actualPrimeEnumeration=False,independentArithmeticBound=False)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--indices',type=int,nargs='+',default=[0,1,3,5,7,8,9,10,11,12])
    parser.add_argument('--height',type=float,default=54.)
    parser.add_argument('--quadrature',type=int,default=64)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    assert 54<=abs(args.height) and args.quadrature>=24
    rows=[]
    for j in args.indices:
        assert 0<=j<=20
        r=row(j,args.height,args.quadrature)
        rows.append(r)
        print(json.dumps({k:r[k] for k in ['nativeIndex','N','selectedJoinedChannel','sourceGapToTarget']}),flush=True)
    lam=-2*U*math.log(U)
    c=math.log(32/13)/lam-math.log(19/13)
    frozen=1-math.log(32/13)/(-math.log(U))+math.log(19/13)
    assert frozen<TARGET<1-c
    report=dict(rows=rows,existingSourceLimit=1-c,independentTarget=TARGET,
        sourceGap=1-c-TARGET,
        limitingCoefficientBands=limiting_bands(),
        forbiddenFrozenTwoNSliceLimit=frozen,
        frozenTwoNSliceWouldReverseTargetComparison=True,
        actualCutoffAndAllocationMasks=True,radialNotFrozen=True,
        actualPrimes=False,primeDensityTransport=False,cofinalFloorProved=False,
        pureSelectedZeroChannelOnly=True,allOtherModesAndAnalyticPartsExcluded=True,
        scope='Diagnostic of native finite masks; not a proof or new source theorem.',
        pins=[dict(path='scripts/probe_riesz_native_selberg_profile.py',
            sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())])
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':
    main()

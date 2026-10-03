#!/usr/bin/env python3
"""Probe ONLY the unpaid joined prime/semiprime complete-period profile.

Uses the frozen toy orders and exact older allocation/physical schedule,
not native dyadic data. The original head is joined with the unallocated
correction on each label. No positive price is asserted as an endgame bound.
Cross-count/period credits are finite diagnostics, not asymptotic payments.
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
import scipy
from scipy.stats import binom
import probe_riesz_global_squarefree_completion as completion


def encode(z):
    return dict(re=float(z.real), im=float(z.imag))


def decode(z):
    return complex(z['re'], z['im'])


def joined_data(N):
    data = completion.prepare(N)
    T, L = data['T'], data['L']
    lo = math.floor(math.exp(1.95*N))
    _, prime = completion.base.arithmetic(math.floor(math.exp(L)))
    owners = np.flatnonzero(prime)
    owners = owners[owners >= math.ceil(math.exp(1.02*N))]
    correction = np.zeros(len(T))
    for p in owners:
        c = math.log(int(p))
        qs = np.arange(math.floor(math.exp(1.95*N-c))+1,
                       math.floor(math.exp(2.03*N-c))+1)
        qs = qs[prime[qs]]
        indices = p*qs-lo-1
        correction[indices] += data['magnitude'][indices]*(L-c)
    head = np.zeros(len(T))
    for t, amount in data['headPairs']:
        index = round(math.exp(t))-lo-1
        assert abs(float(T[index])-t) < 1e-13
        head[index] += amount
    assert np.max(head-correction) < 2e-12
    central = (1.971*N < T) & (T <= 2.029*N)
    prime_mask = data['sf'] & (data['count'] == 1) & central
    pair_mask = data['sf'] & (data['count'] == 2) & central
    prime_weight = np.where(prime_mask, -data['magnitude']*data['response'], 0.)
    # The entire pair contribution is assembled before examining signs.
    pair_weight = np.where(pair_mask, -data['magnitude']*data['response'], 0.)+head-correction
    assert np.max(prime_weight) <= 2e-12
    assert np.max(pair_weight) <= 2e-12
    live = (prime_weight != 0.) | (pair_weight != 0.)
    assert np.all((data['count'][live] == 1) | (data['count'][live] == 2))
    return dict(N=N, u=data['u'], L=L, physical=20000**(2*N)//10001**(2*N),
                T=T[live], prime=prime_weight[live],
                pair=pair_weight[live], originalHeadMass=float(head.sum()),
                fullCorrectionMass=float(correction.sum()))


def low_count_data(N):
    """Enumerate ONLY ordinary primes and distinct prime products.

    This avoids sieving every higher-count Riesz divisor response. The exact
    one-/two-prime hinge formulas agree with the frozen full-divisor probe.
    The sieve is deterministic, but floating weights are not certificates.
    """
    u=10001/20000
    L=-2*N*math.log(u)
    physical=20000**(2*N)//10001**(2*N)
    lo,hi=math.floor(math.exp(1.95*N)),math.floor(math.exp(2.03*N))
    assert hi<=100_000_000, 'Optional probe cap prevents an accidental enormous sieve.'
    prime=np.ones(hi+1,dtype=bool)
    prime[:2]=False
    for p in range(2,math.isqrt(hi)+1):
        if prime[p]: prime[p*p::p]=False
    primes=np.flatnonzero(prime)
    central_lo,central_hi=math.floor(math.exp(1.971*N)),math.floor(math.exp(2.029*N))
    ps=primes[np.searchsorted(primes,central_lo+1):np.searchsorted(primes,central_hi,side='right')]
    pt=np.log(ps)
    pw=-np.exp((N+1)*math.log(u)-1.5*pt+(N+1)*np.log(pt)-math.lgamma(N+1))
    times=[pt]
    prime_parts=[pw]
    pair_parts=[np.zeros(len(pt))]
    head_mass=correction_mass=0.
    orders=np.arange(N//5+2,13*N//32+1)
    owners_low,owners_high=math.ceil(math.exp(1.02*N)),math.floor(math.exp(1.25*N))
    physical_top=math.floor(math.exp(L))
    for q in primes[:np.searchsorted(primes,math.isqrt(hi),side='right')]:
        left=max(int(q)+1,lo//int(q)+1)
        right=hi//int(q)
        ps=primes[np.searchsorted(primes,left):np.searchsorted(primes,right,side='right')]
        if not len(ps): continue
        labels=ps*q
        T=np.log(labels)
        c=np.log(ps)
        a=math.log(int(q))
        central=(central_lo<labels)&(labels<=central_hi)
        magnitude=np.exp((N+1)*math.log(u)-1.5*T+(N+1)*np.log(T)-math.lgamma(N+1))/L
        response=L-np.maximum(L-c,0.)-max(L-a,0.)+np.maximum(L-T,0.)
        completed=np.where(central,-magnitude*response,0.)
        correction_mask=(owners_low<=ps)&(ps<=physical_top)
        correction=np.where(correction_mask,magnitude*(L-c),0.)
        head_mask=(owners_low<=ps)&(ps<=owners_high)&(N*N<ps)&(ps<physical)&(N**3<q)
        allocation=binom.pmf(orders[:,None],N+1,(a/T)[None,:]).sum(axis=0)
        head=np.where(head_mask,magnitude*(L-c)*(1-allocation),0.)
        assert np.max(head-correction)<2e-12
        joined=completed+head-correction
        ratio=joined/(magnitude*L)
        assert np.max(ratio)<2e-12 and np.min(ratio)>=-1.-2e-12
        head_mass+=float(head.sum())
        correction_mass+=float(correction.sum())
        live=joined!=0.
        times.append(T[live])
        prime_parts.append(np.zeros(int(live.sum())))
        pair_parts.append(joined[live])
    return dict(N=N,u=u,L=L,physical=physical,T=np.concatenate(times),
                prime=np.concatenate(prime_parts),pair=np.concatenate(pair_parts),
                originalHeadMass=head_mass,fullCorrectionMass=correction_mass)


def positive_sum(values):
    return float(np.maximum(values, 0.).sum())


@lru_cache(maxsize=None)
def quadrature_rule(order):
    return np.polynomial.legendre.leggauss(order)


def continuous_pair_profile(data, T, quadrature_order):
    """Uncertified dx/log(x) comparison, not a transport of actual primes.

    Both Riesz hinges, the correction, and the original head are combined
    before integration. This comparison ONLY diagnoses smooth radial effects.
    """
    N, L = data['N'], data['L']
    lam = L/T
    minimum = math.log(2)/T
    cuts = [minimum,.5]
    cuts += [1-L/T, 1-1.02*N/T, 1-1.25*N/T,
             1-math.log(data['physical'])/T, 1-2*math.log(N)/T,
             3*math.log(N)/T]
    cuts = sorted(set(x for x in cuts if minimum <= x <= .5))
    nodes, weights = quadrature_rule(quadrature_order)
    orders = np.arange(N//5+2,13*N//32+1)
    answer = 0.
    for left,right in zip(cuts,cuts[1:]):
        q = (left+right)/2+(right-left)/2*nodes
        p = 1-q
        riesz = lam-np.maximum(lam-p,0.)-np.maximum(lam-q,0.)
        correction_mask = (1.02*N <= p*T) & (p*T <= L)
        correction = np.where(correction_mask,lam-p,0.)
        head_mask = ((1.02*N <= p*T) & (p*T <= 1.25*N) &
            (2*math.log(N) < p*T) & (p*T < math.log(data['physical'])) &
            (3*math.log(N) < q*T))
        allocated = binom.pmf(orders[:,None],N+1,q[None,:]).sum(axis=0)
        head = np.where(head_mask,(lam-p)*(1-allocated),0.)
        joined_shape = (riesz+correction-head)/lam
        answer += (right-left)/2*float(np.dot(weights,joined_shape/(q*p)))
    return answer


def smooth_periods(data, y, periods, quadrature_order):
    """Full phase retained at quadrature nodes; no estimate is certified."""
    width=2*math.pi/abs(y)
    nodes,weights=quadrature_rule(quadrature_order)
    prime,pair=[],[]
    for period in periods:
        lower=float(period)*width
        T=lower+width/2+width/2*nodes
        amplitude=-np.exp((data['N']+1)*math.log(data['u'])-T/2+
                          data['N']*np.log(T)-math.lgamma(data['N']+1))
        phase=np.cos(y*T)
        profile=np.array([continuous_pair_profile(data,float(t),quadrature_order) for t in T])
        prime.append(width/2*float(np.dot(weights,amplitude*phase)))
        pair.append(width/2*float(np.dot(weights,amplitude*profile*phase)))
    return np.array(prime),np.array(pair)


def row(data, y, density_diagnostic=False):
    N, T = data['N'], data['T']
    width = 2*math.pi/abs(y)
    indices = np.floor(T/width).astype(np.int64)
    lower = indices*width
    complete = (1.971*N <= lower) & (lower+width <= 2.029*N)
    phase = np.exp(-1j*y*T)
    prime_atoms = data['prime']*phase
    pair_atoms = data['pair']*phase
    literal = np.sum(prime_atoms+pair_atoms)
    ps, qs = np.sum(prime_atoms[complete]), np.sum(pair_atoms[complete])
    periods = np.unique(indices[complete])
    buckets = np.searchsorted(periods, indices[complete])
    p_period = np.bincount(buckets, weights=prime_atoms.real[complete], minlength=len(periods))
    q_period = np.bincount(buckets, weights=pair_atoms.real[complete], minlength=len(periods))
    joined_period = p_period+q_period
    p_price, q_price = positive_sum(p_period), positive_sum(q_period)
    joined_price = positive_sum(joined_period)
    cross_credit = p_price+q_price-joined_price
    period_credit = joined_price-max(float((ps+qs).real), 0.)
    assert cross_credit >= -2e-12
    assert period_credit >= -2e-12
    assert abs(float(joined_period.sum())-float((ps+qs).real)) < 2e-12
    correlation = None
    if len(periods)>1 and np.std(p_period)>0. and np.std(q_period)>0.:
        correlation = float(np.corrcoef(p_period, q_period)[0,1])
    adverse_atoms = float(np.sum(-(data['prime']+data['pair'])[complete]*
                                np.maximum(-phase.real[complete], 0.)))
    # Multiplicative biased-sign audit, NOT the one-height logarithmic phase.
    # E[sigma_p]=-a*p^(-(u-1/2)) makes E[sigma_n]=(-a)^omega*n^(-(u-1/2)).
    # Actual finite labels/coefficient masks stay unchanged in this diagnostic.
    tilt = np.exp(-(data['u']-.5)*T[complete])
    prime_mass = float(np.sum(-data['prime'][complete]*tilt))
    pair_mass = float(np.sum(-data['pair'][complete]*tilt))
    optimal_a = min(1., prime_mass/(2*pair_mass)) if pair_mass>0 else 1.
    bias_value = optimal_a*prime_mass-optimal_a**2*pair_mass
    result = dict(N=N, height=y, literalJoined=encode(literal),
        completePrime=encode(ps), completeJoinedPair=encode(qs), completeJoined=encode(ps+qs),
        partialAndExterior=encode(literal-ps-qs), completePeriods=int(len(periods)),
        primePositivePeriodDiagnostic=p_price, joinedPairPositivePeriodDiagnostic=q_price,
        joinedPositivePeriodDiagnostic=joined_price, exactCrossCountCredit=cross_credit,
        exactCrossPeriodCredit=period_credit, periodCorrelation=correlation,
        adverseAtomDiagnostic=adverse_atoms,
        crossCountFraction=cross_credit/(p_price+q_price) if p_price+q_price>0 else 0.,
        oppositeSignedPopulations=bool(ps.real*qs.real<0.),
        biasedSignDiagnostic=dict(primeMass=prime_mass, pairMass=pair_mass,
            optimumAmplitude=optimal_a, expectedValue=bias_value,
            logCharacter=False, cofinalBound=False))
    if density_diagnostic:
        model_p,model_q=smooth_periods(data,y,periods,16)
        dp,dq=p_period-model_p,q_period-model_q
        correlation=None
        if len(periods)>1 and np.std(dp)>0. and np.std(dq)>0.:
            correlation=float(np.corrcoef(dp,dq)[0,1])
        result['smoothDensityDiagnostic']=dict(primeReal=float(model_p.sum()),
            pairReal=float(model_q.sum()), residualPrimeReal=float(dp.sum()),
            residualPairReal=float(dq.sum()), residualPeriodCorrelation=correlation,
            quadratureOrder=16, actualPrimeTransport=False, noErrorEstimate=True)
        if y in (54.,65.,100.):
            check_p,check_q=smooth_periods(data,y,periods,24)
            result['smoothDensityDiagnostic']['quadratureRecheckDifference']=float(
                np.max(np.abs(check_p-model_p))+np.max(np.abs(check_q-model_q)))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[6,7,8])
    parser.add_argument('--heights', type=float, nargs='+', default=[54.,65.,100.])
    parser.add_argument('--scan', action='store_true', help='Also scan 54..154 in steps of two.')
    parser.add_argument('--density-diagnostic', action='store_true',
        help='Subtract an uncertified smooth density comparison to diagnose radial effects.')
    parser.add_argument('--low-count-only', action='store_true',
        help='Use exact one-/two-prime formulas; permits the held-out toy order nine.')
    parser.add_argument('--frozen', type=Path,
        default=Path('.lake/riesz-low-count-signed-boundary/probe.json'))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    frozen = {(r['N'], r['height']):r for r in json.loads(args.frozen.read_text())['cases']}
    heights = sorted(set(args.heights + ([float(x) for x in range(54,155,2)] if args.scan else [])))
    assert all(math.isfinite(y) and 54<=abs(y) for y in heights), 'Retain the actual height regime.'
    cases, regressions = [], 0
    for N in args.orders:
        assert N in ((6,7,8,9) if args.low_count_only else (6,7,8)), 'Not a native evaluator.'
        print(json.dumps(dict(event='prepare', N=N)), flush=True)
        data = low_count_data(N) if args.low_count_only else joined_data(N)
        for y in heights:
            case = row(data,y,args.density_diagnostic)
            if (N,y) in frozen:
                old = frozen[(N,y)]
                assert abs(decode(case['literalJoined'])-decode(old['joinedLiteral'])) < 2e-12
                assert abs(decode(case['completeJoined'])-decode(old['completePeriodsSigned'])) < 2e-12
                assert abs(case['joinedPositivePeriodDiagnostic']-old['signedWholePeriodUpperCost']) < 2e-12
                regressions += 3
            cases.append(case)
        print(json.dumps(dict(event='finished', N=N, heights=len(heights))), flush=True)
    summaries=[]
    for N in args.orders:
        selected=[r for r in cases if r['N']==N]
        correlations=[r['periodCorrelation'] for r in selected if r['periodCorrelation'] is not None]
        summaries.append(dict(N=N, heights=len(selected),
            oppositeSignedPopulationCases=sum(r['oppositeSignedPopulations'] for r in selected),
            medianCrossCountCreditFraction=float(np.median([r['crossCountFraction'] for r in selected])),
            medianPeriodCorrelation=float(np.median(correlations)) if correlations else None,
            largestCompleteJoined=max(selected,key=lambda r:r['completeJoined']['re']),
            largestBiasedExpectation=max(r['biasedSignDiagnostic']['expectedValue'] for r in selected)))
        if args.density_diagnostic:
            residual=[r['smoothDensityDiagnostic']['residualPeriodCorrelation'] for r in selected
                      if r['smoothDensityDiagnostic']['residualPeriodCorrelation'] is not None]
            summaries[-1]['medianSmoothSubtractedCorrelation']=float(np.median(residual)) if residual else None
    paths=[Path(__file__),Path(completion.__file__),Path(completion.base.__file__),args.frozen]
    u=10001/20000
    retained=math.log(32/13)/(-2*u*math.log(u))-math.log(19/13)
    threshold=399/5000
    report=dict(schemaVersion=1, cases=cases, summaries=summaries,
        frozenRegressions=regressions,
        libraries=dict(numpy=np.__version__,scipy=scipy.__version__),
        sourceSideCalibration=dict(radius=u,primeSourceForSimpleZero=1.,
            joinedPairSourceForSimpleZero=-retained,joinedSource=1-retained,
            requiredBoundaryUpper=threshold,sourceGap=1-retained-threshold,
            proofOrEstimateForActualArithmeticSum=False),
        sources=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths],
        scope=dict(optionalOutsideBuildsAndCI=True,toyOrdersNotNative=True,
            idealLengthNotNativeFloor=True,exactOlderFactorialAllocationRetained=True,
            physicalAndBothRadialMasksRetained=True,fullLogCharacterRetainedInActualCases=True,
            originalHeadAndCorrectionJoinedBeforePairDiagnostics=True,
            onlyLowCountsEnumerated=bool(args.low_count_only),
            heldOutOrderNineUncertified=9 in args.orders,
            noPositivePriceUsedAsFloorStrategy=True,noEventualNativeBudgetApplied=True,
            noCofinalFloorCeilingOrZeroExclusion=True,biasedSignsNotFixedHeightLogCharacter=True))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
    print(json.dumps(dict(cases=len(cases),regressions=regressions,summaries=summaries)),flush=True)


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Optional exact-incidence / floating-phase probe of the unpaid toy population.

Detect logarithmic response signatures across ALL counts before measuring
the real signed sum minus the same full prime head. The prime universe and
length remain the earlier toy model, not native dyadic orders/deletion
masks. No cofinal floor or short-interval density estimate is inferred.
"""

import argparse
from collections import Counter, defaultdict
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import probe_riesz_balanced_joint as base


def signature(N, primes, divisors):
    # At u=10001/20000, exp(L) is exactly this rational number. The
    # active divisor test uses integers, not rounded logarithms.
    cutoff = 20000**(2*N)//10001**(2*N)
    scalar = 0
    incidence = [0]*len(primes)
    for mask, (d, sign) in enumerate(divisors):
        if d > cutoff:
            continue
        scalar += sign
        bits = mask
        while bits:
            bit = bits & -bits
            incidence[bit.bit_length()-1] += sign
            bits -= bit
    support = [i for i, a in enumerate(incidence) if a]
    if scalar == 0 and not support:
        kind = 'exact-zero-incidences'
    elif scalar == 0 and len(support) == 1 and abs(incidence[support[0]]) == 1:
        kind = 'single-prime-log'
    elif scalar == 0 and (all(a >= 0 for a in incidence) or all(a <= 0 for a in incidence)):
        kind = 'same-sign-prime-logs'
    elif scalar == 0:
        kind = 'mixed-prime-logs'
    else:
        kind = 'nonzero-cutoff-log'
    # Test the already formalized least-pair gap. This is a sufficient
    # zero condition, not an assertion that every zero comes from a gap.
    least_pair = primes[0]*primes[1]
    gap = all(cutoff <= d or d*least_pair <= cutoff
              for mask, (d, _) in enumerate(divisors) if not mask & 3)
    if gap:
        assert kind == 'exact-zero-incidences'
    return scalar, incidence, kind, gap


def experiment(N, heights):
    data = base.prepare(N, 10001/20000)
    L, u = data['L'], data['u']
    windows = [(1.95,2.03),(1.971,2.029)]
    counts = {w:Counter() for w in windows}
    profiles = {w:Counter() for w in windows}
    zeros_outside_gap = {w:0 for w in windows}
    joined = {w:{y:defaultdict(float) for y in heights} for w in windows}
    total = {w:{y:0. for y in heights} for w in windows}
    absolute = {w:0. for w in windows}
    valuation_debit = {w:0. for w in windows}
    max_response_error = 0.
    for n, primes, divisors in data['labels']:
        A, B, kind, gap = signature(N, primes, divisors)
        logs = [math.log(p) for p in primes]
        response = A*L-math.fsum(b*l for b,l in zip(B,logs))
        literal = math.fsum(sign*max(L-math.log(d),0.) for d,sign in divisors)
        max_response_error = max(max_response_error,abs(response-literal))
        assert abs(response-literal) < 1e-10
        T = math.log(n)
        magnitude = math.exp((N+1)*math.log(u)-1.5*T+
                             (N+1)*math.log(T)-math.lgamma(N+1))/L
        terms = abs(A*L)+math.fsum(abs(b*l) for b,l in zip(B,logs))
        for w in windows:
            if not w[0]*N<T<=w[1]*N:
                continue
            counts[w][len(primes)] += 1
            profiles[w][kind] += 1
            if kind == 'exact-zero-incidences' and not gap:
                zeros_outside_gap[w] += 1
            absolute[w] += magnitude*abs(response)
            valuation_debit[w] += magnitude*terms
            for y in heights:
                atom = -magnitude*response*math.cos(y*T)
                joined[w][y][kind] += atom
                total[w][y] += atom
    cases=[]
    for w in windows:
        for y in heights:
            head = math.fsum(m*math.cos(y*T)*(L-math.log(p))
                             for p,_,m,T in data['headPairs'])
            assert abs(sum(joined[w][y].values())-total[w][y]) < 1e-12
            cases.append(dict(N=N,height=y,window=list(w),labels=sum(counts[w].values()),
                primeCounts=dict(sorted(counts[w].items())),responseProfiles=dict(profiles[w]),
                exactZeroOutsideLeastPairGap=zeros_outside_gap[w],
                signedProfileContributions=dict(joined[w][y]),
                signedMain=total[w][y],signedFullHead=head,jointTotal=total[w][y]-head,
                originalResponseMagnitude=absolute[w],
                separatedLogIncidenceMagnitude=valuation_debit[w],
                maxLogResponseReconstructionError=max_response_error,
                exactIntegerSupportAndZeroIncidences=True,
                allCountsAndFullComplexPhaseRetained=True,
                floorOrSourceScaleCertificate=False))
    return cases


def saturation(path):
    old=json.loads(path.read_text())
    rows=[]
    for case in old['cases']:
        q=next(c for c in case['candidates'] if c['direction']=='divisor-quadratic')
        negative_net=max(-case['jointTotal'],0.)
        excess=q['price']-negative_net
        assert excess>=-1e-12
        rows.append(dict(N=case['N'],height=case['height'],window=case['window'],
            optimizedQuadraticPrice=q['price'],unchangedSignedNet=case['jointTotal'],
            unavoidableNegativeNet=negative_net,costAboveNegativeNet=max(excess,0.),
            negativeNetFraction=negative_net/q['price'] if q['price']>1e-16 else 0.,
            asymptoticStatement=False))
    return rows


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders',nargs='+',type=int,default=[6,7])
    parser.add_argument('--heights',nargs='+',type=float,default=[54.,65.,100.])
    parser.add_argument('--output',type=Path,default=Path('.lake/riesz-balanced-signature/probe.json'))
    args=parser.parse_args()
    assert all(3<=N<=8 for N in args.orders)
    cases=[]
    for N in args.orders:
        print(json.dumps(dict(event='preparing',order=N)),flush=True)
        result=experiment(N,args.heights)
        cases.extend(result)
        for row in result:
            print(json.dumps(row,allow_nan=False),flush=True)
    upstream=Path('.lake/riesz-joint-head-transport/probe.json')
    paths=[Path(__file__),Path(base.__file__),upstream]
    report=dict(schemaVersion=1,
        sources=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths],
        cases=cases,previousCostSaturation=saturation(upstream),
        scope=dict(optionalOutsideBuildsCI=True,toyLength='-2N log(10001/20000)',
            exactRationalDivisorCutoff=True,movingIntegerLength=False,nativeDyadicSchedule=False,
            fullNativeDeletionMasks=False,previousEventualBudgetsApplied=False,
            probeRestrictedToBalancedUnpaidGeometry=True,
            noIndependentSignedBoundOrZeroExclusionInferred=True))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')


if __name__=='__main__':
    main()

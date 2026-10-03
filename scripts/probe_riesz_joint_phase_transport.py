#!/usr/bin/env python3
"""Optional all-count phase transport of the actual balanced toy sum minus head.

Opposite REAL arithmetic amplitudes are paired at nearby actual phases.
The exact unmatched complex contribution is retained; it is never replaced
by a positive density or assumed small. This diagnostic is not a native
moving-length/dyadic certificate, nor an eventual floor estimate.
"""

import argparse
import cmath
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import numpy as np
import probe_riesz_balanced_joint as base
import probe_riesz_balanced_signature as signature


def complex_json(z):
    return dict(re=z.real, im=z.imag)


def masses(data, window):
    N, u, L = data['N'], data['u'], data['L']
    pos, neg = [], []
    counts = {}
    for n, primes, divisors in data['labels']:
        T = math.log(n)
        if not window[0]*N < T <= window[1]*N:
            continue
        A, B, _, _ = signature.signature(N, primes, divisors)
        response = A*L-math.fsum(b*math.log(p) for b,p in zip(B,primes))
        weight = -response*math.exp((N+1)*math.log(u)-T/2+
            (N+1)*math.log(T)-math.lgamma(N+1)-math.log(L))/n
        if weight > 0:
            pos.append((weight,T))
        elif weight < 0:
            neg.append((-weight,T))
        counts[len(primes)] = counts.get(len(primes),0)+1
    # SAME full signed prime correction, independent of main contraction.
    for p, q, weight, T in data['headPairs']:
        amount = -weight*(L-math.log(p))
        if amount > 0:
            pos.append((amount,T))
        elif amount < 0:
            neg.append((-amount,T))
    return np.array(pos), np.array(neg), counts


def transport(pos, neg, height, cut):
    P, Q = float(pos[:,0].sum()), float(neg[:,0].sum())
    common = min(P,Q)
    pos_phase = np.exp(-1j*height*pos[:,1])
    neg_phase = np.exp(-1j*height*neg[:,1])
    positive = complex(np.dot(pos[:,0],pos_phase))
    negative = complex(np.dot(neg[:,0],neg_phase))
    total = positive-negative
    unmatched = (1-common/P)*positive-(1-common/Q)*negative
    pi = np.argsort((height*pos[:,1]-cut)%(2*math.pi))
    qi = np.argsort((height*neg[:,1]-cut)%(2*math.pi))
    p_mass = pos[pi,0]*(common/P)
    q_mass = neg[qi,0]*(common/Q)
    pc, qc = pos_phase[pi], neg_phase[qi]
    i = j = 0
    pp, qq = p_mass[0], q_mass[0]
    cost = 0.
    signed_moment = 0.
    cubic_cost = 0.
    largest_phase_gap = 0.
    matched = 0j
    while i < len(pi) and j < len(qi):
        amount = min(pp,qq)
        delta = pc[i]-qc[j]
        cost += amount*abs(delta)
        matched += amount*delta
        # Keep the SIGNED centered first phase moment. Only the cubic
        # Taylor defect is norm-paid, using |x-sin x| <= |x|^3/6.
        # Choose compatible lifts: q has angle b and p has angle b+gap.
        ratio = pc[i].conjugate()*qc[j]
        gap = math.atan2(ratio.imag,ratio.real)
        b = -math.atan2(qc[j].imag,qc[j].real)
        mid = b+gap/2
        assert abs(delta.real+2*math.sin(mid)*math.sin(gap/2)) < 2e-12
        signed_moment += amount*math.sin(mid)*gap
        cubic_cost += amount*abs(gap)**3/24
        largest_phase_gap = max(largest_phase_gap,abs(gap))
        pp -= amount
        qq -= amount
        if pp <= 0:
            i += 1
            if i < len(pi):
                pp = p_mass[i]
        if qq <= 0:
            j += 1
            if j < len(qi):
                qq = q_mass[j]
    assert abs(matched+unmatched-total) < 2e-10*max(P,Q,1.)
    assert abs(matched) <= cost+1e-12
    assert unmatched.real-cost <= total.real+1e-12
    assert abs(matched.real+signed_moment) <= cubic_cost+1e-12
    assert unmatched.real-signed_moment-cubic_cost <= total.real+1e-12
    return dict(cut=cut, positiveArithmeticMass=P, negativeArithmeticMass=Q,
        commonMatchedMass=common, absoluteUnmatchedMass=abs(P-Q),
        positivePhaseSum=complex_json(positive), negativePhaseSum=complex_json(negative),
        exactSignedTotal=complex_json(total), unmatchedPhaseSum=complex_json(unmatched),
        matchedPhaseSum=complex_json(matched), matchedChordCost=cost,
        signedCenteredPhaseMoment=signed_moment, cubicPhaseCost=cubic_cost,
        largestMatchedPhaseGap=largest_phase_gap,
        cubicFloor=unmatched.real-signed_moment-cubic_cost,
        cubicWholeFloorCost=signed_moment+cubic_cost-unmatched.real,
        finiteSignedFloor=unmatched.real-cost,
        wholeFloorCost=cost-unmatched.real,
        fullTriangleCost=P+Q,
        universalNormPrice=cost+abs(P-Q),
        exactComplexLedgerChecked=True,
        noUnmatchedSmallnessAssumption=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders',type=int,nargs='+',default=[6,7])
    parser.add_argument('--output',type=Path,
        default=Path('.lake/riesz-joint-phase-transport/probe.json'))
    args = parser.parse_args()
    frozen = json.loads(Path('.lake/riesz-balanced-critical-shell/probe.json').read_text())
    prior = {(x['N'],x['height'],tuple(x['window'])):x for x in frozen['cases']}
    cost_data = json.loads(Path('.lake/riesz-joint-head-transport/probe.json').read_text())
    old_costs = {(x['N'],x['height'],tuple(x['window'])):x for x in cost_data['cases']}
    rows = []
    regressions = 0
    for N in args.orders:
        assert 3 <= N <= 8
        print(json.dumps(dict(event='prepare',order=N)),flush=True)
        data = base.prepare(N,10001/20000)
        for window in [(1.95,2.03),(1.971,2.029)]:
            pos, neg, counts = masses(data,window)
            for y in [54.,65.,100.]:
                candidates = [transport(pos,neg,y,cut) for cut in
                    [0.,math.pi/2,math.pi,3*math.pi/2]]
                best = min(candidates,key=lambda row:row['wholeFloorCost'])
                cubic_best = min(candidates,key=lambda row:row['cubicWholeFloorCost'])
                key = (N,y,window)
                old = prior[key]
                assert sum(counts.values()) == old['labels']
                z = best['exactSignedTotal']
                previous = old['signedJoint']
                assert abs(complex(z['re']-previous['re'],z['im']-previous['im'])) < 2e-10
                regressions += 1
                row = dict(N=N,height=y,window=list(window),labels=sum(counts.values()),
                    counts=counts,headPairs=len(data['headPairs']),best=best,cubicBest=cubic_best,
                    comparedCuts=candidates,sourceScaleCofinalFloorProved=False)
                if key in old_costs:
                    prev = old_costs[key]
                    old_price = min(prev['oldPrice'],*(candidate['price'] for candidate
                        in prev['candidates']))
                    row['previousOptimizedWholePrice'] = old_price
                    row['newPriceImprovesPrevious'] = bool(best['wholeFloorCost'] < old_price)
                    row['cubicPriceImprovesPrevious'] = bool(cubic_best['cubicWholeFloorCost'] < old_price)
                    row['cubicPriceImprovesPreviousOrZero'] = bool(max(0,cubic_best['cubicWholeFloorCost']) < old_price)
                rows.append(row)
                print(json.dumps({k:row[k] for k in ['N','height','window','cubicBest']},
                    allow_nan=False),flush=True)
    paths = [Path(__file__),Path(base.__file__),Path(signature.__file__),
        Path('.lake/riesz-balanced-critical-shell/probe.json'),
        Path('.lake/riesz-joint-head-transport/probe.json')]
    result = dict(schemaVersion=1,cases=rows,frozenComplexTotalRegressions=regressions,
        sources=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths],
        scope=dict(optionalOutsideBuildsCI=True,toyLength='-2N log(10001/20000)',
            nativeMovingLength=False,nativeDyadicSchedule=False,fullNativeDeletionMasks=False,
            allCountsOriginalPhaseAndSameFullHeadRetained=True,
            noSourceScaleNativeFloorOrZeroExclusionClaim=True))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n')


if __name__ == '__main__':
    main()

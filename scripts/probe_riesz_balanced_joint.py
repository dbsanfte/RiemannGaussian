#!/usr/bin/env python3
"""Exhaustive finite diagnostic for the balanced signed sum minus its head.

The integer labels, Mobius divisor signs, factorial kernel, full complex phase
and signed head are evaluated literally on a TOY core window. The asymptotic
length -2*N*log(u) is intentionally used to make the owner/head geometry visible
at affordable N. This is NOT the moving integer length, native dyadic schedule,
native deletion masks, a cofinal point or a proof of a source-scale floor.

Counts and cutoff periods are joined BEFORE clipping. Every tested logarithmic
null column is verified against the exact total, including its imaginary part.
The diagnostic is optional and never participates in builds or CI.
"""

import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, eye, hstack
from scipy.stats import binom


def arithmetic(limit):
    spf = np.zeros(limit+1, dtype=np.int32)
    for p in range(2, math.isqrt(limit)+1):
        if not spf[p]:
            row = spf[p*p::p]
            row[row == 0] = p
    axis = np.arange(limit+1, dtype=np.int32)
    prime = (spf == 0) & (axis >= 2)
    spf[prime] = axis[prime]
    return spf, prime


def factors(n, spf):
    primes = []
    while n > 1:
        p = int(spf[n])
        n //= p
        if n % p == 0:
            return None
        primes.append(p)
    return primes


def signed_divisors(primes):
    result = [(1, 1)]
    for p in primes:
        result += [(d*p, -sgn) for d, sgn in result]
    return result


def optimize(rows, bound):
    scale = max(float(np.max(np.abs(rows))), 1e-100)
    matrix = rows/scale
    size, width = matrix.shape
    fit = linprog(np.r_[np.zeros(width-1), np.ones(size)],
                  A_ub=hstack((-csr_matrix(matrix[:, 1:]), -eye(size)), format='csr'),
                  b_ub=matrix[:, 0],
                  bounds=[(-bound, bound)]*(width-1)+[(0., None)]*size,
                  method='highs')
    assert fit.success, fit.message
    candidates = (np.zeros(width-1), fit.x[:width-1])
    weights = min(candidates,
                  key=lambda w: float(np.maximum(-(rows[:, 0]+rows[:, 1:]@w), 0.).sum()))
    return weights, float(np.maximum(-(rows[:, 0]+rows[:, 1:]@weights), 0.).sum())


def prepare(N, u):
    lo, hi = math.floor(math.exp(1.95*N)), math.floor(math.exp(2.03*N))
    spf, prime = arithmetic(hi)
    L = -2*N*math.log(u)
    physical = math.floor(math.exp(L))
    owner_limit = math.exp(1.02*N)
    selected = []
    counts = Counter()
    for n in range(lo+1, hi+1):
        ps = factors(n, spf)
        if ps is None or len(ps) < 3:
            continue
        if max(ps) >= physical or max(ps) >= owner_limit:
            continue
        selected.append((n, ps, signed_divisors(ps)))
        counts[len(ps)] += 1
    owners = np.flatnonzero(prime & (np.arange(hi+1) >= math.ceil(owner_limit)) &
                             (np.arange(hi+1) <= math.floor(math.exp(1.25*N))) &
                             (np.arange(hi+1) > N*N) & (np.arange(hi+1) < physical))
    head_pairs = []
    orders = np.arange(N//5+2, 13*N//32+1)
    for p in owners:
        c = math.log(p)
        qlo, qhi = math.floor(math.exp(1.95*N-c)), math.floor(math.exp(2.03*N-c))
        for q in np.flatnonzero(prime[qlo+1:qhi+1])+qlo+1:
            # The literal prime sieve excludes all primes through N^3.
            if q <= N**3:
                continue
            T = math.log(p*q)
            assigned = float(binom.pmf(orders, N+1, math.log(q)/T).sum())
            smooth = math.exp((N+1)*math.log(u)-1.5*T+
                              (N+1)*math.log(T)-math.lgamma(N+1))/L
            head_pairs.append((int(p), int(q), (1-assigned)*smooth, T))
    return dict(N=N, u=u, lo=lo, hi=hi, L=L, physical=physical,
                labels=selected, counts=counts, headPairs=head_pairs)


def experiment(data, height, bound, radial_window=(1.95, 2.03)):
    N, u, hi, L = (data[k] for k in ('N', 'u', 'hi', 'L'))
    events = {k: np.zeros(hi+2, dtype=np.complex128) for k in data['counts']}
    direct = {k: 0. for k in data['counts']}
    total_abs = 0.
    edge_signed = 0.
    edge_abs = 0.
    central_count = Counter()
    for n, ps, divisors in data['labels']:
        T = math.log(n)
        magnitude = math.exp((N+1)*math.log(u)-1.5*T+
                             (N+1)*math.log(T)-math.lgamma(N+1))/L
        w = -magnitude*complex(math.cos(height*T), -math.sin(height*T))
        response = math.fsum(sgn*max(L-math.log(d), 0.) for d, sgn in divisors)
        atom = w*response
        if not radial_window[0]*N < T <= radial_window[1]*N:
            edge_signed += atom.real
            edge_abs += abs(atom)
            continue
        central_count[len(ps)] += 1
        direct[len(ps)] = direct.get(len(ps), 0.)+atom.real
        total_abs += abs(atom)
        for d, sgn in divisors:
            events[len(ps)][d] += sgn*w

    axis = np.arange(1, hi+1)
    logs, logs_next = np.log(axis), np.log(axis+1)
    delta = logs_next-logs
    hinge = np.maximum(L-logs, 0.)-np.maximum(L-logs_next, 0.)
    groups = np.floor(height*logs/(2*math.pi)).astype(int)
    size = int(groups[-1])+1
    count_rows = {}
    for count, e in events.items():
        phi = np.cumsum(e)[1:hi+1]
        pieces = np.column_stack((
            -phi.real*(delta-hinge), -phi.real*delta, -phi.imag*delta,
            -phi.real*(logs_next**2-logs**2)/(N+1),
            -phi.imag*(logs_next**2-logs**2)/(N+1)))
        rows = np.column_stack([np.bincount(groups, weights=pieces[:, k], minlength=size)
                                for k in range(pieces.shape[1])])
        scale = max(1., abs(direct[count]), total_abs)
        assert abs(rows[:, 0].sum()-direct[count]) <= 1e-10*scale
        assert np.max(np.abs(rows[:, 1:].sum(axis=0))) <= 1e-10*scale
        count_rows[count] = rows

    head_events = np.zeros(hi+2)
    head_direct = 0.
    for p, _q, magnitude, T in data['headPairs']:
        c = magnitude*math.cos(height*T)
        head_events[p] += c
        head_direct += c*(L-math.log(p))
    head = np.bincount(groups, weights=np.cumsum(head_events)[1:hi+1]*hinge,
                       minlength=size)
    assert abs(head.sum()-head_direct) <= 1e-10*max(1., total_abs, abs(head_direct))
    joined = sum(count_rows.values())
    joined[:, 0] -= head
    signed_total = math.fsum(direct.values())-head_direct
    assert abs(joined[:, 0].sum()-signed_total) <= 1e-10*max(1., total_abs)
    weights, cost = optimize(joined, bound)
    fixed_components = [r[:, 0]+r[:, 1:]@weights for r in count_rows.values()]+[-head]
    separate = sum(float(np.maximum(-c, 0.).sum()) for c in fixed_components)
    before_nulls = float(np.maximum(-joined[:, 0], 0.).sum())
    assert -cost <= signed_total+1e-10*max(1., cost)
    assert cost <= separate+1e-10*max(1., separate)
    assert cost <= before_nulls+1e-10*max(1., before_nulls)
    return dict(N=N, height=height, labels=sum(central_count.values()),
                labelsByCount={str(k): int(v) for k, v in central_count.items()},
                headPairs=len(data['headPairs']), totalLogWindow=[1.95*N, 2.03*N],
                selectedTotalLogWindow=[radial_window[0]*N, radial_window[1]*N],
                fullSignedHeadUnchangedAfterRadialPruning=True,
                toyLength=L, balancedOwnerThreshold=1.02*N,
                signedSumByCount={str(k): float(v) for k, v in direct.items()},
                signedHead=head_direct, jointSignedTotal=signed_total,
                atomNormSum=total_abs, periods=size,
                completeJoinedCostBeforeNulls=before_nulls,
                completeJoinedCostWithNulls=cost,
                separatedCountAndHeadCostAtSameNullCoefficients=separate,
                crossCountAndHeadCancellationCostSaving=separate-cost,
                nullSaving=before_nulls-cost, nullParameters=weights.tolist(),
                signedRemovedRadialTotal=edge_signed,
                removedRadialAtomNorm=edge_abs,
                finiteFundedRadialPrice=cost+abs(edge_signed),
                originalJointSignedTotal=signed_total+edge_signed,
                thresholdAtPoint=cost <= 399/5000,
                toyFiniteLowerBound=-cost,
                floorSourceScaleOrCofinalProved=False)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--orders', nargs='+', type=int, default=[6, 7])
    ap.add_argument('--heights', nargs='+', type=float, default=[54., 65., 100.])
    ap.add_argument('--bound', type=float, default=2.)
    ap.add_argument('--compare-radial', action='store_true',
                    help='Price the 1.971/2.029 radial contraction with its actual finite error.')
    ap.add_argument('--output', type=Path,
                    default=Path('.lake/riesz-balanced-joint/probe.json'))
    args = ap.parse_args()
    cases = []
    for N in args.orders:
        assert 3 <= N <= 7, 'Keep the exhaustive toy work bounded.'
        data = prepare(N, 10001/20000)
        for y in args.heights:
            assert y >= 54
            row = experiment(data, y, args.bound)
            if args.compare_radial:
                central = experiment(data, y, args.bound, (1.971, 2.029))
                assert abs(central['originalJointSignedTotal']-row['jointSignedTotal']) <= 1e-10
                central['comparisonFullPrice'] = row['completeJoinedCostWithNulls']
                central['bestFiniteFundedPrice'] = min(row['completeJoinedCostWithNulls'],
                                                       central['finiteFundedRadialPrice'])
                central['finiteNetRadialSaving'] = (row['completeJoinedCostWithNulls']-
                                                    central['bestFiniteFundedPrice'])
                assert -central['bestFiniteFundedPrice'] <= row['jointSignedTotal']+1e-10
                row['radialComparison'] = central
            cases.append(row)
            print(json.dumps({k: row[k] for k in
                ('N', 'height', 'labels', 'jointSignedTotal', 'signedHead',
                 'completeJoinedCostBeforeNulls', 'completeJoinedCostWithNulls',
                 'crossCountAndHeadCancellationCostSaving', 'nullSaving')}, allow_nan=False),
                  flush=True)
    report = dict(schemaVersion=1,
        source=dict(path=str(Path(__file__)), sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),
        cases=cases,
        scope=dict(optionalOutsideBuildsCI=True, finiteToyIntervalExhausted=True,
            mobiusSignsWholePhaseAndFactorialWeightRetained=True,
            countsAndSignedHeadJoinedBeforeClipping=True,
            allNullTotalsAndExactFiniteLedgersVerifiedInFloatingArithmetic=True,
            radialComparisonUsesActualFiniteSignedErrorNotEventualBudget=args.compare_radial,
            radialComparisonKeepsSameFullHead=True,
            movingIntegerLength=False, nativeDyadicSchedule=False,
            nativeDeletionMasks=False, previouslyPaidNativeBudgetsApplied=False,
            numericalProofOrSourceScaleCertificate=False,
            cofinalFloorOrZeroExclusionProved=False))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')


if __name__ == '__main__':
    main()

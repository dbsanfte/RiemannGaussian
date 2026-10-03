#!/usr/bin/env python3
"""Optional joint-prime-head cutoff diagnostic, outside builds and CI.

Exhaust a TOY integer cofactor interval. Preserve the actual factorial owner
allocation, Mobius divisor signs, prime correction and complex phase. Join
the correction to the complete cutoff-period increment before clipping.
This is NOT the native core or a cofinal/source-scale certificate. The
finite error is paid by its actual value, never by an eventual theorem.
"""

import argparse
from collections import defaultdict
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import numpy as np
from scipy.optimize import linprog
from scipy.stats import binom

from probe_riesz_complex_null_profiles import period_edge
from probe_riesz_rough_owner_comparison import arithmetic


def divisors(n):
    out = []
    for d in range(1, math.isqrt(n)+1):
        if n % d == 0:
            out.append(d)
            if d*d != n:
                out.append(n//d)
    return out


def optimize(matrix, bound):
    scale = max(float(np.max(np.abs(matrix))), 1e-100)
    base, dirs = matrix[:, 0]/scale, matrix[:, 1:]/scale
    size = len(base)
    from scipy.sparse import csr_matrix, eye, hstack
    fit = linprog(np.r_[np.zeros(2), np.ones(size)],
                  A_ub=hstack((csr_matrix(dirs), -eye(size)), format='csr'),
                  b_ub=-base, bounds=[(-bound, bound)]*2+[(0., None)]*size,
                  method='highs')
    assert fit.success, fit.message
    candidates = [np.zeros(2), fit.x[:2]]
    p = min(candidates, key=lambda x: float(np.maximum(base+dirs@x, 0.).sum()))
    return p, float(np.maximum(matrix[:, 0]+matrix[:, 1:]@p, 0.).sum())


def experiment(height, b, bound):
    N, p, M, X, u = 32, 100003, 5000, 10000, .50005
    mu, count, _, prime = arithmetic(X)
    L, c = math.log(p)+b, math.log(p)
    weights = {}
    rough = set()
    head_coefficient = 0.
    direct_original = direct_rough = 0.
    for a in range(M+1, X+1):
        T = c+math.log(a)
        assigned = float(binom.pmf(np.arange(N//5+2, 13*N//32+1),
                                  N+1, math.log(a)/T).sum())
        amplitude = math.exp((N+1)*math.log(u)-T/2+(N+1)*math.log(T)
                             -math.lgamma(N+1))/(L*p*a)
        w = -amplitude*(1-assigned)*math.cos(height*T)
        if prime[a]:
            head_coefficient -= w
        if not mu[a] or prime[a]:
            continue
        weights[a] = w
        if a % 2 and a % 3:
            rough.add(a)
        R = math.fsum(int(mu[d])*max(L-math.log(d), 0.)
                      -int(mu[d])*max(L-math.log(p*d), 0.) for d in divisors(a))
        direct_original += w*R
        if a in rough:
            direct_rough += w*R
    H = b*head_coefficient
    events = defaultdict(float)
    for a, w in weights.items():
        if a in rough:
            continue
        for d in divisors(a):
            events[d] += w*int(mu[d])
            events[p*d] -= w*int(mu[d])
    endpoint = p*X
    points = sorted({1, p, endpoint, *events})
    groups = defaultdict(lambda: np.zeros(4))
    phi, unit = 0., 2*math.pi/height
    for left, right in zip(points, points[1:]):
        phi += events[left]
        lo, hi = math.log(left), math.log(right)
        splits = sorted({lo, hi, min(hi, max(lo, L)), min(hi, max(lo, c))})
        for begin, end in zip(splits, splits[1:]):
            cursor, period = begin, math.floor(begin/unit)
            while cursor < end:
                edge = min(end, period_edge(period, unit))
                if edge <= cursor:
                    period += 1
                    continue
                width = edge-cursor
                # Increment = base + p1*log-null + p3*quadratic-null.
                groups[period] += np.array([
                    -phi*width if cursor >= L else 0.,
                    -phi*width,
                    -phi*(edge*edge-cursor*cursor)/(N+1),
                    head_coefficient*width if c <= cursor < L else 0.])
                cursor, period = edge, period+1
    matrix = np.asarray(list(groups.values()))
    totals = matrix.sum(axis=0)
    scale = max(1e-100, abs(direct_original), abs(direct_rough), abs(H))
    assert abs(totals[0]-(direct_original-direct_rough)) <= 1e-9*scale
    assert np.max(np.abs(totals[1:3])) <= 1e-9*scale
    assert abs(totals[3]-H) <= 1e-9*scale
    p0, separate_cost = optimize(-matrix[:, :3], bound)
    joined_matrix = matrix[:, :3].copy()
    joined_matrix[:, 0] -= matrix[:, 3]
    pj, joined_cost = optimize(-joined_matrix, bound)
    base = matrix[:, 0]+matrix[:, 1:3]@p0
    h = matrix[:, 3]
    overlap = float((np.minimum(np.maximum(base, 0.), np.maximum(h, 0.))+
                     np.minimum(np.maximum(-base, 0.), np.maximum(-h, 0.))).sum())
    minus = float(np.maximum(-h, 0.).sum())
    fixed_cost = float(np.maximum(h-base, 0.).sum())
    assert abs((separate_cost+H-fixed_cost)-(overlap-minus)) <= 1e-9*scale
    error = abs(direct_rough+H)
    valid_separate = separate_cost+H+error
    valid_joined = joined_cost+error
    assert -min(valid_separate, valid_joined) <= direct_original+1e-9*scale
    return dict(height=height, N=N, owner=p, cutoff=b, compositeLabels=len(weights),
                roughLabels=len(rough), completePeriods=len(matrix),
                originalSignedTotal=direct_original, signedPrimeHead=H,
                actualFiniteJointError=error, separatePrice=valid_separate,
                joinedPrice=valid_joined, verifiedFiniteSaving=max(0., valid_separate-valid_joined),
                fixedCoefficientGain=overlap-minus, sameSignOverlap=overlap,
                negativeHeadPeriodMass=minus, separateParameters=p0.tolist(),
                joinedParameters=pj.tolist(), earlyHeadFraction=1.,
                originalAndJoinedAbelResidual=max(abs(totals[0]-(direct_original-direct_rough)),
                                                 abs(totals[3]-H)))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path,
                    default=Path('.lake/riesz-prime-head-periods/probe.json'))
    args = ap.parse_args()
    report = dict(schemaVersion=1,
                  cases=[experiment(y, b, 2.) for b in (3., 4.) for y in (54., 65., 100.)],
                  source=dict(path=str(Path(__file__).resolve()),
                              sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),
                  scope=dict(optionalOutsideBuildsCI=True, toyIntervalExhausted=True,
                             ownerFactorialAllocationRetained=True, allCountsAndPeriodsJoined=True,
                             finiteJointErrorPaidByActualValue=True,
                             nativeCoreOrCofinalPoint=False, eventualRateApplied=False,
                             floatingLogsPhasesAndLargePeriodEdges=True,
                             floorOrZeroExclusionProved=False))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    for row in report['cases']:
        print(json.dumps({k: row[k] for k in ('height', 'cutoff', 'signedPrimeHead',
                         'separatePrice', 'joinedPrice', 'verifiedFiniteSaving',
                         'fixedCoefficientGain', 'sameSignOverlap')}, allow_nan=False), flush=True)


if __name__ == '__main__':
    main()

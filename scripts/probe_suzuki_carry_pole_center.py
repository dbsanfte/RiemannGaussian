#!/usr/bin/env python3
"""Two-scale pole-centering preflight on the unchanged finite Fejer packet.

Optional research replay, not an interval certificate. Small packets use
exact rational jump bookkeeping followed by high-precision Hurwitz values.
Large packets use the exact finite floor sums on a refined Mellin grid.
Actual prime data keeps all proper powers and is joined before norms.
"""

import argparse
from fractions import Fraction
from functools import lru_cache
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
from probe_suzuki_integer_carry import prime_power_bases


def jump_events(H):
    events = {}
    for N in range(H, 3*H):
        sign = -1 if N < 2*H else 1
        for k in range(1, 2*N):
            q = Fraction(k, 2*N)
            events[q] = events.get(q, 0)+sign*(1 if k % 2 else -1)
    value = 0
    result = []
    for q, jump in sorted(events.items()):
        change = (value+jump)**2-value**2
        if change:
            result.append((q, change))
        value += jump
    assert value == 0 and sum(change for _, change in result) == 0
    return result


def finite_mellin(H, s):
    """Periodic jump derivation; its general Hurwitz identity is not Lean-proved."""
    terms = []
    for q, change in jump_events(H):
        a = mp.mpf(q.numerator)/q.denominator
        if s == 1:
            value = -mp.digamma(a)-mp.euler
        else:
            # Subtracting the common zeta value exposes exact pole cancellation.
            value = mp.zeta(s, a)-mp.zeta(s)
        terms.append(change*value)
    return mp.fsum(terms)/(s*H**2)


def floor_sum_float(n0, a0, b0):
    """Vector Euclidean floor summation; floating grid replay only."""
    n = np.full_like(a0, n0, dtype=float)
    a, b = a0.copy(), b0.copy()
    answer = np.zeros_like(a)
    active = n > 0
    for _ in range(80):
        if not np.any(active):
            return answer
        qa, qb = np.floor(a), np.floor(b)
        answer += np.where(active, n*(n-1)/2*qa+n*qb, 0)
        a, b = a-qa, b-qb
        maximum = a*n+b
        next_n = np.floor(maximum)
        active &= (next_n > 0) & (a > 0)
        safe = np.where(active, a, 1)
        b = (maximum-next_n)/safe
        a = 1/safe
        n = np.where(active, next_n, 0)
    raise AssertionError('floor-sum grid did not terminate')


def grid_value(H, x):
    denominator = H*x
    def block(A):
        a = 1/denominator
        return (floor_sum_float(H, 2*a, 2*A*a)-
                2*floor_sum_float(H, a, A*a))
    return (block(2*H)-block(H))/H


def integer_floor_sum(n0, m0, a0, b0):
    n = np.full_like(m0, n0)
    m, a, b = m0.copy(), np.full_like(m0, a0), np.full_like(m0, b0)
    answer = np.zeros_like(m)
    active = n > 0
    for _ in range(80):
        if not np.any(active):
            return answer
        qa, qb = a//m, b//m
        answer += np.where(active, n*(n-1)//2*qa+n*qb, 0)
        a, b = a % m, b % m
        maximum = a*n+b
        active &= maximum >= m
        next_n = maximum//m
        b = maximum % m
        m, a = np.where(active, a, 1), m
        n = np.where(active, next_n, 0)
    raise AssertionError('integer floor-sum replay did not terminate')


def integer_value(H, ds):
    def block(A):
        return (integer_floor_sum(H, ds, 2, 2*A)-
                2*integer_floor_sum(H, ds, 1, A))
    return (block(2*H)-block(H))/H


def floor_replay():
    x = np.exp(np.linspace(-6, math.log(6), 311))
    residual = 0.0
    for H in [1, 2, 7, 16, 31]:
        N = np.arange(H, 3*H, dtype=float)[:, None]
        direct = (np.sum((np.floor(2*N[H:]/(H*x)) % 2), axis=0)-
                  np.sum((np.floor(2*N[:H]/(H*x)) % 2), axis=0))/H
        err = float(np.max(np.abs(direct-grid_value(H, x))))
        residual = max(residual, err)
        if err > 1e-9:
            raise AssertionError('finite floating packet differs from direct carry replay')
        ds = np.arange(1, 6*H+1, dtype=np.int64)
        direct_integer = (np.sum((2*N[H:].astype(np.int64)//ds) % 2, axis=0)-
                          np.sum((2*N[:H].astype(np.int64)//ds) % 2, axis=0))/H
        if not np.array_equal(direct_integer, integer_value(H, ds)):
            raise AssertionError('integer floor-sum differs from literal carries')
    return residual


@lru_cache(maxsize=4)
def grid_table(H, points):
    lo, hi = -16.0, math.log(6)
    step = (hi-lo)/points
    logs = lo+(np.arange(points)+.5)*step
    value = grid_value(H, np.exp(logs))
    return logs, value**2, step


def grid_mellin(H, s, points):
    logs, mass, step = grid_table(H, points)
    normalized = np.sum(np.exp(s*logs)*mass)*step
    # This is only the omitted lower tail, not a bound on grid quadrature error.
    tail = math.exp(-16*s.real)/s.real
    return normalized*complex(np.exp(s*math.log(H))), tail


def continuum_kappa(s):
    # Paper diagnostic from the periodic, piecewise quadratic limiting profile.
    nodes = [(1,6,18,0), (1,4,-16,-2), (1,3,30,-1), (1,2,0,-8),
             (2,3,-30,-1), (3,4,16,-2), (5,6,-18,0)]
    return mp.fsum(a*mp.zeta(s, mp.mpf(n)/d)+s*b*mp.zeta(s+1, mp.mpf(n)/d)
                   for n,d,a,b in nodes)/(s*(s+1)*(s+2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--maximum-h', type=int, default=32768)
    parser.add_argument('--grid-points', type=int, default=131072)
    parser.add_argument('--small-h', type=int, default=4)
    parser.add_argument('--output', type=Path,
                        default=Path('.lake/suzuki-carry-pole-center/probe.json'))
    args = parser.parse_args()
    mp.mp.dps = 40
    beta = mp.mpf('0.99995')
    heights = [mp.mpf(60), 12*mp.pi/mp.log(2)]
    exact = []
    for H in [1, 2, args.small_h]:
        cb, c2b = finite_mellin(H, beta), finite_mellin(2*H, beta)
        for y in heights:
            p = 1-1j*y
            cp, c2p = finite_mellin(H, p), finite_mellin(2*H, p)
            det = c2p*cb-cp*c2b
            exact.append({'H':H, 'height':float(y),
                          'matchedCoefficient':mp.nstr(cb,22),
                          'poleCoefficient':str(cp),
                          'sourceDeterminantDividedBy_H_power_1_plus_beta':
                              mp.nstr(abs(det)/H**(1+beta),22),
                          'relativeFinitePoleScaleDefect':
                              mp.nstr(abs(c2p-2**p*cp)/abs(c2p),18),
                          'relativeFiniteMatchedScaleDefect':
                              mp.nstr(abs(c2b-2**beta*cb)/abs(c2b),18)})
    bases = prime_power_bases(12*args.maximum_h)
    ds = np.flatnonzero(bases)
    lam = np.log(bases[ds].astype(float))
    rows = []
    for H in sorted({256, 1024, 4096, args.maximum_h}):
        take = ds <= 12*H
        dd, ll = ds[take], lam[take]
        w1, w2 = integer_value(H, dd)**2, integer_value(2*H, dd)**2
        cb, _ = grid_mellin(H, complex(beta), args.grid_points)
        c2b, _ = grid_mellin(2*H, complex(beta), args.grid_points)
        for y_mp in heights:
            y, p = float(y_mp), 1-1j*float(y_mp)
            cp, tail = grid_mellin(H, p, args.grid_points)
            c2p, _ = grid_mellin(2*H, p, args.grid_points)
            cp_ref, _ = grid_mellin(H, p, 2*args.grid_points)
            c2p_ref, _ = grid_mellin(2*H, p, 2*args.grid_points)
            phase = np.exp(-1j*y*np.log(dd.astype(float)))
            joined = np.sum(ll*phase*(c2p*w1-cp*w2))
            normalized = joined/H
            det = (c2p*cb-cp*c2b)/H
            density = c2p*cp-cp*c2p
            kappa = complex(continuum_kappa(1-1j*y_mp))
            ideal = kappa*complex(continuum_kappa(beta))*(2**p-2**float(beta))
            outer = (dd > 8*H) & (dd < 9*H)
            rows.append({'H':H,'height':y,
                         'poleCanceledFloatingResidual':abs(density),
                         'matchedResponseNormDividedBy_H_power_beta':abs(det)/H**float(beta),
                         'idealLimitMatchedResponseNorm':abs(ideal),
                         'centeredLiteralNormDividedBy_H_power_beta':abs(normalized)/H**float(beta),
                         'centeredLiteralRealDividedBy_H_power_beta':normalized.real/H**float(beta),
                         'poleMellinGridRefinementNormalizedDifference':
                             max(abs(cp-cp_ref)/H, abs(c2p-c2p_ref)/(2*H)),
                         'unresolvedLowerTailBoundNormalized':tail,
                         'outerCellPhasedContributionNormalized':
                             abs(np.sum(ll[outer]*phase[outer]*(c2p*w1[outer]-cp*w2[outer]))/H),
                         'outerCellJoinedAbsoluteMassNormalized':
                             float(np.sum(ll[outer]*np.abs(c2p*w1[outer]-cp*w2[outer]))/H),
                         'outwardRounded':False})
    report={'scope':'Optional noncertifying arithmetic and Mellin preflight',
            'ordinaryPrimePowersRetained':True,'phaseRetainedThroughTwoScaleJoin':True,
            'floorSumDirectReplayMaximumResidual':floor_replay(),
            'smallFiniteJumpMellinReplay':exact,'largeFinitePacketGridReplay':rows,
            'finiteMellinScalingExact':False,'HurwitzAndContinuumFormulaLeanProved':False,
            'globalArithmeticSourcePowerSavingProved':False,'rhProved':False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'output':str(args.output),
                      'smallFiniteJumpMellinReplay':exact,
                      'lastLargePackets':rows[-2:]},indent=2))


if __name__ == '__main__':
    main()

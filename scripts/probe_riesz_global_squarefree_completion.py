#!/usr/bin/env python3
"""Optional all-count integer-lattice completion audit, retaining every boundary.

This uses the frozen toy radius, length and windows. It is not a native
dyadic computation or a certificate. The original balanced main and the
same full head are independently checked against the earlier complex totals.
Completing the main is permitted here only as an exact diagnostic ledger:
the ordinary-prime, semiprime and raw high-owner terms remain explicit.
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
import probe_riesz_balanced_joint as base


def encode(z):
    return dict(re=float(z.real), im=float(z.imag))


def decode(z):
    return complex(z['re'], z['im'])


def prepare(N):
    u = 10001 / 20000
    L = -2 * N * math.log(u)
    lo, hi = math.floor(math.exp(1.95 * N)), math.floor(math.exp(2.03 * N))
    physical = 20000**(2*N) // 10001**(2*N)
    spf, isprime = base.arithmetic(hi)
    primes = np.flatnonzero(isprime)
    counts = np.zeros(hi+1, dtype=np.uint8)
    largest = np.zeros(hi+1, dtype=np.int32)
    squarefree = np.ones(hi+1, dtype=bool)
    squarefree[0] = False
    for p in primes:
        counts[p::p] += 1
        largest[p::p] = p
        if p <= math.isqrt(hi):
            squarefree[p*p::p*p] = False
    mu = np.zeros(physical+1, dtype=np.int8)
    mu[1:] = np.where(squarefree[1:physical+1],
                      np.where(counts[1:physical+1] % 2, -1, 1), 0)
    response = np.zeros(hi+1)
    mark = np.zeros(physical+1)
    mark[1] = 1.
    for d in range(1, physical+1):
        if not mu[d]:
            continue
        if d > 1:
            p = int(spf[d])
            mark[d] = mark[d//p] / (p+1)
        response[d::d] += int(mu[d]) * (L-math.log(d))
    density = (6 / math.pi**2) * math.fsum(
        int(mu[d])*mark[d]*(L-math.log(d)) for d in range(1, physical+1) if mu[d])
    axis = np.arange(lo+1, hi+1)
    T = np.log(axis)
    magnitude = np.exp((N+1)*math.log(u)-1.5*T+(N+1)*np.log(T)
                       -math.lgamma(N+1)) / L
    sf = squarefree[axis]
    ct, lp = counts[axis], largest[axis]
    physical_ok = lp < physical
    balanced = lp < math.exp(1.02*N)
    # Re-evaluate the SAME full correction, including every factorial slot.
    owners = primes[(primes >= math.ceil(math.exp(1.02*N))) &
                    (primes <= math.floor(math.exp(1.25*N))) &
                    (primes > N*N) & (primes < physical)]
    orders = np.arange(N//5+2, 13*N//32+1)
    pairs = []
    for p in owners:
        c = math.log(int(p))
        qlo, qhi = math.floor(math.exp(1.95*N-c)), math.floor(math.exp(2.03*N-c))
        qs = primes[(primes > max(qlo, N**3)) & (primes <= qhi)]
        for q in qs:
            t = math.log(int(p)*int(q))
            allocation = float(binom.pmf(orders, N+1, math.log(int(q))/t).sum())
            weight = math.exp((N+1)*math.log(u)-1.5*t+(N+1)*math.log(t)
                              -math.lgamma(N+1))/L
            pairs.append((t, (L-c)*(1-allocation)*weight))
    return dict(N=N, u=u, L=L, T=T, magnitude=magnitude, response=response[axis],
                sf=sf, count=ct, physical=physical_ok, balanced=balanced,
                density=density, headPairs=pairs)


def experiment(data, y, window, frozen):
    N, L, T = data['N'], data['L'], data['T']
    phase = np.exp(-1j*y*T)
    w = -data['magnitude'] * phase
    inside = (window[0]*N < T) & (T <= window[1]*N)
    sf = data['sf'] & inside
    composite = sf & (data['count'] >= 3)
    literal = composite & data['physical'] & data['balanced']
    high = composite & data['physical'] & ~data['balanced']
    physical_failure = composite & ~data['physical']
    atom = w * data['response']
    bulk = np.sum(atom[sf])
    prime = np.sum(atom[sf & (data['count'] == 1)])
    semiprime = np.sum(atom[sf & (data['count'] == 2)])
    main = np.sum(atom[literal])
    high_total = np.sum(atom[high])
    phys = np.sum(atom[physical_failure])
    density = data['density'] * np.sum(w[inside])
    centered = bulk-density
    head = sum(a*complex(math.cos(y*t), -math.sin(y*t)) for t,a in data['headPairs'])
    joint = main-head
    old = frozen[(N, y, window)]
    main_error = abs(main-decode(old['originalBalancedMain']))
    head_error = abs(head-decode(old['sameFullOriginalHead']))
    assert main_error < 2e-12, main_error
    assert head_error < 2e-12, head_error
    boundary = -prime-semiprime-high_total-phys-head
    assert abs(joint-(density+centered+boundary)) < 2e-12
    return dict(N=N, height=y, window=list(window), originalBalancedMain=encode(main),
                sameFullOriginalHead=encode(head), actualJoint=encode(joint),
                allCountSquarefreeBulk=encode(bulk), signedIntegerDensityMain=encode(density),
                signedCountingError=encode(centered), ordinaryPrimeBoundary=encode(prime),
                semiprimeBoundary=encode(semiprime), rawHighOwnerBoundary=encode(high_total),
                physicalUpperFailure=encode(phys), joinedUnpaidBoundary=encode(boundary),
                mainRegressionError=main_error, headRegressionError=head_error,
                bulkToUnpaidBoundaryMagnitude=abs(bulk)/max(abs(boundary), 1e-300),
                fullRadialPhaseAndAllCountsRetained=True,
                originalHeadHasNotBeenRadiallyPruned=True,
                rawHighOwnerBoundaryHasNoSourcePayment=True,
                noBoundaryDeclaredSmall=True, cofinalFloorProved=False)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--orders', type=int, nargs='+', default=[6, 7])
    ap.add_argument('--output', type=Path,
                    default=Path('.lake/riesz-global-squarefree-completion/probe.json'))
    args = ap.parse_args()
    assert all(N in [6, 7, 8] for N in args.orders)
    previous = Path('.lake/riesz-owner-completion/probe.json')
    frozen = {(r['N'], r['height'], tuple(r['window'])): r
              for r in json.loads(previous.read_text())['cases']}
    cases = []
    for N in args.orders:
        print(json.dumps(dict(event='prepare', N=N)), flush=True)
        data = prepare(N)
        for y in [54., 65., 100.]:
            for window in [(1.95, 2.03), (1.971, 2.029)]:
                row = experiment(data, y, window, frozen)
                cases.append(row)
                print(json.dumps({k:row[k] for k in ['N','height','window','actualJoint',
                      'allCountSquarefreeBulk','ordinaryPrimeBoundary','semiprimeBoundary',
                      'rawHighOwnerBoundary','joinedUnpaidBoundary']}, allow_nan=False), flush=True)
    sources = [Path(__file__), Path(base.__file__), previous]
    report = dict(schemaVersion=1, cases=cases, complexTotalRegressions=len(cases),
                  sources=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
                           for p in sources],
                  scope=dict(optionalOutsideBuildsCI=True, finiteToyIntegersExhausted=True,
                             squarefreeIntegerDensityNotPrimeDensity=True,
                             toyLength='-2N log(10001/20000)', nativeMovingLength=False,
                             nativeDyadicSchedule=False, nativeDeletionMasks=False,
                             noEventualBudgetApplied=True, noCompletedBoundaryDeleted=True,
                             numericalCertificate=False, floorOrZeroExclusionProved=False))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print(json.dumps(dict(cases=len(cases), regressions=len(cases), goalStillOpen=True)), flush=True)


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Optional exact-label/full-phase regression of the joined low-count boundary.

Uses frozen toy orders, ideal length, and the older physical allocation
schedule. Native eventual estimates are NEVER evaluated on these data.
The signed whole-period sum is diagnostic, not an asymptotic certificate.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import numpy as np
import probe_riesz_global_squarefree_completion as completion


def encode(z):
    return dict(re=float(z.real), im=float(z.imag))


def decode(z):
    return complex(z['re'], z['im'])


def experiment(N, frozen):
    data = completion.prepare(N)
    T, L = data['T'], data['L']
    lo = math.floor(math.exp(1.95*N))
    _, isprime = completion.base.arithmetic(math.floor(math.exp(L)))
    owners = np.flatnonzero(isprime)
    owners = owners[owners >= math.ceil(math.exp(1.02*N))]
    correction = np.zeros(len(T))
    for p in owners:
        c = math.log(int(p))
        qs = np.arange(math.floor(math.exp(1.95*N-c))+1,
                       math.floor(math.exp(2.03*N-c))+1)
        qs = qs[isprime[qs]]
        labels = p*qs
        i = labels-lo-1
        correction[i] += data['magnitude'][i]*(L-c)
    head = np.zeros(len(T))
    for t, amount in data['headPairs']:
        n = round(math.exp(t))
        i = n-lo-1
        assert abs(float(T[i])-t) < 1e-13
        head[i] += amount
    assert np.max(head-correction) < 2e-12
    central = (1.971*N < T) & (T <= 2.029*N)
    low_count = data['sf'] & (data['count'] <= 2) & central
    completed = np.where(low_count, -data['magnitude']*data['response'], 0.)
    joined = completed+head-correction
    # Every FULL four-term coefficient is in [-log n,0] after cancellation.
    # The normalization below divides by |u^(N+1) K_N|*log n.
    ratio = joined/(data['magnitude']*L)
    assert np.max(ratio) < 2e-12
    assert np.min(ratio) >= -1.-2e-12
    cases = []
    for y in [54., 65., 100.]:
        phase = np.exp(-1j*y*T)
        literal = np.sum(joined*phase)
        old = frozen[(N,y)]
        assert abs(literal-decode(old['remainingSignedLowCountBoundary'])) < 2e-12
        original_head = np.sum(head*phase)
        prime_correction = np.sum(correction*phase)
        assert abs(original_head-decode(old['sameFullOriginalHead'])) < 2e-12
        assert abs(prime_correction-decode(old['unallocatedPrimeCorrection'])) < 2e-12
        width = 2*math.pi/abs(y)
        period = np.floor(T/width).astype(np.int64)
        lower = period*width
        complete = (1.971*N <= lower) & (lower+width <= 2.029*N)
        signed = joined*phase
        inside = np.sum(signed[complete])
        per_period = np.bincount(period[complete], weights=signed.real[complete])
        positive_period_cost = float(np.maximum(per_period, 0.).sum())
        adverse_arc_price = float(np.sum((-joined[complete])*np.maximum(-phase.real[complete], 0.)))
        assert positive_period_cost <= adverse_arc_price+2e-12
        cases.append(dict(N=N,height=y,joinedLiteral=encode(literal),
            completePeriodsSigned=encode(inside),partialAndExterior=encode(literal-inside),
            signedWholePeriodUpperCost=positive_period_cost,
            adverseArcAtomPrice=adverse_arc_price,
            exactCorrectionOverlapMass=float(np.sum(head)),
            minCoefficientOverLog=float(np.min(ratio)),maxCoefficientOverLog=float(np.max(ratio)),
            completePeriods=int(np.unique(period[complete]).size),
            frozenComplexRegressions=3))
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders',type=int,nargs='+',default=[6,7,8])
    parser.add_argument('--frozen',type=Path,
        default=Path('.lake/riesz-global-raw-owner-payment/probe.json'))
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    original = json.loads(args.frozen.read_text())
    frozen = {(r['N'],r['height']):r for r in original['cases']}
    cases = []
    for N in args.orders:
        print(json.dumps(dict(event='prepare',N=N)),flush=True)
        cases += experiment(N,frozen)
    paths = [Path(__file__).relative_to(Path.cwd()),
        Path('scripts/probe_riesz_global_squarefree_completion.py'),args.frozen]
    report = dict(schemaVersion=1,cases=cases,
        frozenComplexRegressions=sum(r['frozenComplexRegressions'] for r in cases),
        sources=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths],
        scope=dict(optionalOutsideBuildsAndCI=True,toyDataNotNative=True,
            idealLengthNotNativeFloor=True,allLiteralPhasesAndCorrectionsRetained=True,
            nativeEventualTheoremNotAppliedAtToyOrders=True,
            noCofinalFloorCeilingOrZeroExclusionClaim=True))
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(cases=len(cases),regressions=report['frozenComplexRegressions'],
        coefficientRange=[min(r['minCoefficientOverLog'] for r in cases),
                          max(r['maxCoefficientOverLog'] for r in cases)])),flush=True)


if __name__ == '__main__':
    main()

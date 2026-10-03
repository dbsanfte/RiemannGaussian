#!/usr/bin/env python3
"""Optional full-phase regression for the all-count raw-owner payment.

Uses the FROZEN toy model at orders 6/7/8 (ideal length and older physical
cutoff/schedule), not native dyadic data. No asymptotic theorem is applied
at these orders and no independent floor or phase-period bound is inferred.
The unallocated correction is kept separately from the original full head.
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


def probe(N, frozen):
    data = completion.prepare(N)
    u, L, T = data['u'], data['L'], data['T']
    lo, hi = math.floor(math.exp(1.95*N)), math.floor(math.exp(2.03*N))
    axis = np.arange(lo+1, hi+1)
    spf, isprime = completion.base.arithmetic(math.floor(math.exp(L)))
    owners = np.flatnonzero(isprime)
    owners = owners[owners >= math.ceil(math.exp(1.02*N))]
    raw = data['sf'] & (data['count'] >= 3) & ~data['balanced']
    central = (1.971*N < T) & (T <= 2.029*N)
    raw_coefficient = -data['magnitude']*data['response']
    row_coefficient = np.zeros(len(T))
    correction = np.zeros(len(T))
    unit_mark = np.zeros(len(spf), dtype=np.int8)
    unit_mark[1] = 1
    for d in range(2, len(spf)):
        p = int(spf[d])
        a = d//p
        unit_mark[d] = 0 if a % p == 0 else -unit_mark[a]
    owners_count = len(owners)
    incidences = 0
    max_atom_error = 0.
    for p in owners:
        c = math.log(int(p))
        a = np.arange(math.floor(math.exp(1.95*N-c))+1,
                      math.floor(math.exp(2.03*N-c))+1)
        assert np.all((1 < a) & (a < p))
        labels = p*a
        i = labels-lo-1
        t = np.log(labels)
        weight = np.exp((N+1)*math.log(u)-1.5*t+(N+1)*np.log(t)
                        -math.lgamma(N+1))/L
        response = np.zeros(len(a))
        for d in range(1, math.floor(math.exp(L-c))+1):
            if unit_mark[d]:
                response[a % d == 0] += int(unit_mark[d])*(L-c-math.log(d))
        composite = data['sf'][i] & (data['count'][i] >= 3)
        row_coefficient[i[composite]] += weight[composite]*response[composite]
        prime = isprime[a]
        correction[i[prime]] += weight[prime]*(L-c)
        incidences += int(composite.sum())
        if np.any(composite):
            max_atom_error = max(max_atom_error, float(np.max(np.abs(
                data['response'][i[composite]]+response[composite]))))
    assert max_atom_error < 2e-12, max_atom_error
    assert np.max(np.abs(row_coefficient-np.where(raw, raw_coefficient, 0))) < 2e-12
    cases = []
    for y in [54., 65., 100.]:
        phase = np.exp(-1j*y*T)
        raw_full = np.sum(row_coefficient*phase)
        raw_central = np.sum(row_coefficient[central]*phase[central])
        prime_correction = np.sum(correction*phase)
        sf_join = np.sum((row_coefficient+correction)*phase)
        assert abs(sf_join-raw_full-prime_correction) < 2e-12
        old = frozen[(N, y)]
        assert abs(raw_central-decode(old['rawHighOwners'])) < 2e-12
        original_head = sum(w*complex(math.cos(y*t), -math.sin(y*t))
                            for t,w in data['headPairs'])
        assert abs(original_head-decode(old['sameFullHead'])) < 2e-12
        p1 = decode(old['centralOrdinaryPrime'])
        p2 = decode(old['centralSemiprime'])
        low = p1+p2+original_head-prime_correction
        boundary = decode(old['wholeSignedBoundary'])
        assert abs(boundary-low-raw_central-prime_correction) < 2e-12
        cases.append(dict(N=N, height=y, rawFull=encode(raw_full),
            rawCentral=encode(raw_central), unallocatedPrimeCorrection=encode(prime_correction),
            sameFullOriginalHead=encode(original_head), allCountJoined=encode(sf_join),
            centralRadialMismatch=encode(raw_central-raw_full),
            remainingSignedLowCountBoundary=encode(low),
            maxAtomIdentityError=max_atom_error, ownerCount=owners_count,
            compositeIncidences=incidences, frozenComplexRegressions=3))
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[6,7,8])
    parser.add_argument('--frozen', type=Path,
        default=Path('.lake/riesz-global-head-price-audit/probe.json'))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    original = json.loads(args.frozen.read_text())
    frozen = {(x['N'], x['height']): x for x in original['cases']}
    cases = [x for N in args.orders for x in probe(N, frozen)]
    report = dict(schemaVersion=1, cases=cases,
        frozenComplexRegressions=sum(x['frozenComplexRegressions'] for x in cases),
        sources=[dict(path=str(p), sha256=hashlib.sha256(p.read_bytes()).hexdigest())
            for p in [Path(__file__).relative_to(Path.cwd()),
                      Path('scripts/probe_riesz_global_squarefree_completion.py'),args.frozen]],
        scope=dict(optionalOutsideBuildsAndCI=True, fullComplexPhaseRetained=True,
            everyRawCountRetained=True, unallocatedCorrectionNotOriginalHead=True,
            toyDataNotNative=True, idealLengthNotNativeFloor=True,
            noNativeTheoremAppliedAtToyOrders=True, noIndependentFloorClaim=True))
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(cases=len(cases), frozenComplexRegressions=report['frozenComplexRegressions'],
        maxAtomIdentityError=max(x['maxAtomIdentityError'] for x in cases))))

if __name__ == '__main__':
    main()

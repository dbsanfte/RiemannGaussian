#!/usr/bin/env python3
"""Optional price obstruction and whole signed-boundary phase diagnostic.

The scalar envelope is the proved EVENTUAL expression, not a finite-order
lower bound: the PNT lower-count starting order has not been evaluated.
The exhaustive signed diagnostic retains the frozen TOY windows/length,
all count classes, the unallocated raw-high coefficients and SAME full
head. It neither imports a native eventual payment at these orders nor
claims a cofinal floor, zero exclusion or signed divergence.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import mpmath as mp
import numpy as np
import probe_riesz_global_squarefree_completion as completion


def encode(z):
    return dict(re=float(z.real), im=float(z.imag))


def decode(z):
    return complex(z['re'], z['im'])


def scalar_probe():
    mp.mp.dps = 70
    u = mp.mpf(10001)/20000
    rate = mp.log(2*u)
    log_constant = mp.log(u)-mp.mpf(9)/2-mp.log(216)
    def log_envelope(N):
        return log_constant+N*rate-3*mp.log(N+1)
    orders = [256, 640, 1536, 4096, 8192, 65536, 100000, 500000, 1000000]
    crossing = mp.findroot(lambda n: log_envelope(n)-mp.log(mp.mpf(399)/5000),
                           (500000, 1000000))
    return dict(radius=str(u), logarithmicGrowthExponent=str(rate),
        growthConstant=str(mp.exp(log_constant)),
        scalarModelCrossing=str(crossing),
        samples=[dict(N=N, logLowerEnvelope=str(log_envelope(N)),
                      lowerEnvelope=str(mp.exp(log_envelope(N)))) for N in orders],
        scope=dict(eventualEnvelopeOnly=True,
            unevaluatedPNTStartingOrder=True,
            scalarModelCrossingIsNotNativeCertifiedThreshold=True,
            noSignedDivergenceOrCofinalFloorClaim=True))


def signed_probe(N, frozen, head_frozen):
    data = completion.prepare(N)
    T = data['T']
    central = (1971*N/1000 < T) & (T <= 2029*N/1000)
    sf = central & data['sf']
    prime = sf & (data['count'] == 1)
    semi = sf & (data['count'] == 2)
    # Raw high owners have NO allocated-residual or physical support mask.
    high = sf & (data['count'] >= 3) & ~data['balanced']
    coefficient = -data['magnitude']*data['response']
    joined_coefficient = np.where(prime | semi | high, coefficient, 0.)
    full_head_coefficient = np.zeros(len(T))
    lo = math.floor(math.exp(1.95*N))
    for t, amount in data['headPairs']:
        i = round(math.exp(t))-lo-1
        assert 0 <= i < len(T) and abs(T[i]-t) < 1e-14
        full_head_coefficient[i] += amount
    joined_coefficient += full_head_coefficient
    results = []
    for y in [54., 65., 100.]:
        phase = np.exp(-1j*y*T)
        atoms = coefficient*phase
        head_atoms = full_head_coefficient*phase
        joined_atoms = joined_coefficient*phase
        p1 = complex(np.sum(atoms[prime]))
        p2 = complex(np.sum(atoms[semi]))
        raw_high = complex(np.sum(atoms[high]))
        full_head = complex(np.sum(head_atoms))
        total = complex(np.sum(joined_atoms))
        old = frozen[(N, y, (1.971, 2.029))]
        hf = head_frozen[(N, y)]
        assert abs(p1-decode(old['ordinaryPrimeBoundary'])) < 3e-12
        assert abs(p2-decode(old['semiprimeBoundary'])) < 3e-12
        assert abs(raw_high-decode(old['rawHighOwnerBoundary'])-
                   decode(old['physicalUpperFailure'])) < 3e-12
        assert abs(full_head-decode(old['sameFullOriginalHead'])) < 3e-12
        assert abs(total-p1-p2-raw_high-full_head) < 3e-12
        assert abs(p2+full_head-decode(hf['actualJoined'])) < 3e-12
        periods = np.floor(y*T/(2*math.pi)).astype(np.int64)
        bins = []
        for k in range(int(periods.min()), int(periods.max())+1):
            keep = periods == k
            z = complex(np.sum(joined_atoms[keep]))
            sp = complex(np.sum(atoms[keep & semi]))
            hp = complex(np.sum(head_atoms[keep]))
            others = complex(np.sum(atoms[keep & (prime | high)]))
            assert abs(z-sp-hp-others) < 3e-12
            high_counts = {str(c): encode(complex(np.sum(atoms[keep & high &
                            (data['count'] == c)])))
                           for c in np.unique(data['count'][high])}
            a, b = 2*math.pi*k/y, 2*math.pi*(k+1)/y
            bins.append(dict(period=k, logInterval=[a,b],
                fullPhasePeriodInsideToySupport=1.95*N <= a and b <= 2.03*N,
                fullPhasePeriodInsideCentralCore=1.971*N <= a and b <= 2.029*N,
                joined=encode(z), centralSemiprime=encode(sp),
                sameFullHead=encode(hp), ordinaryPrimeAndRawHigh=encode(others),
                rawHighByCount=high_counts))
        assert abs(sum(decode(b['joined']) for b in bins)-total) < 3e-12
        results.append(dict(N=N,height=y,
            wholeSignedBoundary=encode(total), centralOrdinaryPrime=encode(p1),
            centralSemiprime=encode(p2), rawHighOwners=encode(raw_high),
            sameFullHead=encode(full_head),
            wholeJoinedAtomPrice=float(np.abs(joined_coefficient).sum()),
            assembledPhasePeriodNormSum=sum(abs(decode(b['joined'])) for b in bins),
            completeCorePeriodNormSum=sum(abs(decode(b['joined'])) for b in bins
                if b['fullPhasePeriodInsideCentralCore']),
            coreBoundaryAndExteriorPeriodNormSum=sum(abs(decode(b['joined'])) for b in bins
                if not b['fullPhasePeriodInsideCentralCore']),
            globalSignedNorm=abs(total), periods=bins))
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[6,7,8])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert all(N in [6,7,8] for N in args.orders)
    old_path = Path('.lake/riesz-global-squarefree-completion/probe.json')
    head_path = Path('.lake/riesz-global-head-central-payment/probe.json')
    frozen = {(r['N'],r['height'],tuple(r['window'])):r
              for r in json.loads(old_path.read_text())['cases']}
    heads = {(r['N'],r['height']):r for r in json.loads(head_path.read_text())['cases']}
    rows = []
    for N in args.orders:
        print(json.dumps(dict(event='prepare',N=N)),flush=True)
        rows.extend(signed_probe(N,frozen,heads))
        for r in rows[-3:]:
            print(json.dumps({k:r[k] for k in ['N','height','wholeSignedBoundary',
                'wholeJoinedAtomPrice','assembledPhasePeriodNormSum',
                'completeCorePeriodNormSum','coreBoundaryAndExteriorPeriodNormSum',
                'globalSignedNorm']}),
                flush=True)
    paths = [Path(__file__),Path(completion.__file__),old_path,head_path]
    report = dict(schemaVersion=1,scalarEnvelope=scalar_probe(),cases=rows,
        frozenComplexRegressions=5*len(rows),
        sources=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
                 for p in paths],
        scope=dict(optionalOutsideBuildsCI=True,diagnosticOnly=True,
            toyLength='-2N log(10001/20000)',nativeMovingLength=False,
            nativeDyadicSchedule=False,nativeDeletionMasks=False,
            fullHeadAndRawHighCoefficientsPreserved=True,
            noPositiveCountAllowanceInSignedPeriodSum=True,
            noEventualPaymentAppliedAtToyOrders=True,
            phasePeriodsRetainExteriorEndpoints=True,
            noCofinalFloorOrZeroExclusionClaim=True))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
    print(json.dumps(dict(cases=len(rows),regressions=5*len(rows),
                         goalStillOpen=True)),flush=True)


if __name__ == '__main__':
    main()

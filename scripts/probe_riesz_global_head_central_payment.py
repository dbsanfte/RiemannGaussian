#!/usr/bin/env python3
"""Optional finite regression for the global central-semiprime/head join.

The frozen TOY windows, length and head are retained. Every matching head
label is joined with its actual central semiprime atom before any norm.
Outer head atoms keep their full signed phase. No eventual native budget
is used at these toy orders and no cofinal floor margin is claimed.
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


def run(N, frozen):
    data = completion.prepare(N)
    T, L = data['T'], data['L']
    central = (1971*N/1000 < T) & (T <= 2029*N/1000)
    semi = central & data['sf'] & (data['count'] == 2)
    amplitudes = np.zeros(len(T))
    amplitudes[semi] = -data['magnitude'][semi]*data['response'][semi]
    assert np.max(amplitudes, initial=0) <= 1e-14
    semi_price = -float(amplitudes.sum())
    joined = amplitudes.copy()
    head_mass, central_mass, outer_mass = 0., 0., 0.
    central_pairs, outer_pairs, labels = [], [], set()
    lo = math.floor(math.exp(1.95*N))
    for t, amount in data['headPairs']:
        n = round(math.exp(t))
        assert n not in labels
        labels.add(n)
        head_mass += amount
        i = n-lo-1
        assert 0 <= i < len(T) and abs(T[i]-t) < 1e-14
        assert data['sf'][i] and data['count'][i] == 2
        if central[i]:
            assert amount <= -amplitudes[i]+1e-14
            joined[i] += amount
            central_mass += amount
            central_pairs.append((t, amount))
        else:
            outer_mass += amount
            outer_pairs.append((t, amount))
    coupled_price = float(np.abs(joined).sum())
    assert abs(coupled_price-(semi_price-central_mass)) < 3e-12
    assert abs(head_mass-central_mass-outer_mass) < 3e-12
    rows = []
    for y in [54., 65., 100.]:
        phase = np.exp(-1j*y*T)
        semiprime = complex(np.sum(amplitudes*phase))
        full_head = sum(a*complex(math.cos(y*t), -math.sin(y*t))
                        for t, a in data['headPairs'])
        central_head = sum(a*complex(math.cos(y*t), -math.sin(y*t))
                           for t, a in central_pairs)
        outer_head = sum(a*complex(math.cos(y*t), -math.sin(y*t))
                         for t, a in outer_pairs)
        central_joined = complex(np.sum(joined*phase))
        actual = semiprime+full_head
        ref = frozen[(N, y, (1.971, 2.029))]
        assert abs(semiprime-decode(ref['semiprimeBoundary'])) < 3e-12
        assert abs(full_head-decode(ref['sameFullOriginalHead'])) < 3e-12
        assert abs(actual-(central_joined+outer_head)) < 3e-12
        assert abs(central_joined-(semiprime+central_head)) < 3e-12
        assert abs(central_joined) <= coupled_price+3e-12
        assert abs(actual) <= coupled_price+outer_mass+3e-12
        rows.append(dict(N=N, height=y, centralSemiprime=encode(semiprime),
            sameFullHead=encode(full_head), centralHead=encode(central_head),
            signedOuterHead=encode(outer_head), actualJoined=encode(actual),
            centralJoined=encode(central_joined), centralSemiprimePrice=semi_price,
            fullHeadAtomMass=head_mass, centralHeadAtomMass=central_mass,
            outerHeadAtomMass=outer_mass, centralCoupledAtomPrice=coupled_price,
            separatedCentralAtomPrice=semi_price+central_mass,
            exactCentralPriceSaving=2*central_mass,
            fullJoinedFinitePrice=semi_price-head_mass+2*outer_mass,
            everyHeadLabelHasUniqueOwner=True,
            matchedCentralLabels=len(central_pairs), outerLabels=len(outer_pairs),
            sameFullHeadPreserved=True, nativeCofinalFloorSavingClaimed=False))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[6, 7, 8])
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    assert all(N in [6, 7, 8] for N in args.orders)
    frozen_path = Path('.lake/riesz-global-squarefree-completion/probe.json')
    frozen = {(r['N'], r['height'], tuple(r['window'])): r
              for r in json.loads(frozen_path.read_text())['cases']}
    rows = []
    for N in args.orders:
        print(json.dumps(dict(event='prepare', N=N)), flush=True)
        results = run(N, frozen)
        rows.extend(results)
        r = results[0]
        print(json.dumps({k:r[k] for k in ['N','matchedCentralLabels','outerLabels',
            'centralSemiprimePrice','centralHeadAtomMass','outerHeadAtomMass',
            'exactCentralPriceSaving']}, allow_nan=False), flush=True)
    paths = [Path(__file__),Path(completion.__file__),frozen_path]
    report = dict(schemaVersion=1,cases=rows,
        frozenComplexTotalRegressions=2*len(rows),
        sources=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
                 for p in paths],
        scope=dict(optionalOutsideBuildsCI=True,diagnosticOnly=True,
            toyLength='-2N log(10001/20000)',nativeMovingLength=False,
            nativeDyadicSchedule=False,nativeDeletionMasks=False,
            noEventualBudgetAppliedAtToyOrders=True,outerHeadNotDropped=True,
            ordinaryPrimeAndRawHighOwnerBoundaryStillUnpaid=True,
            noCofinalFloorOrZeroExclusionClaim=True))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
    print(json.dumps(dict(cases=len(rows),regressions=2*len(rows),
        fullHeadPreserved=True,goalStillOpen=True)), flush=True)


if __name__ == '__main__':
    main()

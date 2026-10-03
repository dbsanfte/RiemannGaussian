#!/usr/bin/env python3
"""Optional finite regression for pole removal on the SAME signed prime head.

Every kept factorial slot, including orders zero and one, and the full
product phase are retained. The balanced main is unchanged. This diagnostic
uses the frozen toy length -2N log u, NOT native dyadic/moving-length masks.
It never applies the eventual/native exponential budget at these toy orders.
"""

import argparse
import cmath
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from scipy.stats import binom
import probe_riesz_balanced_joint as base


def encode(z):
    return dict(re=float(z.real), im=float(z.imag))


def decode(row):
    return complex(row['re'], row['im'])


def head(data, height):
    N, L = data['N'], data['L']
    C = (1.5+1j*height)/(.5+1j*height)
    kept = [k for k in range(N+2) if not N//5+1 < k <= 13*N//32]
    original_terms, filtered_terms, correction_terms = [], [], []
    boundary_terms = []
    absolute_original = 0.
    relative_bound = 0.
    maximum_ratio = 0.
    minimum_logs = [math.inf, math.inf]
    for p, q, weight, T in data['headPairs']:
        x = math.log(q)/T
        masses = binom.pmf(kept, N+1, x)
        allocated = float(masses.sum())
        assert allocated > 0
        original = (L-math.log(p))*weight*cmath.exp(-1j*height*T)
        raw = original/allocated
        multipliers = [(1-C**(N+1-k)/p)*(1-C**k/q) for k in kept]
        selected = sum(float(mass)*factor for mass, factor in zip(masses,multipliers))
        correction = raw*sum(float(mass)*(factor-1) for mass, factor in
                             zip(masses,multipliers))
        boundary = raw*sum(float(mass)*(factor-1) for k, mass, factor in
                           zip(kept,masses,multipliers) if k <= 1 or N+1-k <= 1)
        filtered = raw*selected
        assert abs(filtered-original-correction) < 5e-15*max(abs(original),1.)
        maximum_ratio = max(maximum_ratio, abs(correction)/abs(original))
        minimum_logs[0] = min(minimum_logs[0], math.log(p))
        minimum_logs[1] = min(minimum_logs[1], math.log(q))
        # Direct slotwise estimate, not the N>=64 Lean envelope.
        direct_bound = sum(float(mass)*(abs(C**(N+1-k)/p)+abs(C**k/q)+
                         abs(C**(N+1-k)/p)*abs(C**k/q))
                           for k, mass in zip(kept,masses))
        assert abs(correction) <= abs(raw)*direct_bound+1e-18
        relative_bound += abs(raw)*direct_bound
        absolute_original += abs(original)
        original_terms.append(original)
        filtered_terms.append(filtered)
        correction_terms.append(correction)
        boundary_terms.append(boundary)
    total = lambda terms: complex(math.fsum(z.real for z in terms),
                                  math.fsum(z.imag for z in terms))
    original, filtered, correction = map(total,
        [original_terms,filtered_terms,correction_terms])
    assert abs(filtered-original-correction) < 1e-13
    assert abs(correction) <= relative_bound+1e-18
    return dict(N=N,height=height,pairs=len(data['headPairs']),
        keptOrders=kept,fullSignedOriginalHead=encode(original),
        fullSignedFilteredHead=encode(filtered),exactOperatorCorrection=encode(correction),
        orderZeroOneCorrection=encode(total(boundary_terms)),
        perPairTriangleBoundSummed=relative_bound,
        originalHeadAbsoluteDiagnostic=absolute_original,
        maximumRelativePairChange=maximum_ratio,
        minimumPrimeLogs=minimum_logs,C=encode(C),C_norm=abs(C),
        allOriginalHeadMasksPhaseAndOrdersRetained=True,
        noLowerOrderDeletion=True,nativeBudgetApplied=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders',type=int,nargs='+',default=[6,7,8])
    parser.add_argument('--output',type=Path,default=Path(
        '.lake/riesz-prime-head-pole-payment/probe.json'))
    args = parser.parse_args()
    frozen_path = Path('.lake/riesz-balanced-critical-shell/probe.json')
    frozen = json.loads(frozen_path.read_text())
    old = {(r['N'],r['height'],tuple(r['window'])):r for r in frozen['cases']}
    rows, regressions = [], 0
    for N in args.orders:
        assert 3 <= N <= 8
        print(json.dumps(dict(event='prepare',N=N)),flush=True)
        data = base.prepare(N,10001/20000)
        for height in [65.,100.]:
            result = head(data,height)
            for window in [(1.95,2.03),(1.971,2.029)]:
                row = old[(N,height,window)]
                original = decode(result['fullSignedOriginalHead'])
                assert abs(original-decode(row['signedFullHead'])) < 2e-13
                main_sum = decode(row['signedMain'])
                assert abs(main_sum-original-decode(row['signedJoint'])) < 2e-13
                filtered = decode(result['fullSignedFilteredHead'])
                correction = decode(result['exactOperatorCorrection'])
                assert abs((main_sum-filtered)-(main_sum-original)+correction) < 2e-13
                regressions += 1
                rows.append(dict(**result,window=window,signedMain=encode(main_sum),
                    originalJoint=encode(main_sum-original),
                    filteredJoint=encode(main_sum-filtered),
                    exactWholeSignedCorrectionLedgerChecked=True,
                    arithmeticFloorOrCofinalBoundProved=False))
            print(json.dumps(dict(event='head',N=N,height=height,
                pairs=result['pairs'],change=result['exactOperatorCorrection'],
                allBoundaryOrdersRetained=True)),flush=True)
    sources = [Path(__file__),Path(base.__file__),frozen_path]
    report = dict(schemaVersion=1,cases=rows,frozenComplexTotalRegressions=regressions,
        sourceHashes=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
                      for p in sources],
        scope=dict(optionalOutsideBuildsCI=True,floatingNotIntervalCertificate=True,
            toyLength='-2N log(10001/20000)',nativeMovingLength=False,
            nativeDyadicSchedule=False,fullNativeDeletionMasks=False,
            noEventualBudgetAtToyOrders=True,noFloorSavingsPercentClaim=True))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(cases=len(rows),regressions=regressions,
        goalRemainsOpen=True)),flush=True)


if __name__ == '__main__':
    main()

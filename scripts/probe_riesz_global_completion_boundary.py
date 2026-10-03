#!/usr/bin/env python3
"""Optional literal-head audit of the global semiprime boundary cancellation.

The same toy head and full phase are retained. This measures cancellation
of an auxiliary completion boundary, not progress in the cofinal floor.
It never calls a previous eventual estimate at the toy orders.
"""

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


def main():
    frozen_path = Path('.lake/riesz-global-squarefree-completion/probe.json')
    frozen = json.loads(frozen_path.read_text())
    cases = []
    for N in [6, 7, 8]:
        u = 10001/20000
        L = -2*N*math.log(u)
        physical = 20000**(2*N)//10001**(2*N)
        hi = math.floor(math.exp(1.25*N))
        _, prime = base.arithmetic(hi)
        ps = np.flatnonzero(prime)
        owners = ps[(ps >= math.ceil(math.exp(1.02*N))) &
                    (ps > N*N) & (ps < physical)]
        orders = np.arange(N//5+2, 13*N//32+1)
        pairs = []
        for p in owners:
            c = math.log(int(p))
            lo, top = math.floor(math.exp(1.95*N-c)), math.floor(math.exp(2.03*N-c))
            for q in ps[(ps > max(lo, N**3)) & (ps <= top)]:
                d, T = math.log(int(q)), math.log(int(p)*int(q))
                weight = math.exp((N+1)*math.log(u)-1.5*T+(N+1)*math.log(T)
                                  -math.lgamma(N+1))/L
                allocation = 1-float(binom.pmf(orders,N+1,d/T).sum())
                old = (L-c)*allocation*weight
                response = max(L,0.)-max(L-c,0.)-max(L-d,0.)+max(L-c-d,0.)
                assert abs(response-(T-L)) < 5e-14
                new = response*weight
                assert new >= old >= 0.
                # This lower bound is also checked on these toy rows, but
                # the native Lean theorem has its separate N>=65536 regime.
                assert response-(L-c)*allocation >= .17*N-1e-12
                pairs.append((T,new,old))
        old_mass = math.fsum(o for _,_,o in pairs)
        new_mass = math.fsum(b for _,b,_ in pairs)
        joined_mass = math.fsum(b-o for _,b,o in pairs)
        assert abs(joined_mass-(new_mass-old_mass)) < 2e-13
        for y in [54.,65.,100.]:
            phase = lambda t: complex(math.cos(y*t),-math.sin(y*t))
            head = sum(o*phase(t) for t,_,o in pairs)
            boundary = sum(b*phase(t) for t,b,_ in pairs)
            coupled = sum((b-o)*phase(t) for t,b,o in pairs)
            assert abs(coupled-(boundary-head)) < 2e-13
            old_cases = [r for r in frozen['cases'] if r['N']==N and r['height']==y]
            assert len(old_cases)==2
            for r in old_cases:
                h = r['sameFullOriginalHead']
                assert abs(head-complex(h['re'],h['im'])) < 2e-12
            cases.append(dict(N=N,height=y,pairs=len(pairs),sameFullHead=encode(head),
                              matchedSemiprimeBoundary=encode(boundary),
                              coupledBoundary=encode(coupled),heightZeroHead=old_mass,
                              separateAtomNormPrice=new_mass+old_mass,
                              coupledAtomNormPrice=joined_mass,
                              exactAtomNormSaving=2*old_mass,
                              everyLiteralHeadLabelMatched=True,
                              nativeFloorSavingClaimed=False,
                              globalPrimeAndHighOwnerBoundariesStillUnpaid=True))
    paths = [Path(__file__),Path(base.__file__),frozen_path]
    output = Path('.lake/riesz-global-squarefree-completion/boundary-probe.json')
    output.write_text(json.dumps(dict(schemaVersion=1,cases=cases,headComplexRegressions=18,
        sources=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths],
        scope=dict(optionalOutsideBuildsCI=True,toyLength=True,nativeMovingLength=False,
                   nativeDyadicSchedule=False,noEventualBudgetApplied=True,
                   noWholeFloorOrZeroExclusionClaim=True)),indent=2,allow_nan=False)+'\n')
    print(json.dumps(dict(cases=len(cases),headComplexRegressions=18,
                         oldHeadMassByOrder={N:next(r['heightZeroHead'] for r in cases if r['N']==N)
                                            for N in [6,7,8]},goalStillOpen=True)))


if __name__=='__main__':
    main()

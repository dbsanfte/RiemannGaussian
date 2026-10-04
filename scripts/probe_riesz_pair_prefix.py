#!/usr/bin/env python3
"""Optional quantitative regression of the proved global prefix payment.

Replay the existing actual-prime cache; no new prime density or phase model.
The finite sample checks algebra only and is below the theorem's N>=65536
threshold. Rational tilt exponents and large-order budgets are diagnostics;
Lean proves the bounds on the whole literal support. This does not estimate
the remaining signed main or certify the floor.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import numpy as np
from flint import arb, ctx
from scipy.stats import binom

import probe_riesz_pair_structure as pair


def digest(path):
    return dict(path=str(path), sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest())


def comparison(N, L, x, z):
    T = x+z
    F = binom.cdf(13*N//32, N+1, z/T)
    G = binom.cdf(N//5+1, N+1, z/T)
    other = binom.cdf(13*N//32, N+1, x/T)
    alpha = T/L*(L-x)
    # Stable complementary tail; do not compute 1-cdf when it is tiny.
    tail = binom.sf(13*N//32, N+1, z/T)
    owner_error = np.where(x < 1.02*N, alpha*F,
                   np.where(x <= 1.25*N, alpha*G, -alpha*tail))
    nonowner_error = T/L*(L-z)*other
    prefix = T*(1-T/L)-alpha*F-nonowner_error
    return prefix, owner_error+nonowner_error


def run(cache):
    samples = json.loads(cache.read_text())
    rows = []
    max_replay = 0.
    pairs = 0
    for row in samples['rows']:
        N = row['N']
        ctx.prec = max(1200, math.ceil(2*N/math.log(2))+256)
        left = np.array([int(p) for p in row['left']['primes']], dtype=object)
        right = np.array([int(p) for p in row['right']['primes']], dtype=object)
        assert row['left']['provedByFLINT'] and row['right']['provedByFLINT']
        # Reuse the proven cache, checking product geometry again.
        assert min(left) > max(right) > N**16
        x = np.array([float(arb(p).log().mid()) for p in left])[:, None]
        z = np.array([float(arb(q).log().mid()) for q in right])[None, :]
        c = pair.coefficient(N, left[:, None], right[None, :], x, z)
        assert np.all(c['central'])
        T = c['T']
        L = pair.parameters(N)['L']
        assert np.all(T > L) and np.all(z <= L)
        prefix, stable_error = comparison(N, L, x, z)
        replay = float(np.max(np.abs(c['joined']-prefix-stable_error)))
        assert replay < 2e-10*max(1., float(np.max(np.abs(c['joined']))))
        max_replay = max(max_replay, replay)
        pairs += int(T.size)
        rows.append(dict(N=N, seed=row['seed'], box=row['box'], share=row['share'],
            actualPairIncidences=int(T.size),
            maxCoefficientErrorOverN=float(np.max(np.abs(stable_error))/N),
            algebraReplayMaxAbsoluteError=replay,
            formalThresholdMet=(N >= 65536)))

    rates = dict(
        highOwner=(13/32)*math.log(11/10)-math.log(2077/2000),
        lowOwner=-((13/32)*math.log(10/9)+math.log(119/125)),
        headLowerEndpoint=-((1/5)*math.log(5/4)+math.log(116/125)))
    assert rates['highOwner'] > 1/1250
    assert rates['lowOwner'] > 1/250
    assert rates['headLowerEndpoint'] > 1/40
    growth = math.log(2*pair.U)
    assert 1/1250-growth > 1/1600
    budgets = []
    for N in (256, 640, 1536, 3584, 8192, 18432, 40960, 65536, 90112, 196608):
        logbudget = math.log(12)+2+math.log(N+1)-N/1600
        budgets.append(dict(N=N, bound=math.exp(logbudget), logBound=logbudget,
            formalThresholdMet=(N >= 65536)))
    return dict(classification='Regression of globally proved coefficient-error payment only',
        sourceHead='49db91eb2f5ea148c82b00bae9f241a836c272fe',
        sources=[digest(p) for p in (
            'scripts/probe_riesz_pair_prefix.py',
            'RiemannGaussian/ZetaRieszPairPrefixPayment.lean',
            'scripts/probe_riesz_pair_structure.py', cache)],
        replay=dict(rows=rows, actualPairIncidences=pairs,
            maxAlgebraReplayError=max_replay, sharedPrimesNotIndependent=True,
            cachePrimalityReproved=False, belowFormalThreshold=True),
        uniformTiltExponents=rates, sourceGrowthCeiling=growth,
        leanCoefficientExponent=1/1250, leanSourceScaledExponent=1/1600,
        globalErrorBudget='12*exp(2)*(N+1)*exp(-N/1600), N>=65536',
        budgetDiagnostics=budgets, independentSignedMainBound=False,
        floorBound=False, achievedFloorMargin=0)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cache', type=Path, default=Path('.lake/riesz-pair-structure/scan.primes.json'))
    ap.add_argument('--output', type=Path, default=Path('.lake/riesz-pair-prefix-payment/probe.json'))
    args = ap.parse_args()
    result = run(args.cache)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(output=str(args.output),
        actualPairIncidences=result['replay']['actualPairIncidences'],
        maxAlgebraReplayError=result['replay']['maxAlgebraReplayError'],
        floorBound=False)))


if __name__ == '__main__':
    main()

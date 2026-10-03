#!/usr/bin/env python3
"""Optional finite rough-owner comparison diagnostic, outside builds/CI.

Exhaust the TOY cofactor interval, retaining the actual binomial owner
selector, total-log factorial weight, phase, squarefree and rough masks.
Compute the density scalar and prime-cofactor subtraction jointly. This
checks signs/normalization and mask variation; it is NOT a native carrier,
an interval certificate, or evidence for a cofinal floor/rate. In particular
the toy interval does NOT satisfy exp(N/2)<=M or the original core window.
The proved geometric comparison is not claimed applicable to this toy.
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


def arithmetic(limit):
    spf = np.zeros(limit+1, dtype=np.int64)
    for p in range(2, limit+1):
        if spf[p] == 0:
            for n in range(p, limit+1, p):
                if spf[n] == 0:
                    spf[n] = p
    mu = np.ones(limit+1, dtype=np.int8)
    count = np.zeros(limit+1, dtype=np.int8)
    marks = np.ones(limit+1)
    mu[0] = 0
    for n in range(2, limit+1):
        p = int(spf[n])
        m = n//p
        if m % p == 0:
            mu[n] = 0
            count[n] = count[m]
            marks[n] = marks[m]
        else:
            mu[n] = -mu[m]
            count[n] = count[m]+1
            marks[n] = marks[m]/(p+1)
    prime = spf == np.arange(limit+1)
    prime[:2] = False
    return mu, count, marks, prime


def case(mu, count, marks, prime, N, p, M, X, b, height, forbidden):
    axis = np.arange(X+2)
    rough = np.ones(X+2, dtype=bool)
    for q in forbidden:
        rough[q::q] = False
    rough[0] = False
    sf = mu != 0
    sieve = sf & rough
    composite = sieve & ~prime & (axis > 1)
    active = (axis > M) & (axis <= X)
    logs = np.log(np.maximum(axis, 1))
    c = math.log(p)
    T = c+logs
    share = logs/T
    orders = np.arange(N//5+2, 13*N//32+1)
    assert len(orders) > 0
    # EXACT finite factorial selector, evaluated in floating arithmetic.
    allocation = binom.pmf(orders[:, None], N+1, share[None, :]).sum(axis=0)
    amplitude = (1-allocation)*np.exp(-T/2)*T**(N+1)/math.factorial(N)
    w = np.where(active, amplitude*np.cos(height*T)/np.maximum(axis, 1), 0.)
    R = math.floor(math.exp(b))
    assert R <= M and R**4 <= M**3 and X < p
    riesz = np.zeros(X+2)
    for d in range(1, R+1):
        riesz[d::d] += int(mu[d])*max(b-math.log(d), 0.)
    rho = 6/math.pi**2
    for q in forbidden:
        rho *= q/(q+1)
    density = rho*sum(int(mu[d])*marks[d]*max(b-math.log(d), 0.)
                      for d in range(1, R+1) if rough[d])
    density_main = density*w.sum()
    prime_head = b*w[prime & sieve].sum()
    literal = float((w*riesz*composite).sum())
    main = density_main-prime_head
    norm = (.50005**(N+1))/(p*(c+b))
    smooth_variation = float((axis[1:X+1]*np.abs(w[1:X+1]-w[2:X+2])).sum())
    extended = w*composite
    masked_variation = float((axis[1:X+1]*
        np.abs(extended[1:X+1]-extended[2:X+2])).sum())
    by_count = {str(k+1): norm*float((w*riesz*(composite & (count == k))).sum())
                for k in sorted(set(count[composite & active].tolist()))}
    assert abs(sum(by_count.values())-norm*literal) <= 1e-12*max(1, abs(norm*literal))
    # Independently expand the finite divisor profile, WITHOUT count splitting.
    expanded = sum(int(mu[d])*max(b-math.log(d), 0.)*
        sum(w[n] for n in range(d, X+1, d) if composite[n])
        for d in range(1, R+1))
    assert abs(expanded-literal) <= 1e-9*max(1, abs(literal))
    return dict(N=N, owner=p, M=M, X=X, cutoff=b, height=height,
        forbiddenPrimes=forbidden, compositeLabels=int((composite & active).sum()),
        sourceScaledLiteral=norm*literal, sourceScaledDensityMain=norm*density_main,
        sourceScaledPrimeHead=norm*prime_head, sourceScaledJoinedMain=norm*main,
        sourceScaledSignedError=norm*(literal-main),
        sourceScaledErrorIfPrimeHeadDropped=norm*(literal-density_main),
        smoothWeightVariation=smooth_variation, zeroExtendedVariation=masked_variation,
        maskedToSmoothVariationRatio=masked_variation/smooth_variation,
        joinedCountDiagnostic=by_count,
        divisorExpansionResidual=expanded-literal,
        support=dict(NativeCofinalPoint=False, originalCoreWindow=False,
            largeCofactorHypothesis=False, geometricTheoremApplied=False))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path('.lake/riesz-rough-owner-comparison/probe.json'))
    args = parser.parse_args()
    N, p, M, X = 32, 100003, 5000, 10000
    assert all(p % d for d in range(2, math.isqrt(p)+1))
    mu, count, marks, prime = arithmetic(X+1)
    cases = [case(mu, count, marks, prime, N, p, M, X, b, height, forbidden)
             for b in (3., 4.) for height in (54., 65., 100.)
             for forbidden in ([2, 3], [2, 3, 5, 7])]
    report = dict(schemaVersion=1, cases=cases,
        source=dict(path=str(Path(__file__).resolve()),
                    sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),
        scope=dict(optionalOutsideBuildsAndCI=True, toyIntegerIntervalExhausted=True,
            exactFactorialOrdersRetained=True, phaseSquarefreeRoughMasksRetained=True,
            allCountsJoinedBeforeMainComparison=True, primeHeadNeverDropped=True,
            noSamplingImportanceWeights=True, floatingDensityLogsPhaseAndProbabilities=True,
            nativeOrOriginalCorePacket=False, geometricTheoremApplied=False,
            cofinalFloorOrZeroExclusionProved=False))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    for c in cases:
        print(json.dumps({k: c[k] for k in ('cutoff', 'height', 'forbiddenPrimes',
            'sourceScaledLiteral', 'sourceScaledSignedError', 'sourceScaledPrimeHead',
            'maskedToSmoothVariationRatio')}, allow_nan=False), flush=True)


if __name__ == '__main__':
    main()

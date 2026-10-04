#!/usr/bin/env python3
"""Optional exact/regression checks for whole signed pair completion.

This checks coefficient bookkeeping and a small genuine-prime universe.
It does not evaluate the exhaustive literal carrier or certify the unknown
edge constant. All sampled orders are below the proved N>=65536 threshold.
Keep it outside ordinary builds/CI.
"""

import argparse
from fractions import Fraction as F
import itertools
import json
import math
from pathlib import Path

import mpmath as mp


def lower(N, K, q):
    return sum(math.comb(N, k)*q**k*(1-q)**(N-k)
               for k in range(min(K, N)+1))


def coefficients(N, L, x, z):
    T = x+z
    fx, fz = lower(N+1, 13*N//32, x/T), lower(N+1, 13*N//32, z/T)
    Q = T*(1-T/L)-T/L*((L-x)*fz+(L-z)*fx)
    selberg = -2*x*z/T
    intercept = T*(1-fx-fz)-selberg
    slope = -T+x*fz+z*fx
    return Q, selberg, intercept, slope


def exact_split_checks():
    rows = []
    for N in (*range(65), 97, 256):
        for x, z in ((1, 1), (1, 31), (31, 1), (3, 7), (7, 3), (13, 19), (97, 3)):
            x, z, L = F(x), F(z), F(7*(N+1), 5)
            Q, selberg, A, B = coefficients(N, L, x, z)
            assert Q-selberg == A+(x+z)/L*B
            assert abs(A) <= 2*(x+z) and abs(B) <= x+z
            assert coefficients(N, L, z, x) == (Q, selberg, A, B)
            rows.append(dict(N=N, x=int(x), z=int(z), splitExact=True,
                             interceptAndSlopeBounds=True, swappedIncidencePreserved=True))
    Q, selberg, A, B = coefficients(8, F(63, 5), F(13), F(19))
    assert Q-selberg != A+B  # Missing total-log/length factor is detected.
    return dict(checks=len(rows), exactRationalArithmetic=True,
                wrongSlopeScaleRejected=True, orders=sorted({r['N'] for r in rows}))


def finite_prime_checks():
    primes = [2, 3, 5, 7, 11, 97, 257, 1009, 5003, 9973, 100003]
    assert all(p>1 and all(p%d for d in range(2, math.isqrt(p)+1)) for p in primes)
    rows = []
    mp.mp.dps = 90
    for N, u, y in itertools.product((1, 4, 8, 16, 32, 64),
                                    (mp.mpf(1)/2, mp.mpf(10001)/20000), (54, -54, 142)):
        # A positive length suffices for this finite algebra regression;
        # the literal moving length is used in Lean, not approximated here.
        L = mp.mpf(7)*(N+1)/5
        s, M, K = mp.mpf(3)/2+1j*y, N+1, 13*N//32
        moments = [sum(mp.log(p)**k/mp.factorial(k)*mp.exp(-s*mp.log(p))
                       for p in primes) for k in range(N+3)]
        central = M*sum(moments[k]*moments[M-k] for k in range(K+1, M-K))/2
        central -= M*(M+1)*sum(moments[k]*moments[M+1-k]
                              for k in range(K+1, M+1-K))/(2*L)
        central -= M*sum(k*moments[k]*moments[M+1-k] for k in range(1, K+1))/L
        Qdiag = sum(coefficients(N, L, mp.log(p), mp.log(p))[0]*
                    (2*mp.log(p))**N/mp.factorial(N)*mp.exp(-s*2*mp.log(p)) for p in primes)/2
        direct, joined, interior_added = 0j, 0j, 0
        intercept_error, atom_error = mp.mpf(0), mp.mpf(0)
        width = 2*mp.pi/abs(y)
        exterior_A, exterior_B, literal = 0j, 0j, 0j
        selberg_sum = 0j
        retained = 0
        for p, q in itertools.combinations(primes, 2):
            x, z, T = mp.log(max(p, q)), mp.log(min(p, q)), mp.log(p*q)
            Q, selberg, A, B = coefficients(N, L, x, z)
            kernel = T**N/mp.factorial(N)*mp.exp(-s*T)
            successor = T**(N+1)/mp.factorial(N+1)*mp.exp(-s*T)
            atom_error = max(atom_error, abs((Q-selberg)*kernel-(A*kernel+M/L*B*successor)))
            intercept_error = max(intercept_error, max(mp.mpf(0), abs(A)-2*T, abs(B)-T))
            atom = (Q-selberg)*kernel
            direct += atom
            selberg_sum += selberg*kernel
            left = mp.floor(T/width)*width
            keep = mp.mpf(1971)*N/1000 <= left and left+width <= mp.mpf(2029)*N/1000
            if keep:
                literal += atom
                retained += 1
            else:
                exterior_A += A*kernel
                exterior_B += B*successor
                interior_added += int(mp.mpf(1971)*N/1000+1 < T <= mp.mpf(2029)*N/1000-1)
        joined = central-Qdiag-selberg_sum
        completion_error = abs(u**M*(direct-literal-exterior_A-M/L*exterior_B))
        convolution_error = abs(u**M*(direct-joined))
        assert max(completion_error, convolution_error, atom_error, intercept_error) < mp.mpf('1e-70')
        assert interior_added == 0
        def encode(value):
            return dict(re=mp.nstr(mp.re(value), 85), im=mp.nstr(mp.im(value), 85))
        rows.append(dict(N=N, u=str(u), y=y, finitePrimeUniverse=primes, retainedPairs=retained,
                         allDistinctPairs=math.comb(len(primes), 2), addedInteriorPairs=interior_added,
                         sourceScaledFinite=encode(u**M*direct), sourceScaledLiteral=encode(u**M*literal),
                         sourceScaledExteriorIntercept=encode(u**M*exterior_A),
                         sourceScaledExteriorSlope=encode(u**M*M/L*exterior_B),
                         completionIdentityError=float(completion_error),
                         joinedConvolutionError=float(convolution_error), atomSplitError=float(atom_error)))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    exact = exact_split_checks()
    rows = finite_prime_checks()
    mp.mp.dps = 90
    U, sigma = mp.mpf(10001)/20000, 1+mp.mpf(1)/10000000
    tilts = []
    for b in (mp.mpf(1971)/1000, mp.mpf(2029)/1000):
        exponent = mp.log(U*b)+1+(sigma-mp.mpf(3)/2)*b
        assert exponent < -mp.mpf(1)/1000000
        tilts.append(dict(radialSlope=str(b), exponent=mp.nstr(exponent, 80)))
    output = dict(exactCoefficientChecks=exact, finitePrimeRegressions=rows, tiltDiagnostics=tilts,
                  finiteUniverseIsExhaustiveLiteralCarrier=False,
                  regressionLength='7*(N+1)/5; generic positive-length algebra only',
                  sourceNormalizationUsed=True, fullComplexPhaseRetained=True,
                  allSampledOrdersBelowFormalThreshold=True, geometricConstantNumericallyPriced=False,
                  optionalOutsideCI=True, independentSignedMainBoundProved=False, floorCredit=0)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(dict(exactChecks=exact['checks'], finiteCases=len(rows),
                          maxReplayError=max(r['joinedConvolutionError'] for r in rows),
                          unpaidSignedMain=True)))


if __name__ == '__main__':
    main()

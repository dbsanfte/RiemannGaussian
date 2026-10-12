#!/usr/bin/env python3
"""Exact incidence ledgers and diagnostic phases for the signed CRT audit.

Floating logarithms, PNT comparisons and phase signs are not proof input.
Every selected pair is an actual prime pair and its native incidence is
counted by exact CRT arithmetic. This does not sample a hypothetical zero.
"""
from __future__ import annotations

import argparse
import bisect
import cmath
import json
import math
from fractions import Fraction
from pathlib import Path

from probe_arithmetic_operator_growing_schur import primes_to


def incidence(X: int, p: int, q: int) -> int:
    if math.gcd(p, q) != 1:
        return 0
    first = p * (-pow(p, -1, q) % q)
    if first == 0:
        first = p * q
    return 0 if first > X else 1 + (X-first)//(p*q)


def probe(ceiling: int) -> dict:
    primes = primes_to(ceiling)
    exact_pairs = exact_ledgers = float_pairs = 0
    cases = []
    for y in (1.0, 2.0, 54.0, -54.0, 65.0, 100.0, 350.0):
        A = math.exp(1/(8*abs(y)))
        B = math.exp(1/(4*abs(y)))
        c = (A-1)**2/72
        targets = (10_000,) if abs(y) < 54 else (10_000, 100_000, 700_000, 1_700_000)
        for target in targets:
            J = math.floor((abs(y)*math.log(target)-0.25)/(2*math.pi))
            if J < 0:
                continue
            x = math.exp((J*2*math.pi+0.25)/abs(y))
            H = math.ceil(B*x/4)
            X = 4*H
            assert B*x < ceiling and X <= 3*x
            P = primes[bisect.bisect_right(primes,x):bisect.bisect_right(primes,A*x)]
            Q = primes[bisect.bisect_right(primes,A*x):bisect.bisect_right(primes,B*x)]
            if not P or not Q:
                continue
            assert set(P).isdisjoint(Q)
            rational_sum = Fraction(0)
            floating = 0j
            smallest_relative_phase = 1.0
            for p in P:
                for q in Q:
                    assert p < q and 2*H < p <= X and 2*H < q <= X
                    count = incidence(X, p, q)
                    assert count == 0
                    # Integer surrogate coefficients, deliberately NOT Gamma data.
                    wp, wq = p % 7 + 1, q % 11 + 1
                    delta = Fraction(count)-Fraction(X,p*q)
                    if p in P[:16] and q in Q[:16]:
                        rational_sum += wp*wq*delta
                    exact_pairs += 1
                    relative = cmath.exp(1j*y*(math.log(q)-math.log(p)))
                    smallest_relative_phase = min(smallest_relative_phase,relative.real)
                    assert relative.real >= 0.5-1e-9
                    floating += math.log(p)*math.log(q)*float(delta)*relative
                    float_pairs += 1
            # Exact whole masked pair ledger, before any norm or real part.
            expected = -X*sum((Fraction(p%7+1,p) for p in P[:16]),Fraction(0))*sum(
                (Fraction(q%11+1,q) for q in Q[:16]),Fraction(0))
            assert rational_sum == expected
            exact_ledgers += 1
            lp = sum(math.log(p) for p in P)
            lq = sum(math.log(q) for q in Q)
            lower_mass = (A-1)*x/2
            # Qualitative PNT eventual premises are checked at these finite samples
            # only; they are NOT certified by this diagnostic.
            mass_premises = lp >= lower_mass and lq >= lower_mass
            if mass_premises:
                assert -floating.real >= c*X-1e-7
            left = sum(math.log(p)/p*cmath.exp(-1j*y*math.log(p)) for p in P)
            right = sum(math.log(q)/q*cmath.exp(-1j*y*math.log(q)) for q in Q)
            rank_one = -X*left*right.conjugate()
            residual = abs(floating-rank_one)
            assert residual <= 1e-8*max(1,abs(floating))
            cases.append({'diagnosticHeight':y,'J':J,'lowerRealCutoff':x,
                          'nativeEvenCutoff':X,'lowerPrimeCount':len(P),'upperPrimeCount':len(Q),
                          'actualIncidence':0,'minimumRelativePhaseReal':smallest_relative_phase,
                          'signedBoundaryReal':floating.real,'signedBoundaryImag':floating.imag,
                          'negativeRealOverNativeCutoff':-floating.real/X,
                          'analyticLowerConstant':c,'samplePNTPremisesSatisfied':mass_premises,
                          'complexRankOneResidual':residual,'proofInput':False})
    return {'scope':'literal phase-compatible signed CRT completion, not prescribed RH carrier',
            'checksPassed':True,'proofInput':False,'integerPrimeCeiling':ceiling,
            'exact':{'nativePrimePairIncidenceChecks':exact_pairs,
                     'rationalWholeSelectedMaskLedgers':exact_ledgers,
                     'rationalLedgerUsesFirst16PrimesPerBand':True,
                     'maskKeepsBothNativeEndpoints':True,'properPowersOutsideMaskPaid':False,
                     'integerSurrogateWeightsGrantedGammaCompatibility':False},
            'floatingDiagnosticOnly':{'relativePhaseAndBoundaryChecks':float_pairs,'cases':cases},
            'asymptoticOrActualZeroSourceInferredFromSamples':False,
            'linearBoundaryIsZeroModeContribution':False,
            'actualDensityPoleCancelledByFiniteCRTSubtractionClaimed':False,
            'newRHEndpointOrZeroExclusionClaimed':False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ceiling',type=int,default=2_000_000)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=probe(args.ceiling)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'checksPassed':result['checksPassed'],'proofInput':False,
                      'exact':result['exact'],'floatingCases':len(result['floatingDiagnosticOnly']['cases'])}))


if __name__=='__main__':
    main()

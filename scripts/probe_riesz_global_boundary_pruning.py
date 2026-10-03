#!/usr/bin/env python3
"""Optional exact-divisor support diagnostic for native physical failures.

Native order N=256 and L=log((floor(u^-N/(N+1))+2)^2) are kept exactly.
The cutoff comparison d<X uses integers. Riesz responses are represented
as integer linear combinations of log(X) and individual prime logs,
before any floating phase or norm. Primes are exploratory SymPy values,
not Lean primality certificates. This is not a count-tail or floor bound.
"""

import argparse
import itertools
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import sympy


def log_profile(X, primes):
    constant = 0
    coefficients = dict.fromkeys(primes, 0)
    active = 0
    for bits in itertools.product((False, True), repeat=len(primes)):
        selected = [p for p, b in zip(primes, bits) if b]
        d = math.prod(selected)
        if d >= X:
            continue
        active += 1
        mu = (-1)**len(selected)
        constant += mu
        for p in selected:
            coefficients[p] -= mu
    return dict(constant=constant,
                primeCoefficients={str(p): v for p, v in coefficients.items() if v},
                activeDivisors=active)


def model(N=256):
    cutoff = pow(20000, N) // (pow(10001, N) * (N+1))
    X = (cutoff+2)**2
    L = math.log(X)
    assert L >= 5*N/4
    p = int(sympy.nextprime(X))
    rows = []
    for count in range(3, 13):
        log_root = (2*N-math.log(p))/(count-1)
        seed = math.floor(math.exp(log_root))
        middle = []
        q = seed
        for _ in range(count-1):
            q = int(sympy.nextprime(q))
            middle.append(q)
        assert len(set([p]+middle)) == count
        a = math.prod(middle)
        n = p*a
        T = math.log(n)
        assert a < X <= p
        assert 1971*N/1000 < T <= 2029*N/1000
        profile = log_profile(X, [p]+middle)
        assert profile['constant'] == 0
        assert profile['primeCoefficients'] == {}
        rows.append(dict(count=count, p=str(p), cofactors=list(map(str, middle)),
                         logRatio=T/N, exactRieszLogProfile=profile,
                         arithmeticCoefficientExactlyZero=True,
                         fullPhasePreservedAtHeights=[54, 65, 100]))
    q = int(sympy.nextprime(math.floor(math.exp(2*N-math.log(p)))))
    semiprime = log_profile(X, [p, q])
    assert semiprime['constant'] == 0
    assert semiprime['primeCoefficients'] == {str(q): 1}
    prime_label = int(sympy.nextprime(math.floor(math.exp(2*N))))
    assert 1971*N/1000 < math.log(prime_label) <= 2029*N/1000
    assert X <= prime_label
    prime = log_profile(X, [prime_label])
    assert prime['constant'] == 1 and prime['primeCoefficients'] == {}
    return dict(N=N, radius='10001/20000', nativeLinearCutoff=str(cutoff),
                nativePhysicalCutoff=str(X), nativeLength=L,
                rows=rows,
                semiprimeNegativeControl=dict(p=str(p), q=str(q),
                    exactRieszLogProfile=semiprime, response='log(q)',
                    boundaryNotDiscarded=True),
                ordinaryPrimeNegativeControl=dict(p=str(prime_label),
                    exactRieszLogProfile=prime, response='log(X)',
                    restoredPrimeBoundaryNotDiscarded=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    report = dict(schemaVersion=1, diagnosticOnly=True,
                  actualNativeFloorAndPhysicalCutoff=True,
                  noAsymptoticBudgetAppliedAtFiniteOrder=True,
                  noNativeLowCountMembershipInferred=True,
                  noPrimeCertificationOrFloorClaim=True,
                  exactIntegerSubsetSignsRetained=True, model=model())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print('10 count classes: exact saturated-cofactor log profiles are zero.')
    print('Semiprime and ordinary-prime controls retain their nonzero boundaries.')
    print('No cofinal floor, raw-owner payment or prime certificate claimed.')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Optional comparison of actual shell masses and all-count costs.

This does not evaluate the retained carrier or certify its floor. The
complete-period theorem retains its original cofactor cap and whole-fibre
membership requirement. The owner-boundary theorem also retains its actual
short radial window. Comparison constants are deliberately coarse.
"""

from fractions import Fraction
from itertools import combinations
import json
import math

from probe_riesz_symmetric_period import constant_logs


def primes_to(n):
    sieve = bytearray(b"\x01") * (n+1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(n)+1):
        if sieve[p]:
            sieve[p*p::p] = b"\x00"*((n-p*p)//p+1)
    return [p for p in range(2, n+1) if sieve[p]]


def response(k):
    capacities = [max((math.comb(k-2, j) for j in range(k-1)
                       if j % 2 == parity), default=0) for parity in (0, 1)]
    return 2*(1+sum(capacities))


def finite_symmetry():
    p = (3, 5, 7, 11, 13, 17, 19, 23)
    mass = sum((Fraction(1, q) for q in p), Fraction(0))
    result = []
    for k in range(1, len(p)+1):
        squarefree = sum((math.prod(Fraction(1, q) for q in U)
                          for U in combinations(p, k)), Fraction(0))
        assert math.factorial(k)*squarefree <= mass**k
        result.append(dict(k=k, reciprocalMass=str(squarefree),
                           exactFactorialInequality=True))
    return result


def main():
    M = 5*math.log(4)
    primes = primes_to(math.ceil(math.exp(12)))
    actual = []
    for H in (1, 1.5, 2, 3):
        P = [p for p in primes if H <= math.log(p) <= 4*H]
        mass = math.fsum(1/p for p in P)
        assert mass <= M
        actual.append(dict(H=H, count=len(P), actualReciprocalMass=mass,
                           uniformUpperBound=M))
    costs = []
    for k in (6, 10, 20, 40, 100, 256):
        price = 200000*response(k)+1200*(k+1)*response(k)+400*2**k
        new = math.log(price)+k*math.log(M)-math.lgamma(k+1)
        upper = math.log(1207600)+k*math.log(4*M)-math.lgamma(k+1)
        boundary = (math.log(512*(k+2)*response(k+2))+k*math.log(M)
                    - math.lgamma(k+1))
        bupper = math.log(24576)+k*math.log(4*M)-math.lgamma(k+1)
        assert new <= upper+1e-12 and boundary <= bupper+1e-12
        costs.append(dict(k=k,
                          oldLogCost=constant_logs(k)["symmetricLogPopulationCost"],
                          shellLogCost=new, closeOwnerLogCost=boundary,
                          compatibleOriginalCofactorCapNotInferred=True))
    print(json.dumps(dict(diagnosticOnly=True, actualShellMasses=actual,
                         finiteSquarefreeSymmetry=finite_symmetry(), countCosts=costs,
                         coarseAllCountConstant=1207600*math.exp(4*M),
                         coarseAllBoundaryConstant=24576*math.exp(4*M),
                         completePeriodsRequired=True,
                         originalCofactorCapRetained=True,
                         otherOwnerHolesPaid=False,
                         relativeRadialBoundOnly=True,
                         sourceScaleDecayClaimed=False,
                         effectiveStartingOrderCertified=False,
                         wholeFloorCertified=False), indent=2))


if __name__ == "__main__":
    main()

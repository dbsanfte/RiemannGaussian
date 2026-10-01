#!/usr/bin/env python3
"""Optional diagnostics for signed owner-period and clipped-start costs.

The finite labels below only check the ownership geometry; their logarithms
are below the Lean theorem's eventual Chebyshev threshold. No numerical
prime-period cancellation, effective start, source decay or floor is certified.
This is outside ordinary builds and CI.
"""
from fractions import Fraction
from itertools import combinations
import json
import math


def primes_upto(limit):
    sieve = [True]*(limit+1)
    sieve[0:2] = [False, False]
    for p in range(2, math.isqrt(limit)+1):
        if sieve[p]:
            for n in range(p*p, limit+1, p):
                sieve[n] = False
    return [p for p in range(2, limit+1) if sieve[p]]


def ownership_rows():
    ps = primes_upto(269)
    rows = []
    y = 54
    for count in (7, 11, 21):
        for q, clipped in ((263, True), (229, False)):
            cofactor = [q] + [p for p in ps if 53 <= p < q][-count+2:]
            assert len(cofactor) == count-1 and len(set(cofactor)) == count-1
            p = 269
            T = math.log(p)+math.fsum(math.log(t) for t in cofactor)
            v = T-0.9*math.pi/y
            P0 = v-math.pi/y-math.fsum(math.log(t) for t in cofactor)
            is_clipped = any(math.log(t) > P0 for t in cofactor)
            gap = math.log(p)-math.log(q)
            assert is_clipped == clipped
            assert not is_clipped or gap < 1/8
            rows.append(dict(totalPrimeCount=count, owner=p, secondPrime=q,
                             actualSquarefreeFactors=[p]+cofactor,
                             ownerStartClipped=is_clipped,
                             closeOwner=gap < 1/8,
                             ownerLogGap=gap,
                             geometryOnly=True,
                             eventualPrimeMassThresholdSatisfied=False))
    return rows


def exact_symmetry():
    ps = [5, 7, 11, 13, 17, 19]
    results = []
    for k in range(len(ps)+1):
        mass = sum((Fraction(1, math.prod(U)) for U in combinations(ps, k)), Fraction())
        ordered_mass = math.factorial(k)*mass
        assert ordered_mass/math.factorial(k) == mass
        results.append(dict(count=k, squarefreeReciprocalMass=str(mass),
                            orderedDistinctMass=str(ordered_mass),
                            exactSymmetryFactor=math.factorial(k)))
    return results


def main():
    lam = 10*math.log(4)
    owner = 481*4**10
    boundary = 1536*4**10
    total = owner+boundary
    assert total == 2114977792
    contributions = [math.exp(k*math.log(lam)-math.lgamma(k+1))
                     for k in range(256)]
    all_count_mass = math.exp(lam)
    assert math.isclose(math.fsum(contributions), all_count_mass, rel_tol=2e-14)
    max_order = max(range(len(contributions)), key=contributions.__getitem__)
    prices = []
    for log_N in (1250, 2500, 10000):
        # N is intentionally represented in the log domain, not as a float.
        log_price = math.log(total/4)-math.log(log_N)-log_N
        prices.append(dict(logOrder=log_N, log10RelativeSupplyPrice=log_price/math.log(10),
                           leadingFormula="joinedOwnerCost / (4*(N+2)*log(N+1))",
                           idealAsymptoticPriceOnly=True,
                           supplyScaleAndDisjointCoverStillRequired=True))
    print(json.dumps(dict(diagnosticOnly=True,
                         ownershipRows=ownership_rows(),
                         exactSquarefreeCountSymmetry=exact_symmetry(),
                         ownerAllCountCost=owner, boundaryAllCountCost=boundary,
                         joinedOwnerCost=total,
                         dominantBudgetIndex=max_order,
                         budgetWeightThrough39=math.fsum(contributions[:40])/all_count_mass,
                         cutoffCountCeilingUsed=False,
                         relativeSupplyPrices=prices,
                         sourceScaleDecayClaimed=False,
                         wholeFloorCertified=False,
                         effectiveStartingOrderCertified=False), indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Optional quantitative regression of squarefree period symmetry.

This evaluates comparison constants, not the retained carrier. Complete
period geometry is still required. No starting order, literal clipped
period bound, whole floor, or deficit percentage is certified.
"""

from fractions import Fraction
from itertools import combinations
import json
import math


def constant_logs(k):
    def capacity(parity):
        return max((math.comb(k-2, j) for j in range(k-1)
                    if j % 2 == parity), default=0)

    def moment(exponent):
        return 6*math.log(4)/(-math.expm1(-exponent*math.log(2)))

    response = 2*(1+capacity(0)+capacity(1))
    terms = [math.log((200000+1200*(k+1))*response)
             + k*math.log(moment(1/k)),
             math.log(400)+k*math.log(2)+k*math.log(2*moment(1/(2*k)))]
    peak = max(terms)
    old = peak+math.log(sum(math.exp(t-peak) for t in terms))
    new = old-math.lgamma(k+1)
    upper = math.log(2000000)+k*math.log(2048)
    assert new <= upper
    return dict(cofactorCount=k, oldLogPopulationCost=old,
                symmetricLogPopulationCost=new,
                exactSavingDenominator=math.factorial(k),
                relativeLogSaving=-math.lgamma(k+1),
                uniformUpperLogCost=upper,
                wholeCarrierMassEvaluated=False)


def finite_symmetry():
    primes = (2, 3, 5, 7, 11, 13, 17)
    weights = tuple(Fraction(1, p) for p in primes)
    rows = []
    for k in range(1, len(primes)+1):
        mass = sum((math.prod(choice) for choice in combinations(weights, k)),
                   start=Fraction(0))
        ordered_cover = sum(weights)**k
        distinct_ordered = math.factorial(k)*mass
        assert distinct_ordered <= ordered_cover
        rows.append(dict(k=k, squarefreeReciprocalMass=str(mass),
                         distinctOrderedMass=str(distinct_ordered),
                         fullTupleUpperMass=str(ordered_cover),
                         exactRationalInequality=True))
    return rows


def growing_band():
    rows = []
    for digits in (6, 20, 50, 100, 500, 1000):
        order = 10**digits
        # 4096 = 2^12, so this is the exact Nat.log, not a floating log.
        base_log = ((order+1).bit_length()-1)//12
        ceiling = base_log//4
        assert 4096**(4*ceiling) <= order+1
        rows.append(dict(order=f"10^{digits}",
                         cofactorCountCeiling=ceiling,
                         logRelativeRadialUpperCost=math.log(2000000)
                         - math.log(order+1)/4,
                         effectiveStartCertified=False))
    return rows


if __name__ == '__main__':
    print(json.dumps(dict(diagnosticOnly=True,
                         exactFiniteSymmetry=finite_symmetry(),
                         comparisonConstants=[constant_logs(k)
                                              for k in (2, 6, 7, 10, 20, 54, 100)],
                         growingBand=growing_band(),
                         noPrimeDensityOrZeroHypothesis=True,
                         noPhysicalMaskCompletion=True,
                         clippedPeriodsAndOwnerHolesPaid=False,
                         sourceScaleDecayClaimed=False,
                         wholeFloorCertified=False), indent=2))

#!/usr/bin/env python3
"""Optional regression of the proved whole polynomial-owner payment.

The original dyadic labels, masks and factorial incidence regression are
retained. The rational geometric bound is EVENTUAL: these finite samples do
not certify its starting order, a population mass, or the whole signed floor.
This script is outside ordinary builds and CI.
"""

import argparse
import itertools
import json
import math

from sympy import nextprime, primerange

from probe_riesz_canonical_joint import core_mask
from probe_riesz_hinge_allocation import original_label
from probe_riesz_lower_radial import make_prime, parameters


def finite_euler_regression():
    primes = list(primerange(2, 44))
    atom_sum = math.fsum(
        2**len(subset) * math.exp(-(63/64)*math.log(math.prod(subset)))
        for count in range(len(primes)+1)
        for subset in itertools.combinations(primes, count)
    )
    product = math.prod(1+2*p**(-(63/64)) for p in primes)
    assert math.isclose(atom_sum, product, rel_tol=1e-12)
    # The Rankin mass here is finite and directly computed. The Lean proof
    # bounds it by the convergent full mass; that constant is not evaluated.
    order = 32
    actual_mass = math.fsum(p**(-(63/64)) for p in primes)
    comparison_mass = math.fsum(p**(-(129/128)) for p in primes)
    rankin_bound = (order+1)**(3/4)*comparison_mass
    assert actual_mass <= rankin_bound
    return dict(primeUniverse=primes, completeSquarefreeSubsetMass=atom_sum,
                finiteEulerProduct=product, finiteRankinMass=actual_mass,
                finiteComparisonMass=comparison_mass,
                finiteRankinUpper=rankin_bound,
                completeCountSumRetained=True)


def original_sample(j, height):
    ceiling = 2**(j+3)
    order = 8*(j+4)*ceiling
    pars = parameters(order)
    count, frozen = (15, 12) if j == 1 else (28, 21)
    start = make_prime(pars['length']/(frozen-5/3))
    primes = [start]
    while len(primes) < count:
        primes.append(int(nextprime(primes[-1])))
    label = math.prod(primes)
    owner = primes[-1]
    assert core_mask(order, label, dict.fromkeys(primes, 1), pars, ceiling) == 'core'
    assert 1.97*order < math.log(label) <= 2.03*order
    threshold = (order+1)**32
    inside = owner <= threshold
    assert inside
    previous = original_label(j, height)
    return dict(N=order, count=count, countCeiling=ceiling,
                originalCoreMask='core', originalLargestPrime=owner,
                polynomialOwnerThreshold=threshold,
                exactIntegerOwnerComparison=inside,
                ownerLogPerN=math.log(owner)/order,
                polynomialThresholdLogPerN=math.log(threshold)/order,
                lengthLowerPrecondition=pars['length'] >= 11*order/8,
                previousMaskAndBothHingeRegression=previous,
                noZeroHypothesisUsed=True, sampleUnderflowIsNotEvidence=True)


def rates():
    rate = (10001/20000)*(64/33)*math.exp(1/256)
    assert 0 < rate < 39/40
    return dict(rate=rate, provedRationalGeometricUpper=39/40,
                geometricLogRate=math.log(rate),
                sourceGrowthLogRate=math.log(2*(10001/20000)),
                sublinearEulerExponentPower=3/4,
                comparisonMassExponent=129/128,
                finiteBoundPrefactor=(203/50)*(10001/20000),
                eventualUpperLogs=[dict(N=n, logEventualUpper=n*math.log(39/40))
                                  for n in (640, 1536, 4096, 8192)],
                eventualStartEvaluated=False,
                fullComparisonMassEvaluated=False,
                finiteOrdersAreNotCertifiedByEventualRate=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dyadic-index', type=int, choices=(1, 2), default=2)
    parser.add_argument('--height', type=float, default=54.)
    args = parser.parse_args()
    print(json.dumps(dict(diagnosticOnly=True, rates=rates(),
                         finiteEuler=finite_euler_regression(),
                         originalLabel=original_sample(args.dyadic_index, args.height),
                         allOriginalMasksAndPhasesRetained=True,
                         remainingLargeOwnerRowsBounded=False,
                         wholeFloorCertified=False), indent=2))


if __name__ == '__main__':
    main()

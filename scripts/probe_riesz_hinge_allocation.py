#!/usr/bin/env python3
"""Optional diagnostic of the proved whole-hinge owner-allocation payment.

Use log-domain arithmetic, the literal unpaid orders, and the existing actual
dyadic/core close-owner regression. The fixed global majorant mass is NOT
evaluated here. Error rates per unit of that mass are not floor certificates.
This script is not imported by ordinary builds or CI.
"""

import argparse
import json
import math

from sympy import isprime, nextprime

from probe_riesz_canonical_joint import core_mask
from probe_riesz_hinge_pair import close_owner_label
from probe_riesz_lower_radial import make_prime, parameters


def log_allocation(n, orders, share):
    """The complete original selected binomial sum, without subtracting from 1."""
    logs = [math.lgamma(n+2)-math.lgamma(k+1)-math.lgamma(n+2-k)+
            k*math.log(share)+(n+1-k)*math.log1p(-share) for k in orders]
    if not logs:
        return None
    peak = max(logs)
    return peak+math.log(math.fsum(math.exp(value-peak) for value in logs))


def rate_regression():
    rate = .503*(2048/1023)*math.exp(-1/8)
    assert 0 < rate < .9
    tests = []
    for n in (32, 128, 640, 1536):
        pars = parameters(n)
        observed = log_allocation(n, pars['orders'], 5/6)
        assert observed is None or observed <= -n/8+1e-10
        tests.append(dict(N=n, originalUnpaidOrderCount=len(pars['orders']),
                          smallestAllowedCofactorShare=5/6,
                          logOriginalAllocation=observed,
                          provedLogAllocationUpper=-n/8))
    costs = [dict(N=n, logSourceCostPerFixedMajorantMass=math.log(503/500)+n*math.log(rate),
                  logRationalUpperPerFixedMajorantMass=math.log(503/500)+n*math.log(.9))
             for n in (640, 1536, 4096, 8192)]
    return dict(rate=rate, provedRationalRateUpper=.9,
                originalOrderTests=tests, sourceErrorRates=costs,
                fixedMajorantMassEvaluated=False,
                effectiveFloorStartingOrderCertified=False)


def original_label(j, height):
    ceiling = 2**(j+3)
    n = 8*(j+4)*ceiling
    pars = parameters(n)
    count, frozen_count = (15, 12) if j == 1 else (28, 21)
    target = pars['length']/(frozen_count-5/3)
    primes = [make_prime(target)]
    while len(primes) < count:
        primes.append(int(nextprime(primes[-1])))
    assert all(isprime(p) for p in primes) and len(set(primes)) == count
    p = primes[-1]
    b = math.prod(primes[:frozen_count])
    e = math.prod(primes[frozen_count:-1])
    label = p*b*e
    assert core_mask(n, label, dict.fromkeys(primes, 1), pars, ceiling) == 'core'
    total, owner = math.log(label), math.log(p)
    assert 1.97*n < total <= 2.03*n
    assert pars['length'] < math.log(b)
    assert 2*owner+math.log(b) <= 2.03*n
    assert owner <= total/6
    fraction = log_allocation(n, pars['orders'], 1-owner/total)
    assert fraction is None or fraction <= -n/8+1e-9
    # The independent regression retains both original hinges and phase.
    physical = close_owner_label(j, height)
    assert abs(physical['totalLogPerN']-total/n) < 1e-12
    assert physical['bothOriginalOwnerGapsFail']
    return dict(N=n, count=count, countCeiling=ceiling, originalCoreMask='core',
                totalLogPerN=total/n, ownerLogPerN=owner/n,
                originalOwnerShare=owner/total, originalCofactorShare=1-owner/total,
                lengthPerN=pars['length']/n,
                lengthLowerPrecondition=pars['length'] >= 11*n/8,
                genuineFailedGapHinge=True, originalPrimesAllSixthBounded=True,
                logOriginalOwnerAllocation=fraction,
                provedLogAllocationUpper=-n/8,
                pointwiseAllocationEstimateApplies=True,
                maskPreservingPhysicalRegression=physical,
                sourcePopulationMassCertified=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dyadic-index', type=int, choices=(1, 2), default=2)
    parser.add_argument('--height', type=float, default=54.)
    args = parser.parse_args()
    print(json.dumps(dict(diagnosticOnly=True, actualDyadicSchedule=True,
                         rates=rate_regression(),
                         originalLabel=original_label(args.dyadic_index, args.height),
                         hypothesisOfZetaZeroUsed=False,
                         unallocatedSignedMainBounded=False, wholeFloorCertified=False), indent=2))


if __name__ == '__main__':
    main()

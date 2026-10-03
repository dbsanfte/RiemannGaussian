#!/usr/bin/env python3
"""Optional diagnostic for the independent cubic canonical-crossing payment.

The prime labels, original masks, factorial orders and common complex phase
remain literal. The probe is not a population estimate or a finite starting
order certificate. The eventual decay is proved in Lean. This script is
manual and is not part of ordinary builds or CI.
"""

import argparse
from fractions import Fraction
import json
import math

import mpmath as mp
from sympy import isprime, nextprime, primerange

from probe_riesz_canonical_joint import allocation, core_mask
from probe_riesz_lower_radial import parameters


def prime_at_log(logarithm):
    # Preserve the large integer without overflowing a binary64 exponential.
    with mp.workdps(80):
        return int(nextprime(int(mp.exp(mp.mpf(logarithm)))))


def literal_row(j, height, frozen_count):
    ceiling = 2**(j+3)
    n = 8*(j+4)*ceiling
    pars = parameters(n)
    r = int(nextprime(n*n+1))
    q = int(nextprime(r))
    assert n*n < r < q <= n**3
    assert frozen_count in (3, 5)
    p = prime_at_log((1 if frozen_count == 3 else .7)*n)
    target = (3899/2000+1/504000)*n
    residual = target-math.log(p)-math.log(r*q)
    if frozen_count == 3:
        middle = [prime_at_log(residual)]
    else:
        b1 = prime_at_log(residual/3-.1)
        b2 = prime_at_log(residual/3-.05)
        middle = [b1, b2, prime_at_log(residual-math.log(b1)-math.log(b2))]
    b = r*q*math.prod(middle)
    e = prime_at_log(2*n-math.log(p*b))
    primes = [r, q, *middle, e, p]
    count = frozen_count+2
    assert len(set(primes)) == count and all(isprime(t) for t in primes)
    assert q < min(*middle, e) and max(primes) == p
    label = p*b*e
    outer, total = math.log(p*b), math.log(label)
    assert core_mask(n, label, dict.fromkeys(primes, 1), pars, ceiling) == 'core'
    assert 3899*n/2000 < outer <= (39/20-1/2016)*n
    assert outer+math.log(p) > 203*n/100 and math.log(p) < 243*n/200
    assert 1.97*n < total <= 2.03*n
    cut = outer-3899*n/2000
    signs = {1: 1, r: -1, q: -1, r*q: 1}
    retained = [d for d in signs if math.log(d) < cut]
    assert retained == [1]
    hinge = lambda d: max(math.log(p*(b//d))-pars['length'], 0)-max(
        math.log(b//d)-pars['length'], 0)
    joined = math.fsum(-signs[d]*hinge(d) for d in retained)
    assert joined < 0
    multiplier = math.fsum(signs[d]*hinge(d) for d in retained)/hinge(1)
    assert multiplier == 1
    unassigned = 1-allocation(n, pars['orders'], 1-math.log(p)/total)
    log_amplitude = ((n+1)*math.log(10001/20000)-1.5*total+
                     (n+1)*math.log(total)-math.lgamma(n+1)-math.log(pars['length']))
    phase = [math.cos(height*total), -math.sin(height*total)]
    native_ceiling = ceiling//864+1
    return dict(N=n, dyadicIndex=j, originalCount=count, originalCountCeiling=ceiling,
                originalCoreMask='core', canonicalPair=[r, q],
                quadraticSelector=False, cubicSelector=True,
                canonicalRoughness=True, wholeWindowOwnerGap=True,
                originalUnsignedGap=True, totalLogPerN=total/n,
                exactOriginalFactorization=[str(t) for t in primes],
                physicalLength=pars['length'],
                eventualLengthPreconditionHolds=pars['length'] >= 11*n/8,
                retainedDivisors=retained, joinedCoefficient=joined,
                exactRowMultiplier=multiplier, originalOwnerAllocation=1-unassigned,
                originalPhase=phase, sourceScaledLogAmplitude=log_amplitude,
                sourceScaledLogNorm=log_amplitude+math.log(abs(joined)*unassigned),
                nativeCountCeiling=native_ceiling,
                nativeCountCropAdmitsLabel=count < native_ceiling,
                labelObservationIsNotPopulationMass=True)


def prefix_regression():
    rows = []
    for cutoff in (100, 1000, 10000):
        primes = list(primerange(2, cutoff+1))
        log_cost = math.fsum(math.log1p(p**(-23/32)+p**(-46/32)) for p in primes)
        log_bound = (64/9)*cutoff**(9/32)
        assert log_cost <= log_bound
        rows.append(dict(cutoff=cutoff, exactFinitePrimeCount=len(primes),
                         weightedProductLog=log_cost, provedLogEnvelope=log_bound))
    return rows


def rate_audit():
    # Exact rational inequality used in the Lean source-rate comparison.
    gap = Fraction(9, 64512)-Fraction(203, 6553600)-Fraction(1, 10000)
    assert gap > Fraction(1, 125000)
    # This is only a diagnostic of the sufficient sublinear-cost absorption.
    # It does not certify the full eventual packet's finite starting index.
    log10_absorption = (32/5)*math.log10((64/9)*250000)
    return dict(sieveExponent='23/32', secondPrimeThreshold='N^3',
                prefixLogEnvelope='(64/9)*N^(27/32)',
                sourceLogRateUpper='-1/125000',
                retainedLogRateUpper='-1/250000',
                exactRationalLinearGap=str(gap),
                sufficientScalarAbsorptionOrderLog10=log10_absorption,
                fullPacketStartingOrderCertified=False,
                finiteSourceBudget=[dict(N=n, logRateBeforePolynomialConstants=
                    -n/125000+(64/9)*n**(27/32)) for n in (640, 1536, 4096, 8192)])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dyadic-index', nargs='+', type=int, default=[1, 2])
    parser.add_argument('--height', type=float, default=54)
    args = parser.parse_args()
    print(json.dumps(dict(diagnosticOnly=True, rate=rate_audit(),
                         finitePrimePrefix=prefix_regression(),
                         literalRows=[literal_row(j, args.height, count)
                                      for j in args.dyadic_index for count in (3, 5)],
                         zetaZeroHypothesisUsed=False, populationMassCertified=False,
                         wholeFloorCertified=False), indent=2))


if __name__ == '__main__':
    main()

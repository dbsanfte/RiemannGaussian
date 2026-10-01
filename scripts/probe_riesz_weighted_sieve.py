#!/usr/bin/env python3
"""Optional diagnostic for the weighted canonical-pair cutoff payment.

Retain the actual prime intersection factors rather than replacing each
by three. Genuine original-label examples exercise pairs beyond sqrt(N)
while keeping the literal phase, allocation, core and roughness predicates.
Floating tests certify neither the cofinal starting order nor a whole floor.
This probe is deliberately outside ordinary builds and CI.
"""

import argparse
import cmath
import json
import math

from sympy import isprime, nextprime, primerange

from probe_riesz_canonical_joint import allocation, core_mask
from probe_riesz_lower_radial import parameters


def prime_at_log(x):
    return int(nextprime(math.floor(math.exp(x))))


def literal_row(n, pair, height):
    r, s = pair
    assert isprime(r) and isprime(s) and r < s <= n*n
    pars = parameters(n)
    p = prime_at_log(.7*n)
    # Strictly inside the ORIGINAL row's unsigned comparison gap.
    target = (3899/2000+1/504000)*n
    residual = target-math.log(p)-math.log(r*s)
    q1 = prime_at_log(residual/3-.1)
    q2 = prime_at_log(residual/3-.05)
    q3 = prime_at_log(residual-math.log(q1)-math.log(q2))
    b = r*s*q1*q2*q3
    e = prime_at_log(2*n-math.log(p*b))
    primes = [r, s, q1, q2, q3, e, p]
    assert len(set(primes)) == len(primes) and all(isprime(q) for q in primes)
    assert s < min(q1, q2, q3, e) and max(primes) == p
    label = p*b*e
    total, outer = math.log(label), math.log(p*b)
    assert core_mask(n, label, dict.fromkeys(primes, 1), pars, 128) == 'core'
    assert 3899*n/2000 < outer <= (39/20-1/2016)*n
    assert outer+math.log(p) > 203*n/100
    assert math.log(p) < 243*n/200
    cut = outer-3899*n/2000
    signs = {1: 1, r: -1, s: -1, r*s: 1}
    retained = [d for d in signs if math.log(d) < cut]
    assert retained == [1]
    hinge = lambda d: max(math.log(p*(b//d))-pars['length'], 0)-max(
        math.log(b//d)-pars['length'], 0)
    mu_b = -1  # Five distinct frozen cofactor primes.
    joined = math.fsum(mu_b*signs[d]*hinge(d) for d in retained)
    multiplier = math.fsum(signs[d]*hinge(d) for d in retained)/hinge(1)
    assert abs(multiplier) <= 4
    unassigned = 1-allocation(n, pars['orders'], 1-math.log(p)/total)
    log_amplitude = ((n+1)*math.log(10001/20000)-1.5*total+
                     (n+1)*math.log(total)-math.lgamma(n+1)-math.log(pars['length']))
    observation = joined*unassigned*math.exp(log_amplitude)*cmath.exp(-1j*height*total)
    return dict(N=n, pair=list(pair), originalCount=len(primes),
                originalCoreMask='core', oldSqrtCapSelected=s <= math.isqrt(n),
                newPolynomialCapSelected=s <= n*n, canonicalRoughMask=True,
                wholeWindowOwnerGap=True, originalUnsignedGap=True,
                retainedDivisors=retained, joinedCoefficient=joined,
                exactRowMultiplier=multiplier, originalOwnerAllocation=1-unassigned,
                sourceScaledLiteralReal=observation.real,
                sourceScaledLogAmplitude=log_amplitude,
                floatingUnderflow=log_amplitude < -745,
                originalPhaseRetained=True, populationBoundCertified=False)


def prefix_cost(n):
    primes = list(primerange(2, n*n+1))
    weights = [p**(-17/32) for p in primes]
    cost = math.fsum(math.log1p(w+w*w) for w in weights)
    return dict(N=n, forbiddenPrimeCount=len(primes),
                weightedProductLogCost=cost,
                oldThreePerPrimeLogCost=len(primes)*math.log(3),
                weightedPrefixLogCostPerN=cost/n,
                comparisonLogEnvelopeBeforeOuterFactors=cost-n/10000,
                finiteStartingOrderCertified=False)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--orders', type=int, nargs='+', default=[256, 640, 1536])
    ap.add_argument('--height', type=float, default=54)
    args = ap.parse_args()
    rows = [literal_row(n, pair, args.height) for n in args.orders if n <= 640
            for pair in [(17, 19), (257, 263), (65519, 65521)]]
    print(json.dumps(dict(diagnosticOnly=True, literalRows=rows,
                         prefixCosts=[prefix_cost(n) for n in args.orders],
                         cofinalScheduleTested=False, floorCertified=False,
                         geometricDecayProof='Lean eventual comparison, not these samples'),
                     indent=2))


if __name__ == '__main__':
    main()

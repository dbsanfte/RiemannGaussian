#!/usr/bin/env python3
"""Optional literal-label regression for the lower radial payment.

Genuine primes and the existing original masks are retained. The rate
certificate is rational, while the label observations are floating
diagnostics. Neither is a finite starting-order or whole-floor certificate.
This probe is not part of the ordinary build or CI.
"""

import argparse
import cmath
from fractions import Fraction
from itertools import combinations
import json
import math

from sympy import isprime, nextprime

from probe_riesz_canonical_joint import allocation, core_mask
from probe_riesz_fixed_count_period import unpaid_orders


def parameters(n):
    # The same original parameters, without materializing unused exp(2.03N)
    # integer-cell edges through a floating exponential.
    cutoff = 20000**n // (10001**n*(n+1))
    physical = (cutoff+2)**2
    u = 10001/20000
    tilt = 1/(-2*math.log(u))
    log_rate = (2-2*tilt)*math.log(u)-math.log(tilt)
    trial = min(math.floor(math.exp(-n*log_rate/(2*(tilt+2.5)))), cutoff+1)
    return dict(physical=physical, length=math.log(physical), trial=trial,
                orders=unpaid_orders(n).tolist())


def make_prime(logarithm):
    return int(nextprime(math.floor(math.exp(logarithm))))


def radial_label(n, slopes, height):
    primes = [make_prime(n*s) for s in slopes]
    assert len(set(primes)) == len(primes) and all(isprime(p) for p in primes)
    label = math.prod(primes)
    p = max(primes)
    cofactor = sorted(q for q in primes if q != p)
    pars = parameters(n)
    mask = core_mask(n, label, {q: 1 for q in primes}, pars, 128)
    assert mask == 'core', mask
    total = math.log(label)
    response = []
    for k in range(len(cofactor)+1):
        for subset in combinations(cofactor, k):
            b = math.prod(subset)
            hinge = max(0, math.log(p*b)-pars['length'])-max(0, math.log(b)-pars['length'])
            response.append((-1)**k*hinge)
    signed_hinge = math.fsum(response)
    unallocated = 1-allocation(n, pars['orders'], 1-math.log(p)/total)
    coefficient = unallocated*total/pars['length']*signed_hinge
    kernel_log_norm = -1.5*total+n*math.log(total)-math.lgamma(n+1)
    source_kernel_log_norm = (n+1)*math.log(10001/20000)+kernel_log_norm
    normalized = coefficient*math.exp(source_kernel_log_norm)*cmath.exp(-1j*height*total)
    reference = 1+1/1048576
    endpoint = 197/100
    log_kernel_tilt_ratio = (n+1)*math.log(10001/20000)+kernel_log_norm+reference*total
    certified_kernel_log_budget = math.log(10001/20000)-n/100000
    in_strip = total <= endpoint*n
    if in_strip:
        assert log_kernel_tilt_ratio <= certified_kernel_log_budget+1e-9
    return dict(N=n, count=len(primes), originalMask=mask,
                totalLogPerN=total/n, lowerStrip=in_strip,
                signedCofactorHinge=signed_hinge,
                originalOwnerAllocation=1-unallocated,
                sourceScaledLiteralReal=normalized.real,
                sourceScaledKernelLogNorm=source_kernel_log_norm,
                floatingKernelUnderflow=source_kernel_log_norm < -745,
                logKernelToEulerWeight=log_kernel_tilt_ratio,
                certifiedLowerStripLogBudget=certified_kernel_log_budget,
                originalPhaseRetained=True, populationMassCertified=False)


def reinforcing_edges(n, height):
    pars = parameters(n)
    p = make_prime(.065*n)
    v = (math.log(5)+math.log(6))/2
    target_c = 3899*n/2000+v
    count = 31
    other_log = (target_c-math.log(p)-math.log(30))/count
    q = make_prime(other_log)
    other = []
    for _ in range(count):
        assert 5 < q < p
        other.append(q)
        q = int(nextprime(q))
    b = 30*math.prod(other)
    e = make_prime(1.99*n-math.log(p*b))
    assert 5 < e < p and e not in other
    primes = [p, 2, 3, 5, *other, e]
    label = math.prod(primes)
    assert len(set(primes)) == len(primes) and all(isprime(q) for q in primes)
    assert core_mask(n, label, {q: 1 for q in primes}, pars, 128) == 'core'
    delta_signs = {1: 1, 2: -1, 3: -1, 6: 1}
    observations = []
    original_divisors = []
    for frozen, unsigned in ((b, e), (b//5, e*5)):
        cutoff = math.log(p*frozen)-3899*n/2000
        deltas = [d for d in delta_signs if math.log(d) < cutoff]
        mu_frozen = (-1)**(count+(3 if frozen == b else 2))
        terms = []
        for d in deltas:
            hinge = max(0, math.log(p*(frozen//d))-pars['length'])-max(0, math.log(frozen//d)-pars['length'])
            assert abs(hinge-math.log(p)) < 1e-10
            terms.append(mu_frozen*delta_signs[d]*hinge)
            original_divisors.append(unsigned*d)
        observations.append(dict(cutoff=cutoff, selectedDivisors=deltas,
                                 frozenMobius=mu_frozen, joinedCoefficient=math.fsum(terms)))
    assert observations[0]['selectedDivisors'] == [1, 2, 3]
    assert observations[1]['selectedDivisors'] == [1]
    assert len(set(original_divisors)) == len(original_divisors)
    joined = math.fsum(z['joinedCoefficient'] for z in observations)
    assert abs(joined+2*math.log(p)) < 1e-10
    total = math.log(label)
    unallocated = 1-allocation(n, pars['orders'], 1-math.log(p)/total)
    log_amplitude = (n+1)*math.log(10001/20000)-1.5*total+(n+1)*math.log(total)-math.lgamma(n+1)-math.log(pars['length'])
    common_weight = unallocated*math.exp(log_amplitude)*cmath.exp(-1j*height*total)
    return dict(N=n, count=len(primes), originalMask='core',
                commonOriginalLabel=True, distinctOriginalDivisorIncidences=True,
                blocks=observations, joinedCoefficient=joined,
                predictedJoinedCoefficient=-2*math.log(p),
                sourceScaledReal=(common_weight*joined).real,
                edgesReinforce=True, allPossiblePairingsRuledOut=False)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--orders', nargs='+', type=int, default=[256, 640])
    ap.add_argument('--height', type=float, default=54)
    args = ap.parse_args()
    q = Fraction(99984988, 100000000)
    u = Fraction(10001, 20000)
    endpoint = Fraction(197, 100)
    exponent_bound = 100*(q-1)+1-(Fraction(3, 2)-1-Fraction(1, 1048576))*endpoint
    assert q**100 > u*endpoint and exponent_bound < -Fraction(1, 100000)
    rows = [radial_label(n, slopes, args.height) for n in args.orders
            for slopes in ((.2, .3, .41, .52, .53), (.2, .3, .43, .51, .56))]
    print(json.dumps(dict(diagnosticOnly=True, exactRationalRateCertificate=True,
                         logRateUpperBound=float(exponent_bound),
                         targetLogRate=-1/100000, radialRows=rows,
                         edgeRegression=reinforcing_edges(args.orders[0], args.height),
                         wholeFloorCertified=False, cofinalPopulationMassCertified=False), indent=2))


if __name__ == '__main__':
    main()

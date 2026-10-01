#!/usr/bin/env python3
"""Optional original-label diagnostic for canonical-pair cutoff payments.

Build squarefree labels from genuine primes, retain the moving length,
original core/count/physical masks, owner allocation and complex phase,
and join the clipped canonical divisor block before observing its sign.
This is a floating transcription regression, never a cofinal or floor
certificate. It is intentionally outside the ordinary build and CI.
"""

import argparse
import cmath
import json
import math

from sympy import isprime, nextprime

from probe_riesz_canonical_joint import allocation, core_mask, parameters


def witness(n, pair, owner_slope, other_count, height):
    r, s = pair
    assert isprime(r) and isprime(s) and r < s
    pars = parameters(n, 8)
    p = int(nextprime(math.floor(math.exp(owner_slope*n))))
    v = (math.log(r)+math.log(s))/2
    target_c = 3899*n/2000+v
    other_log = (target_c-math.log(p)-math.log(r*s))/other_count
    q = int(nextprime(math.floor(math.exp(other_log))))
    other = []
    for _ in range(other_count):
        assert s < q < p
        other.append(q)
        q = int(nextprime(q))
    b = r*s*math.prod(other)
    e = int(nextprime(math.floor(math.exp(1.99*n-math.log(p*b)))))
    primes = [r, s, *other, e, p]
    assert len(set(primes)) == len(primes)
    assert all(isprime(q) for q in primes)
    assert s < e < p
    label = p*b*e
    factors = {q: 1 for q in primes}
    mask = core_mask(n, label, factors, pars, 128)
    assert mask == 'core', mask
    assert sorted(primes[:-1])[:2] == [r, s]
    total = math.log(label)
    c = math.log(p*b)
    actual_v = c-3899*n/2000
    assert math.log(r) < actual_v <= math.log(s)
    deltas = [d for d in (1, r, s, r*s) if math.log(d) < actual_v]
    assert deltas == [1, r]
    assert c <= 3899*n/2000+math.log(r*s)
    assert math.log(e)+math.log(r*s) >= total-3899*n/2000
    signs = {1: 1, r: -1, s: -1, r*s: 1}
    mu_b = (-1)**(other_count+2)
    hinge = lambda z: max(math.log(p*z)-pars['length'], 0)-max(math.log(z)-pars['length'], 0)
    terms = [mu_b*signs[d]*hinge(b//d) for d in deltas]
    joined = math.fsum(terms)
    h_b = hinge(b)
    multiplier = math.fsum(signs[d]*hinge(b//d) for d in deltas)/h_b
    assert abs(multiplier) <= 4+1e-10
    assert all(math.log(p*(b//d)) > 3899*n/2000 for d in deltas)
    unallocated = 1-allocation(n, pars['orders'], 1-math.log(p)/total)
    source_amplitude = math.exp((n+1)*math.log(10001/20000)-1.5*total+
                                (n+1)*math.log(total)-math.lgamma(n+1))/pars['length']
    common_weight = unallocated*source_amplitude*cmath.exp(-1j*height*total)
    is_tiny = math.log(p) <= 161*n/2000
    if is_tiny:
        assert abs(joined) <= 1e-11*max(1, sum(map(abs, terms)))
        assert abs(common_weight*joined) <= 1e-11*max(1, abs(common_weight))
    return {
        'N': n, 'canonicalPair': [r, s], 'coreCount': len(primes),
        'coreMask': mask, 'secondPrimeAtMostSqrtN': s <= math.isqrt(n),
        'wholeWindowOwnerGap': c+math.log(p) > 2.03*n,
        'tinyOwner': is_tiny, 'deltaSelection': deltas,
        'divisorCoefficients': terms, 'joinedCoefficient': joined,
        'cutoffMultiplier': multiplier,
        'sourceScaledRealObservation': (common_weight*joined).real,
        'originalPhaseAndAllocationRetained': True,
        'oldOwnerGapCreditOverlap': 0, 'oldAffineOrbitOverlap': 0,
        'cofinalScheduleTested': False, 'populationMassCertified': False,
        'floorCertified': False,
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--N', type=int, default=256)
    ap.add_argument('--height', type=float, default=54)
    args = ap.parse_args()
    rows = [witness(args.N, pair, .7, 3, args.height)
            for pair in ((2, 5), (3, 7), (5, 11), (7, 13))]
    rows += [witness(args.N, pair, .065, 32, args.height)
             for pair in ((2, 5), (43, 47))]
    print(json.dumps({'diagnosticOnly': True, 'rows': rows}, indent=2))


if __name__ == '__main__':
    main()

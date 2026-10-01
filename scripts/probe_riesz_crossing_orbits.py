#!/usr/bin/env python3
"""Optional original-label regression for complete crossing-orbit cancellation.

The old reinforcing clipped edges are retained as a negative regression.
Restoring their full canonical blocks, on the same physical label, gives
zero. A fully rough example also lies beyond the polynomial sieve cap.
Floating regression is not the Lean population proof or a whole-floor
certificate. This script is outside ordinary builds and CI.
"""

import argparse
import cmath
import json
import math

from sympy import isprime, nextprime

from probe_riesz_canonical_joint import allocation, core_mask
from probe_riesz_lower_radial import parameters, make_prime


def original_example(n, height, rough=False):
    pars = parameters(n)
    p = make_prime(.065*n)
    if rough:
        r = int(nextprime(n*n))
        s = int(nextprime(r))
        total_target = 2.02*n
        outer_target = (2.02-.056)*n
    else:
        r, s = 2, 3
        total_target = 1.99*n
        outer_target = 3899*n/2000+(math.log(5)+math.log(6))/2
    third = int(nextprime(s))
    q = make_prime((outer_target-math.log(p)-math.log(r*s*third))/31)
    other = []
    for _ in range(31):
        assert third < q < p
        other.append(q)
        q = int(nextprime(q))
    b = r*s*third*math.prod(other)
    e = make_prime(total_target-math.log(p*b))
    primes = [p, r, s, third, *other, e]
    assert s < e < p and e not in other
    assert len(set(primes)) == len(primes) and all(isprime(q) for q in primes)
    label = p*b*e
    assert core_mask(n, label, dict.fromkeys(primes, 1), pars, 128) == 'core'
    total = math.log(label)
    unassigned = 1-allocation(n, pars['orders'], 1-math.log(p)/total)
    log_amplitude = ((n+1)*math.log(10001/20000)-1.5*total+
                     (n+1)*math.log(total)-math.lgamma(n+1)-math.log(pars['length']))
    common = unassigned*math.exp(log_amplitude)*cmath.exp(-1j*height*total)
    blocks = []
    bases = [(b, e, 34)] if rough else [(b, e, 34), (b//third, e*third, 33)]
    for frozen, base, count in bases:
        outer = math.log(p*frozen)
        gap = outer+math.log(p)
        cut = outer-3899*n/2000
        assert 0 < cut <= math.log(r*s)
        assert gap <= 2.03*n
        values = []
        clipped = []
        original = []
        for d, sign in [(1, 1), (r, -1), (s, -1), (r*s, 1)]:
            signed = frozen//d
            assert base*d*signed == label//p
            hinge = max(0, math.log(p*signed)-pars['length'])-max(
                0, math.log(signed)-pars['length'])
            assert abs(hinge-math.log(p)) < 1e-9
            assert math.log(p*signed)+math.log(p) <= 2.03*n
            value = (-1)**count*sign*hinge
            values.append(value)
            if math.log(d) < cut:
                clipped.append(value)
            original.append([base*d, signed])
        full = math.fsum(values)
        old = math.fsum(clipped)
        restored = full-old
        assert abs(full) < 1e-9
        blocks.append(dict(originalIncidences=original, clippedValue=old,
                           restoredComplement=restored, fullValue=full,
                           wholeRowOwnerGapFailsForAllMembers=True,
                           allHingesSaturated=True,
                           sourceScaledFullReal=(common*full).real))
    original_divisors = [row[0] for b in blocks for row in b['originalIncidences']]
    assert len(set(original_divisors)) == len(original_divisors)
    # A new block wholly beyond the artificial cutoff, on the SAME label.
    # This tests the larger affine population, rather than only restoring
    # the previously clipped crossing blocks.
    long_base = other[0]*other[1]
    long_frozen = (label//p)//long_base
    pair_log = math.log(r*s)
    short_end = total-3899*n/2000
    assert math.log(long_base) >= short_end
    assert math.log(long_base)+pair_log >= short_end
    assert total-math.log(long_base)+math.log(p) <= 2.03*n
    assert math.log(p)+math.log(long_base)+pair_log <= total-pars['length']
    long_values = []
    for d, sign in [(1, 1), (r, -1), (s, -1), (r*s, 1)]:
        signed = long_frozen//d
        assert long_base*d*signed == label//p
        hinge = max(0, math.log(p*signed)-pars['length'])-max(
            0, math.log(signed)-pars['length'])
        long_values.append((-1)**(len(primes)-3)*sign*hinge)
    long_full = math.fsum(long_values)
    assert abs(long_full) < 1e-9
    long_orbit = dict(base=long_base, baseLog=math.log(long_base),
                      artificialShortEnd=short_end, outsideOldInterior=True,
                      outsideCutoffCrossing=True, failedWholeRowOwnerGap=True,
                      individualSignedValues=long_values, fullValue=long_full,
                      sourceScaledFullReal=(common*long_full).real)
    return dict(N=n, count=len(primes), pair=[r, s], originalCoreMask='core',
                allPrimesRough=all(q > n*n for q in primes),
                beyondPolynomialSieveCap=s > n*n, blocks=blocks,
                clippedEdgesJoined=math.fsum(b['clippedValue'] for b in blocks),
                fullOrbitsJoined=math.fsum(b['fullValue'] for b in blocks),
                originalPhaseAndAllocationRetained=True,
                originalCommonWeightUnchanged=True,
                sourceScaledLogAmplitude=log_amplitude,
                floatingUnderflow=log_amplitude < -745,
                distinctOriginalIncidences=True, additionalLongAffineOrbit=long_orbit,
                floorCertified=False)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--N', type=int, default=256)
    ap.add_argument('--height', type=float, default=54)
    args = ap.parse_args()
    examples = [original_example(args.N, args.height),
                original_example(args.N, args.height, rough=True)]
    print(json.dumps(dict(diagnosticOnly=True, originalExamples=examples,
                         arithmeticPopulationProvedInLean=True,
                         cofinalStartingOrderCertified=False,
                         wholeFloorCertified=False), indent=2))


if __name__ == '__main__':
    main()

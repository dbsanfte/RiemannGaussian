#!/usr/bin/env python3
"""Optional whole-bin cover and remaining signed-crossing probes.

Actual-prime checks exercise unique ownership and signed partitioning
below the eventual theorem thresholds. Large-log crossing probes are
continuous models with integer-grid prime logarithms, NOT prime labels.
No numerical floor, population payment or effective start is certified.
This script is not invoked by ordinary builds or CI.
"""
import itertools
import json
import math

import mpmath as mp

from probe_riesz_dense_count_cover import dyadic_scale
from probe_riesz_clipped_owner_period import ownership_rows
from probe_riesz_dense_populations import all_location_prices

mp.mp.dps = 100


def actual_cofactor_stability():
    rows = []
    head = mp.log(2)  # Diagnostic rescaling; NOT the formal head >=5000.
    for row in ownership_rows():
        ps = sorted(row['actualSquarefreeFactors'])[:-1]
        a = math.prod(ps)
        pattern = sorted({dyadic_scale(mp.log(q), head) for q in ps
                          if head < mp.log(q)})
        extensions = []
        for p in (269, 271, 277, 281, 283, 293):
            n = p*a
            assert p > max(ps) and n//p == a
            other = sorted({dyadic_scale(mp.log(q), head) for q in ps
                            if head < mp.log(q)})
            assert pattern == other
            extensions.append(p)
        rows.append(dict(originalCount=len(ps)+1, uniqueCofactor=a,
                         occupiedPattern=pattern, testedOwnerPrimes=extensions,
                         originalCountPreserved=True, diagnosticHeadRescaled=True,
                         literalCoreAndEventualThresholdCertified=False))
    return rows


def signed_pattern_partition():
    ps = [2, 3, 5, 7, 11, 13, 17, 19]
    head = mp.log(2)
    direct = mp.mpc(0)
    groups = {}
    labels = 0
    for bits in itertools.product((0, 1), repeat=len(ps)):
        factors = [p for p, b in zip(ps, bits) if b]
        if len(factors) < 3:
            continue
        n = math.prod(factors)
        owner = max(factors)
        a = n//owner
        pattern = tuple(sorted({dyadic_scale(mp.log(q), head)
                                for q in factors if q != owner and head < mp.log(q)}))
        # Arbitrary correlated allocation and full phase remain in the weight.
        allocation = mp.mpf(n % 11)/12
        t = mp.log(n)
        w = allocation * mp.exp(-t/2-mp.j*54*t)*t**7/math.factorial(7)
        direct += w
        groups[pattern] = groups.get(pattern, mp.mpc(0))+w
        labels += 1
    error = abs(direct-mp.fsum(groups.values()))
    assert error < mp.mpf('1e-90')
    return dict(actualSquarefreeLabels=labels, uniquePatterns=len(groups),
                signedPartitionError=float(error), allocationAndPhaseRetained=True,
                diagnosticHeadRescaled=True, numericalCarrierFloorCertified=False)


def grid_subset_counts(logs):
    signed, unsigned = [1], [1]
    for x in logs:
        a, b = [0]*(len(signed)+x), [0]*(len(unsigned)+x)
        for i, v in enumerate(signed):
            a[i] += v
            a[i+x] -= v
        for i, v in enumerate(unsigned):
            b[i] += v
            b[i+x] += v
        signed, unsigned = a, b
    assert sum(unsigned) == 2**len(logs)
    return signed, unsigned


def tent(x, a, b):
    return max(mp.mpf(0), min(x, a, b, a+b-x))


def remaining_crossing_probe(ratio, count):
    # Integer-grid log models allow an EXACT signed subset-count polynomial;
    # they do not certify prime existence or multiplicative independence.
    logs = sorted(set(round(3*ratio**i) for i in range(count)))
    a, b, background = logs[0], logs[1], logs[2:]
    signed, unsigned = grid_subset_counts(background)
    scale = mp.mpf(10)**6
    cofactor = sum(logs)*scale
    owner = cofactor*mp.mpf(11)/9
    total = owner+cofactor
    order = total/mp.mpf('1.99')
    u = mp.mpf(10001)/20000
    length = -2*order*mp.log(u)-2*mp.log(order+1)
    # Leading continuous moving length; the integer-cutoff rounding is NOT used.
    first, second = (total-length)/scale, (cofactor-length)/scale
    even = odd = mp.mpf(0)
    active_even = active_odd = 0
    for x, (sg, un) in enumerate(zip(signed, unsigned)):
        if not un:
            continue
        value = tent(first-x, a, b)-tent(second-x, a, b)
        if not value:
            continue
        e, o = (un+sg)//2, (un-sg)//2
        even += e*value
        odd += o*value
        active_even += e
        active_odd += o
    response = (-1)**len(logs)*(even-odd)*scale
    unsigned_response = (abs(even)+abs(odd))*scale
    head = max(mp.mpf(5000), 32*mp.log(order+1))
    bins = {dyadic_scale(x*scale, head) for x in logs if x*scale > head}
    cap = int(mp.floor(mp.log(order+1)/16))
    support = [i for i, v in enumerate(unsigned) if v]
    gap = min(y-x for x, y in zip(support, support[1:]))
    separated = gap >= a+b
    kind = ('inactive' if not active_even and not active_odd else
            'separated' if separated else
            'both-parities' if active_even and active_odd else 'one-parity')
    assert len(bins) > cap and len(logs)+1 < 5*mp.log(order+1)+2
    return dict(continuousIntegerLogModel=True, actualPrimeLabel=False,
                exactMovingIntegerLength=False, originalCarrierMasksCertified=False,
                ratio=ratio, cofactorCount=len(logs), logN=float(mp.log(order)),
                occupiedBinCount=len(bins), newPaidBinCeiling=cap,
                survivingCrossingClass=kind, activeEvenCount=active_even,
                activeOddCount=active_odd,
                joinedSignedResponse=float(response),
                unsignedResponse=float(unsigned_response),
                signedToUnsignedRatio=(float(abs(response)/unsigned_response)
                                       if unsigned_response else 0),
                globalPopulationBoundCertified=False)


def main():
    print(json.dumps(dict(
        diagnosticOnly=True, ordinaryBuildOrCI=False,
        numericalFloorCertified=False, effectiveStartingOrderCertified=False,
        actualCofactorStability=actual_cofactor_stability(),
        signedPartition=signed_pattern_partition(),
        allLocationPrices=all_location_prices(),
        remainingCrossings=[remaining_crossing_probe(r, k) for r, k in
                            ((1.2, 24), (1.35, 24), (1.6, 18), (1.9, 14), (2.0, 14), (2.01, 14))],
        checkedLedger='same original supply: new1/512 spent,1/512 retained',
        remaining='fixed counts3,4,6,7; lower growing counts with more '
                  'occupied bins; total separated cost; mixed-parity '
                  'transport and unmatched one-parity populations; numerical margin',
        falseInferenceAvoided='relative period price decay is not source-normalized norm decay',
    ), indent=2, allow_nan=False))


if __name__ == '__main__':
    main()

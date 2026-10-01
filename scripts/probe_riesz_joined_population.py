#!/usr/bin/env python3
"""Optional current count56+ signed-crossing models.

These are continuous INTEGER-LOG geometries, not actual prime labels.
The original complex/factorial/allocation weight is common to each
label's divisor response and is NOT priced by this diagnostic.
No population estimate, numerical whole floor or effective start is proved.
The probe is outside ordinary builds/CI.
"""
import json
import math

import mpmath as mp

from probe_riesz_few_bin_cover import grid_subset_counts, tent
from probe_riesz_dense_count_cover import dyadic_scale

mp.mp.dps = 100


def geometry(logs, owner_share):
    scale = mp.mpf(10)**6
    cofactor = sum(logs)*scale
    total = cofactor/(1-owner_share)
    order = total/mp.mpf('1.99')
    u = mp.mpf(10001)/20000
    length = -2*order*mp.log(u)-2*mp.log(order+1)
    first, second = (total-length)/scale, (cofactor-length)/scale
    head = max(mp.mpf(5000), 32*mp.log(order+1))
    bins = {dyadic_scale(x*scale, head) for x in logs if head < x*scale}
    cap = int(mp.floor(mp.log(order+1)/16))
    assert len(logs)+1 >= 56 and len(logs)+1 < 5*mp.log(order+1)+2
    assert len(bins) > cap
    return scale, first, second, dict(
        continuousIntegerLogModel=True, actualPrimeLabel=False,
        exactMovingIntegerLength=False, literalCoreMasksCertified=False,
        ownerShare=float(owner_share), totalPrimeCount=len(logs)+1,
        logN=float(mp.log(order)), occupiedBinCount=len(bins),
        newPaidBinCeiling=cap, stillInMergedCountAndBinRange=True,
        commonPhaseFactorialAndAllocationNotEstimated=True,
        globalPopulationCostCertified=False)


def current_crossings(ratio, nominal_count):
    logs = sorted({round(3*ratio**i) for i in range(nominal_count)})
    scale, first, second, result = geometry(logs, mp.mpf(11)/20)
    a, b = logs[:2]
    signed, unsigned = grid_subset_counts(logs[2:])
    # Sum only the exact supported tents; zero terms are not errors.
    active = set()
    for axis in (first, second):
        lo = max(0, int(mp.floor(axis-a-b)))
        hi = min(len(signed)-1, int(mp.ceil(axis)))
        active.update(range(lo, hi+1))
    even = odd = mp.mpf(0)
    ev = od = 0
    for x in sorted(active):
        sg, un = signed[x], unsigned[x]
        value = tent(first-x, a, b)-tent(second-x, a, b)
        if not value or not un:
            continue
        e, o = (un+sg)//2, (un-sg)//2
        even += e*value
        odd += o*value
        ev += e
        od += o
    response = (-1)**len(logs)*(even-odd)*scale
    cost = (abs(even)+abs(odd))*scale
    result.update(ratio=ratio, activeEvenCount=ev, activeOddCount=od,
                  signedTwoHingeResponse=float(response),
                  unsignedTwoHingeResponse=float(cost),
                  signedToUnsignedRatio=float(abs(response)/cost) if cost else 0,
                  universalCancellationFractionCertified=False)
    return result


def separated_growing(owner_share):
    # 54 background binary logs, so unique divisor translations are12*j.
    # Exactly one can hit a tent of width3+6; no2^54 enumeration is needed.
    logs = [3*2**i for i in range(56)]
    scale, first, second, result = geometry(logs, owner_share)
    response = mp.mpf(0)
    active = []
    for side, axis in ((1, first), (-1, second)):
        j = int(mp.floor(axis/12))
        value = (tent(axis-12*j, 3, 6)
                 if 0 <= j < 2**54 else mp.mpf(0))
        if value:
            parity = (-1)**j.bit_count()
            response += side*parity*value*scale
            active.append(dict(hinge=side, activeDivisorIndex=j,
                               subsetParity=parity, tentHeight=float(value*scale)))
    assert abs(response) <= 2*3*scale
    result.update(separatedDivisorLogStep=12e6, twoPrimeTentWidth=9e6,
                  activeTents=active, signedTwoHingeResponse=float(response),
                  countFreeFloor=-6e6, commonWeightOmittedFromModel=True)
    return result


def main():
    print(json.dumps(dict(
        diagnosticOnly=True, ordinaryBuildOrCI=False,
        numericalWholeFloorCertified=False, effectiveStartingOrderCertified=False,
        sameSupplyRetained='257/512 (Lean ledger, not a source-normalized floor constant)',
        growingMixedCrossings=[current_crossings(r, k) for r, k in
            ((1.04, 96), (1.08, 70), (1.12, 65), (1.16, 60), (1.2, 58))],
        growingSeparatedCrossings=[separated_growing(mp.mpf(q))
                                  for q in ('0.54', '0.55', '0.56')],
        remaining='count four, plus56<=omega<5log(N+1)+2 with many bins; '
                  'total separated cost, mixed transport and unmatched parity cost; '
                  'final independent rational margin',
    ), indent=2, allow_nan=False))


if __name__ == '__main__':
    main()

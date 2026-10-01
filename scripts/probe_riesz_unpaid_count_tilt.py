#!/usr/bin/env python3
"""Optional post-cancellation count-budget probe; not a prime certificate.

All counts, both parities and the literal clipped-count shift are included.
This compares the proven factorial population price, not actual prime
density. The fixed arithmetic head is kept symbolic. Nothing runs in
ordinary builds or CI, and no source-scale whole floor is inferred.
"""

import json
import math

import mpmath as mp

mp.mp.dps = 100


def count_tail_upper(mass, first):
    """Entire infinite positive budget, using decreasing term ratios."""
    ratio = 2*mass/(first+1)
    assert ratio < 1
    leading = mp.exp(first*mp.log(2*mass)-mp.loggamma(first+1))
    return leading/(1-ratio)


def row(log_x):
    x = mp.exp(log_x)
    # Numerical MODEL ONLY: C_head=0 is factored out, not evaluated.
    mass = mp.mpf(log_x)
    first = math.ceil(5*log_x)
    raw_tail = count_tail_upper(mass, first)
    tilted = mp.exp(5*mass-5*log_x*mp.log(mp.mpf(5)/2))
    rational_bound = mp.exp(mp.mpf(log_x)/2)
    assert raw_tail <= tilted <= rational_bound
    owner_scale = (x-1)/(64*log_x)
    total = 2*(x-1)
    assert total <= 128*owner_scale*log_x
    main_price = 481*tilted/owner_scale
    boundary_price = 1536*tilted/owner_scale
    joined = main_price+boundary_price
    assert abs(joined-2017*tilted/owner_scale) < mp.mpf('1e-60')*joined
    locations = 1+mp.log(4*x)/mp.log(2)
    global_actual_tilt = joined*locations
    conservative = 258176*log_x*mp.exp(-mp.mpf(log_x)/2)*locations
    assert global_actual_tilt <= conservative
    return dict(
        logNPlusOne=log_x,
        firstCofactorCount=first,
        minimumWholeBoundaryCount=first+2,
        oldPaidCountCoefficient=float(8/mp.log(2)),
        logInfiniteCountTailUpper=float(mp.log(raw_tail)),
        logExactTiltBudget=float(mp.log(tilted)),
        logRationalTiltBudget=float(mp.log(rational_bound)),
        logGlobalJoinedPriceWithoutHead=float(mp.log(global_actual_tilt)),
        logConservativePriceWithoutHead=float(mp.log(conservative)),
        bothParitiesAndAllHigherCountsIncluded=True,
        actualClippedCountShiftRetained=True,
        oldSpentCountRangeDisjoint=True,
        reciprocalPrimeMassIsModel=True,
        actualPrimePopulation=False,
        arithmeticHeadEvaluated=False,
        wholePhysicalFibreCoverCertified=False,
        sourceNormalizedWholeFloorCertified=False,
    )


def threshold_scan():
    rows = []
    for c in [2, 3, 4, 4.4, 5, 8/math.log(2)]:
        count_coefficient = mp.mpf(str(c))
        exponent = count_coefficient*(1-mp.log(count_coefficient/2))-1
        rows.append(dict(countPerLogN=c,
                         optimizedPostOwnerPower=float(exponent),
                         decaysInBudgetModel=exponent < 0,
                         formalThresholdIsFive=c == 5))
    return rows


def main():
    print(json.dumps(dict(
        diagnosticOnly=True,
        ordinaryBuildOrCI=False,
        newArithmeticFloorCertified=False,
        supplyUnit='exp(-v/2) * v^N/N!',
        headDependence='formal price contains exp(5*C_head); not evaluated here',
        rows=[row(t) for t in [32, 64, 128, 256, 512, 1024]],
        thresholdBudgetScan=threshold_scan(),
        remaining='Lower-count dense overlaps, separated population funding, '
                  'whole literal fibre cover and placement into the floor ledger.'
    ), indent=2, allow_nan=False))


if __name__ == '__main__':
    main()

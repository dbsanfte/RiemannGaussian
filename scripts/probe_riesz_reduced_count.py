#!/usr/bin/env python3
"""Optional quantitative regression of the checked global count saving.

All quoted geometric allowances are eventual. Finite dyadic samples do not
certify a starting order, a whole-population mass, or the remaining floor.
No zero ordinate is assumed; this script is outside ordinary builds/CI.
"""

import argparse
import json
import math

from probe_riesz_hinge_allocation import original_label


def rates():
    radius = 10001/20000
    tilt = 499999/1000000
    root = math.exp(math.log(17/16)/256)
    raw = radius/tilt/root
    paid = (1+raw)/2
    assert math.isclose(root**256, 17/16, rel_tol=1e-12)
    assert (radius/tilt)**256 < 17/16
    assert 0 < raw < paid < 1
    return dict(radiusCeiling=radius, summableTilt=tilt,
                countRoot=root, rawGeometricRate=raw, paidGeometricRate=paid,
                rawLogRate=math.log(raw), paidLogRate=math.log(paid),
                crudeWholeSourceGrowthLogRate=math.log(2*radius),
                comparisonMassExponent=3/2-tilt,
                countDivisor=256, allShareGeometriesRetained=True,
                eventualStartEvaluated=False, fullComparisonMassEvaluated=False)


def schedule():
    result = []
    for j in (2, 5, 8, 16, 64):
        count_ceiling = 2**(j+3)
        order = 8*(j+4)*count_ceiling
        first_paid = (count_ceiling+255)//256
        root_log_cost = order*math.log(17/16)/256
        actual_count_log_saving = first_paid*math.log(count_ceiling)
        assert actual_count_log_saving >= root_log_cost-1e-10
        result.append(dict(j=j, N=order, K=count_ceiling,
                           firstPaidCount=first_paid,
                           largestStillRetainedCount=(count_ceiling-1)//256,
                           provedCountPowerLogSaving=root_log_cost,
                           actualCountPowerLogSaving=actual_count_log_saving,
                           finiteOrderPaymentCertified=False))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dyadic-index', type=int, choices=(1, 2), default=2)
    parser.add_argument('--height', type=float, default=54.)
    args = parser.parse_args()
    sample = original_label(args.dyadic_index, args.height)
    condition = sample['countCeiling'] <= 256*sample['count']
    assert condition
    print(json.dumps(dict(diagnosticOnly=True, rates=rates(), schedule=schedule(),
                         literalHingeSample=sample,
                         literalSampleSatisfiesCountCondition=condition,
                         exactOriginalMasksAndBothHingesRetained=True,
                         geometricThresholdEvaluated=False,
                         noZetaZeroHypothesisUsed=True,
                         remainingLowCountSignedSumBounded=False,
                         wholeFloorCertified=False), indent=2))


if __name__ == '__main__':
    main()

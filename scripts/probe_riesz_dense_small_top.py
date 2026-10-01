#!/usr/bin/env python3
"""Optional quantitative count-tilt audit, not a literal-prime certificate.

The finite/infinite count budget is compared directly in its correct
amplitude/v units. Arithmetic heads, prime fibres and source-scale
carrier cancellation are not inferred from this model.
"""

import json
import mpmath as mp

mp.mp.dps = 100


def row(log_x):
    x = mp.exp(log_x)
    order = x-1
    total = 2*order
    scale = total/(512*log_x)
    owner_scale = order/4
    mass = mp.mpf(log_x)  # MODEL only; fixed real arithmetic head omitted.
    first_order = int(mp.ceil(total/(16*scale)-3))
    leading = mp.exp(first_order*mp.log(2*mass)-mp.loggamma(first_order+1))
    ratio = 2*mass/(first_order+1)
    assert ratio < 1
    exact_tail_upper = leading/(1-ratio)
    # Ratios decrease with k; this bounds the ENTIRE infinite tail, not
    # just a numerically truncated count range.
    tilted = 8*mp.exp(4*mass-total/(32*scale))
    clipped_tilted = 8*mp.exp(4*mass-total/(8*scale))
    assert exact_tail_upper <= tilted
    assert total/(32*scale) >= 16*log_x-mp.mpf('1e-80')
    assert 4*scale < owner_scale
    price_without_head = 3848*mp.exp(-12*log_x)*(1+mp.log(4*x)/mp.log(2))
    boundary_price_without_head = mp.mpf(16136)/3848*price_without_head
    return dict(logNPlusOne=log_x, minimumBudgetCount=first_order,
                trueCoreCountLowerBound=32*log_x,
                logInfiniteCountTailUpper=float(mp.log(exact_tail_upper)),
                logLeanTiltBudget=float(mp.log(tilted)),
                logLiteralClippedTiltBudget=float(mp.log(clipped_tilted)),
                logGlobalRelativePriceWithoutFixedHead=float(mp.log(price_without_head)),
                logGlobalBoundaryPriceWithoutFixedHead=float(mp.log(boundary_price_without_head)),
                countLowerBoundExceedsAlreadyPaidThreshold=True,
                newUnpaidCoverageClaimed=False,
                smallTopAndOwnerScaleHypotheses=(scale >= 5000 and owner_scale >= 10000),
                ownerClipsEmptyInGeometry=True,
                reciprocalPrimeMassIsModel=True, actualPrimePopulation=False,
                arithmeticHeadEvaluated=False,
                literalMaskAndFibreCoverCertified=False,
                sourceNormalizedWholeFloorCertified=False)


def main():
    result = dict(diagnosticOnly=True, ordinaryBuildOrCI=False,
                  wholeFloorCertified=False, unrestrictedTotalMatchingCostCertified=False,
                  supplyUnit='exp(-v/2) * v^N/N!',
                  rows=[row(t) for t in [32, 64, 128, 256, 512, 1024]])
    print(json.dumps(result, indent=2, allow_nan=False))


if __name__ == '__main__':
    main()

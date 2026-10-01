#!/usr/bin/env python3
"""Optional intermediate-scale budget and parity-layer diagnostics.

The finite population regression uses actual squarefree integers. Large
clustered geometries are explicitly log models, not constructed primes.
No floor, effective starting order or whole-population cover is certified.
This script is not imported by ordinary builds or CI.
"""

import itertools
import json
import math

import mpmath as mp

mp.mp.dps = 70


def finite_population():
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    middle = {5, 11, 17, 23}
    good_mass = mp.fsum(mp.mpf(1)/p for p in primes if p not in middle)
    middle_mass = mp.fsum(mp.mpf(1)/p for p in middle)
    marker = mp.mpf(16)
    rows = []
    for ceiling in range(len(middle)+1):
        mass = mp.mpf(0)
        label_count = 0
        for flags in itertools.product([False, True], repeat=len(primes)):
            subset = [p for p, flag in zip(primes, flags) if flag]
            if sum(p in middle for p in subset) > ceiling:
                continue
            label_count += 1
            mass += mp.mpf(4)**len(subset)/math.prod(subset)
        bound = marker**ceiling*mp.exp(4*good_mass+4*middle_mass/marker)
        assert mass <= bound+mp.mpf('1e-55')
        rows.append(dict(intermediateCountCeiling=ceiling,
                         actualSquarefreeLabelCount=label_count,
                         actualWeightedReciprocalMass=float(mass),
                         markedEulerUpperBound=float(bound),
                         priceAppliedAfterSignedPeriod=True,
                         chebyshevScaleHypothesesTested=False))
    return rows


def optimized_costs():
    # If the gap mass is at most log(N)+O(1), the positive marker budget
    # has leading exponent c*log(t)+4/t-1 for m=c*log(N).
    # This is an allowance audit, not a signed carrier asymptotic.
    critical = mp.findroot(lambda c: c*(1+mp.log(4/c))-1,
                           (mp.mpf('.26'), mp.mpf('.28')))
    rows = []
    for share in ['.05', '.125', '.25', '.26', '.27', '.28', '.5', '1']:
        c = mp.mpf(share)
        marker = max(mp.mpf(1), 4/c)
        optimum = c*mp.log(marker)+4/marker-1
        fixed = c*mp.log(16)+mp.mpf(1)/4-1
        rows.append(dict(gapCountPerLogN=float(c), optimalPositiveMarker=float(marker),
                         optimizedPositivePriceExponent=float(optimum),
                         fixedMarker16PriceExponent=float(fixed),
                         LeanQuarterCountRange=(c <= mp.mpf(1)/4)))
    assert mp.mpf('.27') < critical < mp.mpf('.28')
    assert rows[2]['fixedMarker16PriceExponent'] < -.05
    return dict(allowanceOnly=True, criticalCountPerLogN=float(critical), rows=rows)


def radial_prices():
    rows = []
    for log_n in [16, 32, 64, 128, 256, 512, 1024, 2048]:
        # Divided by the two fixed, unevaluated Lean arithmetic constants.
        price = 221440*(32*mp.mpf(log_n))**8*(1+(mp.log(4)+log_n)/mp.log(2))*mp.exp(-mp.mpf(log_n)/20)
        rows.append(dict(logNPlusOne=log_n,
                         intermediateCountCeiling=int(mp.floor(mp.mpf(log_n)/4)),
                         logRelativePriceWithoutFixedArithmeticHeads=float(mp.log(price)),
                         correctSupplyUnit='exp(-v/2) * v^N / N!',
                         arithmeticHeadEvaluated=False,
                         certifiedStartingOrder=False))
    return rows


def tent(x, a, b):
    if x <= 0 or x >= a+b:
        return 0.
    return min(x, a, b, a+b-x)


def clustered_gap_model(order, intermediate_count):
    # Equal logs permit an EXACT binomial multiplicity aggregation in
    # this model, without enumerating 2^(12+m) subsets. Prime existence,
    # distinctness and all physical masks are NOT certified here.
    length = -2*order*math.log(10001/20000)-2*math.log(order+1)
    a, b = math.log(2), math.log(3)
    alpha = (length-(a+b)/2)/10
    middle_log = math.sqrt(order)
    cofactor = a+b+12*alpha+intermediate_count*middle_log
    total = 1.99*order
    owner = total-cofactor
    signed = 0.
    separate = 0.
    active_count = 0
    parities = set()
    for macro_count in range(13):
        for gap_count in range(intermediate_count+1):
            axis = macro_count*alpha+gap_count*middle_log
            response = tent(total-length-axis, a, b)-tent(cofactor-length-axis, a, b)
            if abs(response) < 1e-3:
                continue
            multiplicity = math.comb(12, macro_count)*math.comb(intermediate_count, gap_count)
            parity = (-1)**(12+intermediate_count-macro_count-gap_count)
            active_count += multiplicity
            parities.add(parity)
            signed += multiplicity*parity*response
            separate += multiplicity*abs(response)
    ceiling = math.floor(math.log(order+1)/4)
    assert separate > 0
    return dict(continuousLogModel=True, actualPrimeLabel=False,
                exactMovingIntegerLength=False, N=order,
                intermediateCount=intermediate_count,
                newIntermediateCountCeiling=ceiling,
                coveredByNewCountRange=intermediate_count <= ceiling,
                originalGappedSpectrumCovered=intermediate_count == 0,
                ownerLogPerN=owner/order,
                ownerCapGeometry=owner <= 243*order/200,
                cofactorQuarterGeometry=cofactor > total/4,
                activeOrbitCount=active_count, activeParities=sorted(parities),
                joinedToSeparateRatio=abs(signed)/separate,
                entirePopulationMassCertified=False)


def main():
    print(json.dumps(dict(
        diagnosticOnly=True, ordinaryBuildOrCI=False,
        wholeFloorCertified=False, unrestrictedTotalMatchingCostCertified=False,
        finiteActualSquarefreeRegression=finite_population(),
        markerOptimization=optimized_costs(), correctRadialPrice=radial_prices(),
        clusteredCoverage=[clustered_gap_model(10**10, m) for m in [0, 1, 5, 6, 24]],
        remaining='Dense intermediate populations and incomplete original prime fibres '
                  'still require signed bounds. Vanishing relative supply cost is not '
                  'absolute source-o(1), and disjoint supply credits are not created.'
    ), indent=2, allow_nan=False))


if __name__ == '__main__':
    main()

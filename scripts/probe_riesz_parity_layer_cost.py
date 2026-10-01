#!/usr/bin/env python3
"""Optional count-cost and coverage diagnostics, outside builds and CI.

No prime-density transport, cofinal floor or population cover is certified.
The finite reciprocal regression uses actual primes. The large-log parity
layouts are explicitly continuous geometry models, not literal integers.
Costs use amplitude/v, the actual positive-supply units.
"""

import json
import math

import mpmath as mp
import numpy as np

from probe_riesz_hinge_pair import subset_arrays

mp.mp.dps = 70


def finite_reciprocal_regression():
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    logs = [math.log(p) for p in primes]
    axes, counts = subset_arrays(logs)
    J = max(logs)/4
    M = math.fsum(1/p for p in primes)
    rows = []
    for fraction in [.2, .4, .6, .8]:
        v = 4*fraction*math.fsum(logs)
        active = axes >= v/4
        mass = float(np.sum(np.exp(counts[active]*math.log(2)-axes[active])))
        # An actual squarefree reciprocal population, with its total-log
        # restriction retained. Prime-interval thresholds are not tested.
        bound = 8*math.exp(4*M-v/(32*J))
        assert mass <= bound*(1+1e-12)
        rows.append(dict(v=v, actualConstrainedSquarefreeMass=mass,
                         tiltedCountUpperBound=bound, J=J, M=M,
                         chebyshevThresholdMet=False))
    return rows


def count_tail_stress():
    rows = []
    for M in [3, 8, 16]:
        for radial_to_cofactor_scale in [16, 64, 256, 1024, 4096]:
            ratio = mp.mpf(radial_to_cofactor_scale)
            k0 = max(0, math.ceil(float(ratio/16-3)))
            probability = (mp.mpf(1) if k0 == 0 else
                           mp.gammainc(k0, 0, 2*M, regularized=True))
            log_actual = 2*M+mp.log(probability)
            log_bound = mp.log(8)+4*M-ratio/32
            assert log_actual <= log_bound+mp.mpf('1e-50')
            rows.append(dict(M=M, radialToCofactorScale=int(ratio),
                             firstAllowedCount=k0,
                             exactFactorialCountLogPrice=float(log_actual),
                             tiltedFactorialCountLogBound=float(log_bound),
                             unconditionedFactorialCountLogPrice=2*M))
    return rows


def supply_units():
    rows = []
    for log_n in [8, 16, 32, 64, 96, 128, 192, 256]:
        n = mp.exp(log_n)
        # Exactly the Lean expression divided by its fixed, unevaluated
        # gappedHeadCost. No actual starting-order certificate follows.
        price = 221440*(32*log_n)**8*(1+mp.log(4*n)/mp.log(2))/n
        rows.append(dict(logNPlusOne=log_n,
                         logSupplyPriceDividedByFixedHeadCost=float(mp.log(price)),
                         fixedArithmeticHeadEvaluated=False,
                         actualSupplyUnits='exp(-v/2) * v^N / N!'))
    return rows


def two_prime_tent(x, a, b):
    # Stable exact piecewise formula, avoiding cancellation between large
    # max terms when the genuine tent is identically zero.
    if x <= 0 or x >= a+b:
        return 0.
    return max(0., min(x, a, b, a+b-x))


def spectrum_layout(order, mesoscopic):
    # Geometry model ONLY: the moving length's leading expression. Do
    # not materialize its exponentially large exact physical cutoff.
    # This is explicitly not the literal integer carrier regression.
    length = -2*order*math.log(10001/20000)-2*math.log(order+1)
    a, b = math.log(2), math.log(3)
    alpha = (length-(a+b)/2)/10
    background = [alpha]*12
    if mesoscopic:
        background.append(math.sqrt(order))
    axes, ranks = subset_arrays(background)
    cofactor = a+b+math.fsum(background)
    total = 1.99*order
    owner = total-cofactor
    response = []
    for axis in axes:
        response.append(two_prime_tent(total-length-axis, a, b)-
                        two_prime_tent(cofactor-length-axis, a, b))
    response = np.array(response)
    active = np.flatnonzero(np.abs(response) > 1e-3)
    J = max(background)/4
    B = W = 32*math.log(order+1)
    omitted = [x for x in background if B < x < J/W]
    parity = np.where((len(background)-ranks) % 2, -1, 1)
    histogram = {str(int(k)): int(np.sum(ranks[active] == k))
                 for k in np.unique(ranks[active])}
    return dict(continuousGeometryModel=True, actualPrimeLabel=False,
                N=order, layout=('one mesoscopic prime' if mesoscopic else 'cluster'),
                largestOwnerLogPerN=owner/order,
                retainedOwnerCap=owner <= 243*order/200,
                cofactorQuarterConstraint=cofactor > total/4,
                selectedCount=15+int(mesoscopic), J=J, B=B, W=W,
                eventualPrimeMassScaleThreshold=J >= 10000*W,
                coveredByGrowingSpreadPrice=not omitted,
                omittedIntermediateLogs=omitted,
                activeUnsignedCountHistogram=histogram,
                activeParities=sorted({int(x) for x in parity[active]}),
                activeOrbitCount=len(active),
                joinedToSeparateRatio=(abs(float(np.sum(parity[active]*response[active])))/
                                      float(np.sum(np.abs(response[active]))) if len(active) else None),
                globalPopulationMassCertified=False)


def main():
    print(json.dumps(dict(
        diagnosticOnly=True, ordinaryBuildOrCI=False,
        wholeFloorCertified=False, totalMatchingCostCertified=False,
        finiteReciprocalRegression=finite_reciprocal_regression(),
        exactCountTailStress=count_tail_stress(),
        correctSupplyPrice=supply_units(),
        coverageAudit=[spectrum_layout(10**10, flag) for flag in [False, True]],
        limitation='The mesoscopic interval B < log p < J/W is not paid. '
                   'Reinforcing parity layers can survive there too. '
                   'Complete original fibre/mask cover and disjoint reserve credits remain necessary.'
    ), indent=2, allow_nan=False))


if __name__ == '__main__':
    main()

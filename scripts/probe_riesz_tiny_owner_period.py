#!/usr/bin/env python3
"""Optional quantitative regression for the original signed owner price.

No literal carrier, prime interval cancellation, starting order, supply
constant, source-scale decay, or whole numerical floor is certified here.
The cap-free signed estimate and its infinite count/shell sums are proved
in Lean. The large-order rows below audit only the curvature formula.
"""

from fractions import Fraction
import json
import math

from probe_riesz_log_shell import finite_symmetry


def curvature_rows():
    N = 10**12
    v, y = 2*N, 54
    result = []
    for k in (6, 100, 1000, 10**6, 10**8):
        P0 = v/(k+1)+math.pi/y
        b = v-math.pi/y-P0
        H = P0/2
        price = ((2*math.pi/y)*(N+1)/((v-math.pi/y)*P0**2*y**2)
                 + 4/P0**2)
        assert H >= 5000 and b/k >= H and b/k <= P0
        assert price*H**2 <= 5
        result.append(dict(order=N, cofactorCount=k, ownerLogLower=P0,
                           shellLower=H, cofactorShare=b/v,
                           oldCofactorCapSatisfied=b <= .985*v,
                           curvaturePriceTimesShellSquared=price*H**2,
                           provedUpperBound=5,
                           idealLogGeometryOnly=True))
    return result


def shell_series():
    result = []
    for last in (0, 1, 5, 20, 100):
        s = sum((Fraction(1, 2**j) for j in range(last+1)), Fraction(0))
        assert s <= 2
        result.append(dict(lastShell=last, exactInversePriceSum=str(s),
                           bound=2, noNumberOfShellsLoss=True))
    return result


def main():
    M = 5*math.log(4)
    constant = 481*4**10
    partial = math.fsum(math.exp(math.log(481)+k*math.log(2*M)-math.lgamma(k+1))
                        for k in range(2, 257))
    assert partial <= constant
    count_costs = [dict(k=k, logCountPrice=math.log(481)+k*math.log(2*M)
                       - math.lgamma(k+1)) for k in (6, 14, 40, 100, 256, 1000)]
    print(json.dumps(dict(diagnosticOnly=True, originalOwnerAtomRetained=True,
                         curvatureRows=curvature_rows(),
                         exactFiniteSquarefreeSymmetry=finite_symmetry(),
                         dyadicShellPrices=shell_series(),
                         allCountConstant=constant,
                         partialCountPriceThrough256=partial,
                         countCosts=count_costs,
                         relativeAllShellPrice="126091264 / log(N+1)",
                         originalCofactorCapRetained=False,
                         wholePrimeFibresRequired=True,
                         compatibleDisjointLedgerCoverProved=False,
                         supplyPriceFraction="1/256 of the same selected supply",
                         supplyScaleMustBeRetained=True,
                         sourceScaleDecayClaimed=False,
                         otherPrimeHolesPaid=False,
                         wholeFloorCertified=False,
                         effectiveStartingOrderCertified=False), indent=2))


if __name__ == "__main__":
    main()

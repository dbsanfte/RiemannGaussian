#!/usr/bin/env python3
"""Optional dense-count cover/remaining-budget regression.

The finite ownership checks use actual primes, far below the eventual
Chebyshev threshold; they test unique incidence and endpoint bookkeeping.
The quantitative scan is the already-cancelled factorial PRICE with the
unknown arithmetic head factored out. It is not the original carrier,
an effective starting-order certificate, or a numerical floor proof.
Nothing here is invoked by ordinary builds or CI.
"""

import json
import math

import mpmath as mp

from probe_riesz_clipped_owner_period import ownership_rows, exact_symmetry

mp.mp.dps = 100


def dyadic_scale(value, base=mp.mpf(1)):
    """Unique half-open bin base*2^i < value <= 2*base*2^i."""
    assert value > base
    i = int(mp.ceil(mp.log(value/base, 2)))-1
    assert base*2**i < value <= base*2**(i+1)
    return i


def actual_owner_cover():
    results = []
    for row in ownership_rows():
        factors = sorted(row['actualSquarefreeFactors'])
        owner, second = factors[-1], factors[-2]
        assert owner == row['owner'] and second == row['secondPrime']
        a = math.prod(factors[:-1])
        t = mp.log(owner*a)
        y = mp.mpf(54)
        v = t-mp.mpf('0.9')*mp.pi/y
        start = v-mp.pi/y-mp.log(a)
        complete = mp.log(second) <= start
        close = mp.log(owner)-mp.log(second) < mp.mpf(1)/8
        assert complete or close
        assert complete == (not row['ownerStartClipped'])
        scale = dyadic_scale(start if complete else mp.log(second))
        # Shifted signs use separate grids. Each grid has ONE total-log
        # period and ONE owner/second-owner scale for this original label.
        phases = []
        for b in (mp.pi/y, 2*mp.pi/y):
            i = int(mp.ceil((t-b-mp.pi/y)/(2*mp.pi/y)))
            center = b+i*2*mp.pi/y
            assert center-mp.pi/y < t <= center+mp.pi/y
            phases.append(i)
        results.append(dict(
            totalPrimeCount=len(factors), removedPairCount=len(factors)-2,
            owner=owner, secondOwner=second,
            branch='complete-owner-fibre' if complete else 'canonical-second-owner-clip',
            uniqueDyadicScale=scale, staggeredPeriodIndices=phases,
            actualSquarefreeLabel=True, originalLiteralCoreCertified=False,
            eventualChebyshevThresholdMet=False,
        ))
    # Exact dyadic endpoints go into the preceding bin, never both.
    for i in range(20):
        assert dyadic_scale(mp.mpf(2)**(i+1)) == i
    return results


def budget_rows():
    rows = []
    for log_x in (32, 64, 128, 256, 512):
        mass = mp.mpf(log_x)  # MODEL C_head=0; not the actual prime mass.
        old = math.ceil(8*log_x/math.log(2))
        selected = list(range(math.ceil(5*log_x), old-1))
        price = mp.fsum((2*mass)**k/mp.factorial(k) for k in selected)
        tilt = mp.exp(5*mass-5*log_x*mp.log(mp.mpf(5)/2))
        assert price <= tilt <= mp.exp(mp.mpf(log_x)/2)
        global_without_head = (mp.mpf(258176)*log_x*mp.exp(-mp.mpf(log_x)/2)*
                               (1+mp.log(4*mp.exp(log_x))/mp.log(2)))
        rows.append(dict(logNPlusOne=log_x,
                         newWholeLabelLowerCount=math.ceil(5*log_x+2),
                         approximateOldTailCount=old,
                         logExactFinitePostCancellationCountPrice=float(mp.log(price)),
                         logTiltPrice=float(mp.log(tilt)),
                         logGlobalRelativePriceWithoutHead=float(mp.log(global_without_head)),
                         arithmeticHeadEvaluated=False,
                         literalSourceScaleFloorCertified=False))
    return rows


def central_gap_scan():
    """Locate what this proven high-count cancellation CANNOT pay."""
    rows = []
    for c in (mp.mpf(1)/3, mp.mpf(1), mp.mpf(2), mp.mpf(3),
              mp.mpf(4), mp.mpf('4.4'), mp.mpf(5)):
        exponent = c*(1-mp.log(c/2))-1
        rows.append(dict(countPerLogN=float(c),
                         optimizedPostOwnerBudgetPower=float(exponent),
                         priceModelDecays=exponent < 0,
                         centralBudgetObstruction=c == 2,
                         newSignedCancellationCertifiedHere=False))
    return rows


def main():
    print(json.dumps(dict(
        diagnosticOnly=True, ordinaryBuildOrCI=False,
        numericalFloorCertified=False, effectiveStartingOrderCertified=False,
        actualOwnershipBookkeeping=actual_owner_cover(),
        exactSquarefreeSymmetry=exact_symmetry(),
        wholeBandPrices=budget_rows(),
        remainingCentralPriceScan=central_gap_scan(),
        sameSupplyLedger='1/128 retained before this slice; 1/256 spent, 1/256 retained',
        distinction='Relative signed price tends to zero; positive source units need not.',
        remaining='Low fixed counts; few-bin lower-count fibre cover; total separated '
                  'population cost; many-bin mixed-parity matching and one-parity layers.',
    ), indent=2, allow_nan=False))


if __name__ == '__main__':
    main()

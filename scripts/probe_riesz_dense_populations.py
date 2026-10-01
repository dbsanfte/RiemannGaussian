#!/usr/bin/env python3
"""Optional dense-population and joined signed-tent regression.

Small finite checks use actual prime labels. The growing lacunary family
is explicitly a continuous log model; it certifies no prime existence,
physical fibre cover, supply reserve or source-normalized carrier bound.
Nothing in this script runs in ordinary builds or CI.
"""

import itertools
import json
import math

import mpmath as mp

mp.mp.dps = 350


def subsets(items):
    return [tuple(x for x, bit in zip(items, flags) if bit)
            for flags in itertools.product([False, True], repeat=len(items))]


def is_prime(n):
    return n >= 2 and (n == 2 or n % 2 and all(
        n % d for d in range(3, math.isqrt(n)+1, 2)))


def tent(x, a, b):
    if x <= 0 or x >= a+b:
        return mp.mpf(0)
    return min(x, a, b, a+b-x)


def finite_patterns():
    primes = [2, 3, 5, 7, 11, 13, 17, 19]
    assert all(is_prime(p) for p in primes)
    middle = set(primes)-{2}
    base = mp.log(2)
    bins = {p: int(mp.ceil(mp.log(mp.log(p)/base, 2)))-1 for p in middle}
    for p, i in bins.items():
        assert base*2**i < mp.log(p) <= base*2**(i+1)
    available = sorted(set(bins.values()))
    all_labels = subsets(primes)
    rows = []
    for cap in range(len(available)+1):
        direct = mp.mpc(0)
        groups = {}
        masses = {}
        label_count = 0
        for support in all_labels:
            pattern = tuple(sorted({bins[p] for p in support if p in middle}))
            if len(pattern) > cap:
                continue
            label_count += 1
            n = math.prod(support)
            log_n = mp.log(n)
            weight = mp.exp(-log_n/2-3j*log_n)*log_n**6/math.factorial(6)
            direct += weight
            groups[pattern] = groups.get(pattern, mp.mpc(0))+weight
            masses[pattern] = masses.get(pattern, mp.mpf(0))+mp.mpf(4)**len(support)/n
        assert abs(direct-mp.fsum(groups.values())) < mp.mpf('1e-300')
        for pattern, mass in masses.items():
            # An actual small-prime numeric regression, not an application
            # of the formal B>=5000 leading-one prime estimate.
            assert mass <= 3*mp.mpf(32)**len(pattern)
        rows.append(dict(occupiedBinCeiling=cap, actualLabelCount=label_count,
                         uniqueOccupiedPatternCount=len(groups),
                         complexPartitionError=float(abs(direct-mp.fsum(groups.values()))),
                         leadingOneLargePrimeHypothesesTested=False))
    return rows


def all_location_prices():
    rows = []
    for log_x in [160, 256, 512, 1024, 2048, 4096]:
        grid = 2*log_x+1
        cap = log_x//16
        price = mp.fsum(mp.mpf(math.comb(grid, k))*32**k for k in range(cap+1))
        assert price <= mp.exp(1+mp.mpf(log_x)/2)
        rows.append(dict(logNPlusOne=log_x, availableBinUpperCount=grid,
                         occupiedBinCeiling=cap,
                         logExactAllLocationBudget=float(mp.log(price)),
                         logLeanPatternUpperBound=1+log_x/2,
                         logBudgetAfterRadialDivision=float(mp.log(price)-log_x),
                         arithmeticHeadEvaluated=False,
                         supplyUnit='exp(-v/2) * v^N/N!',
                         absoluteSourceDecayCertified=False))
    return rows


def finite_separated_response():
    background = [11, 101, 10007, 1000000007]
    marked = 32416190071
    assert all(is_prime(p) for p in [2, 3, marked]+background)
    a, b = mp.log(2), mp.log(3)
    ell = a+b
    prev = mp.mpf(0)
    for p in background:
        assert ell+prev <= mp.log(p)
        prev += mp.log(p)
    cofactor_support = [2, 3]+background
    cofactor_log = mp.fsum(mp.log(p) for p in cofactor_support)
    total_log = cofactor_log+mp.log(marked)
    background_subsets = subsets(background)
    divisor_logs = sorted(mp.fsum(mp.log(p) for p in support)
                          for support in background_subsets)
    gap = min(y-x for x, y in zip(divisor_logs, divisor_logs[1:]))
    assert gap >= ell
    w = mp.mpc('.7', '.3')
    rows = []
    for length in [a/2, ell/2, mp.log(11)+ell/2,
                   cofactor_log-mp.log(101)-ell/2,
                   total_log-mp.log(10007)-ell/2]:
        # Original divisor hinge, with both hinges and ALL ranks joined.
        original = mp.fsum(
            (-1)**len(support)*(max(0, mp.log(marked)+mp.fsum(mp.log(p) for p in support)-length)
                                  -max(0, mp.fsum(mp.log(p) for p in support)-length))
            for support in subsets(cofactor_support))
        joined = mp.mpf(0)
        active = [0, 0]
        for support in background_subsets:
            axis = mp.fsum(mp.log(p) for p in support)
            first = tent(total_log-length-axis, a, b)
            second = tent(cofactor_log-length-axis, a, b)
            active[0] += first != 0
            active[1] += second != 0
            joined += (-1)**(len(background)-len(support))*(first-second)
        assert abs(original-joined) < mp.mpf('1e-300')
        assert max(active) <= 1
        debit = 2*abs(w.real)*min(a, b)
        assert (w*joined).real >= -debit-mp.mpf('1e-300')
        rows.append(dict(length=float(length), activeTentsAtEachHinge=active,
                         entireSignedResponse=float((w*joined).real),
                         countFreeFloor=-float(debit),
                         originalToJoinedError=float(abs(original-joined))))
    return dict(actualSquarefreeLabel=True, literalCoreMasksCertified=False,
                physicalFibreCoverCertified=False, backgroundPrimeCount=len(background),
                backgroundDivisorCount=2**len(background),
                smallestDivisorLogGap=float(gap), tentWidth=float(ell), rows=rows)


def growing_lacunary_model(log_n):
    # Work entirely in LOG geometry. The length is the leading moving
    # length, not the enormous integer linearDampedCutoff of the repo.
    order = mp.exp(log_n)
    u = mp.mpf(10001)/20000
    length = -2*order*mp.log(u)-2*mp.log(order+1)
    total = mp.mpf('1.99')*order
    a, b = mp.log(2), mp.log(3)
    ell = a+b
    count = 3*log_n//5
    subset_ceiling = 2**count-1
    target = int(mp.floor((total-length)/(mp.mpf('1.2')*order)*subset_ceiling))
    scale = (total-length-ell/2)/target
    background = [scale*2**j for j in range(count)]
    cofactor = ell+mp.fsum(background)
    owner = total-cofactor
    assert all(ell+mp.fsum(background[:i]) <= x for i, x in enumerate(background))
    signed = mp.mpf(0)
    active = [0, 0]
    for index, hinge_axis in enumerate([total-length, cofactor-length]):
        candidate = int(mp.floor(hinge_axis/scale))
        if 0 <= candidate <= subset_ceiling:
            response = tent(hinge_axis-candidate*scale, a, b)
            active[index] = int(response != 0)
            signed += (1 if index == 0 else -1)*(-1)**(count-candidate.bit_count())*response
    assert abs(signed) <= 2*min(a, b)
    head = 32*mp.log(order+1)
    jscale = max(background)/4
    middle = [x for x in background if head < x < jscale/head]
    occupied = {int(mp.ceil(mp.log(x/head, 2)))-1 for x in middle}
    return dict(continuousLogModel=True, actualPrimeLabel=False,
                exactMovingIntegerLength=False, logN=log_n,
                totalBackgroundCount=count, intermediateFactorCount=len(middle),
                occupiedIntermediateBinCount=len(occupied),
                sparseGapCountCeiling=int(mp.floor(mp.log(order+1)/4)),
                denseBinPatternCeiling=int(mp.floor(mp.log(order+1)/16)),
                coveredBySparseGapCount=len(middle) <= mp.log(order+1)/4,
                coveredByDenseBinPrice=len(occupied) <= mp.log(order+1)/16,
                separatedDivisorCertificate=True, activeTentsAtEachHinge=active,
                joinedRealResponseWithUnitWeight=float(signed),
                countFreeDebit=float(2*min(a, b)),
                ownerLogPerN=float(owner/order),
                ownerLargestGeometry=owner >= max(background),
                ownerCapGeometry=owner <= mp.mpf(243)*order/200,
                cofactorQuarterGeometry=cofactor >= total/4,
                populationCostCertified=False, physicalMasksCertified=False)


def main():
    print(json.dumps(dict(
        diagnosticOnly=True, ordinaryBuildOrCI=False,
        wholeFloorCertified=False, totalUnrestrictedMatchingCostCertified=False,
        finiteActualOccupiedPatternRegression=finite_patterns(),
        weightedAllLocationBudgets=all_location_prices(),
        actualPrimeSeparatedRegression=finite_separated_response(),
        growingSeparatedLogModels=[growing_lacunary_model(t) for t in [256, 512, 640]],
        remaining='Diffuse overlapping mixed-parity and one-parity populations; '
                  'total separated population cost; original fibre cover and fresh reserve.'
    ), indent=2, allow_nan=False))


if __name__ == '__main__':
    main()

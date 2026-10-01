#!/usr/bin/env python3
"""Optional signed small-cofactor regression, outside builds and CI.

Group the original divisor incidences of ONE label before pricing them.
The full phase, owner allocation and factorial kernel are common to that
label. Compare clustered and spread large-prime backgrounds; neither is
a count of the arithmetic population. Growing-count examples use model
logarithms, explicitly distinguished from actual prime labels.
"""

import argparse
import cmath
import json
import math
import random

import mpmath as mp
import numpy as np
from sympy import isprime, nextprime, primerange

from probe_riesz_canonical_joint import allocation, core_mask
from probe_riesz_hinge_pair import subset_arrays
from probe_riesz_lower_radial import parameters


def prime_near_log(value):
    with mp.workdps(max(50, int(value / math.log(10)) + 12)):
        return int(nextprime(int(mp.exp(value))))


def small_kernel(points, logs):
    """Exact finite-difference formula, with algebraic exterior zeros.

    Long doubles reduce subtraction noise. The exterior-zero shortcut is
    valid only for at least two factors. It is not a claimed arithmetic
    population payment or a phase approximation.
    """
    points = np.asarray(points, dtype=np.longdouble)
    response = np.zeros_like(points)
    active = (points > 0) & (points < math.fsum(logs))
    axis = points[active]
    subset_logs, counts = subset_arrays(logs)
    for offset, count in zip(subset_logs, counts):
        response[active] += (-1 if count % 2 else 1) * np.maximum(0, axis - offset)
    return response


def folded_profile(n, owner_log, length, small_logs, large_logs,
                   multiplicities=None, height=54.):
    """No triangle inequality across the large-factor bases or counts."""
    if multiplicities is None:
        axes, counts = subset_arrays(large_logs)
        multiplicities = np.ones_like(axes)
    else:
        axes, counts = large_logs
        axes = np.asarray(axes, dtype=np.longdouble)
        counts = np.asarray(counts)
        multiplicities = np.asarray(multiplicities, dtype=np.longdouble)
    parity = np.where(counts % 2, -1, 1)
    total_small = math.fsum(small_logs)
    first_args = owner_log + axes + total_small - length
    half_period = math.pi / abs(height)
    first_gap = np.where(first_args <= 0, -first_args,
                         np.where(first_args >= total_small,
                                  first_args - total_small, 0))
    first_frozen = bool(np.all((first_args + half_period <= 0) |
                              (first_args - half_period >= total_small)))
    response = (-1) ** len(small_logs) * (
        small_kernel(owner_log + axes + total_small - length, small_logs)
        - small_kernel(axes + total_small - length, small_logs)
    )
    signed = np.sum(multiplicities * parity * response, dtype=np.longdouble)
    joined_block_price = np.sum(multiplicities * np.abs(response), dtype=np.longdouble)

    # Previously retained canonical two-small-prime blocks. Only their
    # absolute price is compared; the signed sum is a regression invariant.
    pair = small_logs[:2]
    tail_axes, tail_counts = subset_arrays(small_logs[2:])
    pair_price = np.longdouble(0)
    pair_signed = np.longdouble(0)
    surviving_bases = {}
    for extra, extra_count in zip(tail_axes, tail_counts):
        base = axes + extra
        block = (
            small_kernel(owner_log + base + sum(pair) - length, pair)
            - small_kernel(base + sum(pair) - length, pair)
        )
        sign = parity * (-1) ** int(extra_count)
        pair_signed += np.sum(multiplicities * sign * block, dtype=np.longdouble)
        pair_price += np.sum(multiplicities * np.abs(block), dtype=np.longdouble)
        # Nonzero actual cofactor-hinge blocks: the other hinge is already
        # saturated, and the based whole-window owner gap fails.
        d = base + sum(pair) - length
        retained = ((0 < d) & (d < sum(pair)) &
                    (owner_log + d >= sum(pair)) &
                    (2 * owner_log + base + sum(pair) <= 2.03 * n))
        for count in np.unique(counts[retained]):
            mask = retained & (counts == count)
            key = int(count + extra_count + 2)
            surviving_bases[key] = surviving_bases.get(key, np.longdouble(0)) + np.sum(
                multiplicities[mask], dtype=np.longdouble)
    scale = max(1, float(pair_price))
    assert abs(float(pair_signed - signed)) < 1e-8 * scale
    assert abs(float(signed)) <= float(joined_block_price) + 1e-8 * scale
    assert float(joined_block_price) <= float(pair_price) + 1e-8 * scale
    return dict(signedResponse=float(signed), oldPairPrice=float(pair_price),
                joinedSmallBlockPrice=float(joined_block_price),
                remainingCountCancellationRatio=(float(abs(signed) / joined_block_price)
                                                 if joined_block_price > 1e-9 else None),
                smallBlockToOldPairPrice=(float(joined_block_price / pair_price)
                                          if pair_price > 1e-9 else None),
                survivingCrossingCountHistogram={str(k): float(v)
                                                 for k, v in surviving_bases.items()},
                wholePhasePeriodFirstHingeZero=first_frozen,
                minimumFirstHingeSupportGap=float(np.min(first_gap)),
                phasePeriodHalfWidth=half_period,
                signedIdentityResidual=float(abs(pair_signed - signed)))


def label_probe(index, small_count, spread, offset, height):
    ceiling = 2 ** (index + 3)
    n = 8 * (index + 4) * ceiling
    pars = parameters(n)
    small = list(primerange(2, 100))[:small_count]
    small_logs = [math.log(p) for p in small]
    big_count = 10 if index == 1 else 20
    anchor = 8 if index == 1 else 16
    alpha = (pars['length'] - sum(small_logs) / 2 + offset * small_logs[0]) / anchor
    ratios = [1.] * big_count
    if spread:
        rng = random.Random(20261002 + small_count + index)
        ratios = [rng.uniform(.5, 1.5) for _ in range(big_count)]
        mean = sum(ratios) / big_count
        ratios = [v / mean for v in ratios]
    large = []
    for ratio in ratios:
        p = prime_near_log(alpha * ratio)
        while p in large:
            p = int(nextprime(p))
        large.append(p)
    owner = prime_near_log(1.99 * n - math.log(math.prod(small + large)))
    primes = [owner, *small, *large]
    assert max(primes) == owner and len(set(primes)) == len(primes)
    assert all(isprime(p) for p in primes)
    label = math.prod(primes)
    mask = core_mask(n, label, dict.fromkeys(primes, 1), pars, ceiling)
    assert mask == 'core', mask
    total = math.log(label)
    unassigned = 1 - allocation(n, pars['orders'], 1 - math.log(owner) / total)
    log_weight = ((n + 1) * math.log(10001 / 20000) - 1.5 * total +
                  (n + 1) * math.log(total) - math.lgamma(n + 1) -
                  math.log(pars['length']) + math.log(unassigned))
    profile = folded_profile(n, math.log(owner), pars['length'], small_logs,
                             [math.log(p) for p in large], height=height)
    return dict(diagnosticOnly=True, actualPrimeLabel=True, dyadicIndex=index,
                N=n, originalCoreMask=mask, totalCount=len(primes), countCeiling=ceiling,
                belowReducedCountCeiling=256 * len(primes) < ceiling,
                abovePolynomialOwnerCut=math.log(owner) > 32 * math.log(n + 1),
                smallPrimes=small, background='spread' if spread else 'clustered',
                midpointOffset=offset, totalLogPerN=total / n,
                originalCommonPhaseReal=cmath.exp(-1j * height * total).real,
                originalOwnerAllocatedFraction=1 - unassigned,
                sourceScaledCommonLogWeight=log_weight,
                floatingUnderflow=log_weight < -745,
                originalPhaseAndAllFactorialWeightsRetained=True,
                sourcePopulationMassCertified=False, **profile)


def clustered_growing_probe(index, big_count, small_count, offset):
    ceiling = 2 ** (index + 3)
    n = 8 * (index + 4) * ceiling
    # Model cases do not materialize the astronomical exact integer
    # cutoff. Retain its moving logarithmic length; the omitted rounding
    # is exponentially small, but is not certified by this probe.
    length = 2 * (-n * math.log(10001 / 20000) - math.log(n + 1))
    small_logs = [math.log(p) for p in list(primerange(2, 100))[:small_count]]
    anchor = round(.8 * big_count)
    alpha = (length - sum(small_logs) / 2 + offset * small_logs[0]) / anchor
    owner_log = 1.99 * n - big_count * alpha - sum(small_logs)
    # Binomial multiplicities are EXACT for the equal-log model. Dividing
    # by its active binomial coefficient avoids enormous floating totals.
    reference = math.comb(big_count, anchor)
    counts = list(range(big_count + 1))
    axes = [k * alpha for k in counts]
    multiplicities = [math.comb(big_count, k) / reference for k in counts]
    profile = folded_profile(n, owner_log, length, small_logs, (axes, counts), multiplicities)
    assert 256 * (big_count + small_count + 1) < ceiling
    assert owner_log > 32 * math.log(n + 1)
    assert max(alpha, owner_log) < .65 * (1.99 * n)
    return dict(diagnosticOnly=True, actualPrimeLabel=False, equalLogModel=True,
                N=n, largeFactorCount=big_count, smallFactorCount=small_count,
                belowReducedCountCeiling=True, abovePolynomialOwnerCut=True,
                originalLogWindowAndOwnerGeometry=True,
                activeMultiplicityNormalization=f'binomial({big_count},{anchor})',
                midpointOffset=offset, **profile)


def reflection_probe(small_count):
    """Check the signed block, not a density approximation of prime labels.

    Use high precision in the midpoint and integrated-moment regressions.
    Reflection zeros and moment zeros are already exact algebraically;
    their finite checks identify which profile regularity would exploit them.
    """
    with mp.workdps(70):
        logs = [mp.log(p) for p in list(primerange(2, 100))[:small_count]]
        total = mp.fsum(logs)
        subsets = [(mp.mpf(0), 1)]
        for value in logs:
            subsets += [(s + value, -sign) for s, sign in list(subsets)]

        def kernel(d):
            return mp.fsum(sign * max(mp.mpf(0), d - s) for s, sign in subsets)

        samples = []
        for offset in (-mp.mpf('0.2'), -mp.mpf('0.1'), mp.mpf(0),
                       mp.mpf('0.1'), mp.mpf('0.2')):
            distance = offset * logs[0]
            d = total / 2 + distance
            old_price = mp.mpf(0)
            tail = [(mp.mpf(0), 1)]
            for value in logs[2:]:
                tail += [(s + value, -sign) for s, sign in list(tail)]
            for s, _ in tail:
                pair_response = mp.fsum(sign * max(mp.mpf(0), d - s - a)
                                       for a, sign in subsets[:4])
                old_price += abs(pair_response)
            # Reflection + the existing quarter divisor-mass Lipschitz
            # estimate gives this explicit joined bound for ODD blocks.
            odd_bound = (2 ** small_count / 4) * abs(distance)
            if small_count % 2:
                assert abs(kernel(d)) <= odd_bound + mp.mpf('1e-55')
            samples.append(dict(offsetInLeastPrimeLogs=float(offset),
                                joinedResponse=float(kernel(d)),
                                oldPairPrice=float(old_price),
                                oddReflectionBound=(float(odd_bound)
                                                    if small_count % 2 else None),
                                joinedToSeparatePrice=(float(abs(kernel(d)) / old_price)
                                                       if old_price else None)))
        moments = []
        for order in range(min(small_count - 2, 4)):
            value = mp.fsum(sign * (
                total ** (order + 2) / (order + 2)
                - s * total ** (order + 1) / (order + 1)
                + s ** (order + 2) / ((order + 1) * (order + 2)))
                for s, sign in subsets)
            assert abs(value) < mp.mpf('1e-50')
            moments.append(dict(order=order, absoluteResidual=float(abs(value))))
        return dict(diagnosticOnly=True, smallPrimeCount=small_count,
                    smallPrimes=list(primerange(2, 100))[:small_count],
                    sameLabelPhaseAndWeightRetained=True,
                    midpointSamples=samples, continuousProfileMomentZeros=moments,
                    actualPrimeCrossingProfileRegularityCertified=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dyadic-index', type=int, choices=(1, 2), default=1)
    parser.add_argument('--height', type=float, default=54.)
    args = parser.parse_args()
    actual = [label_probe(args.dyadic_index, m, spread, offset, args.height)
              for m in (2, 3, 4) for spread in (False, True)
              for offset in (0., .2)]
    growing = [clustered_growing_probe(j, k, m, offset)
               for j, k in ((12, 64), (14, 256)) for m in (2, 3, 4, 5, 6, 7, 8)
               for offset in (0., .2)]
    print(json.dumps(dict(actualPrimeLabels=actual, growingCountLogModels=growing,
                         smallBlockReflectionProfiles=[reflection_probe(m)
                                                        for m in (3, 4, 5, 6, 7, 8)],
                         conclusion='Small factors give exact finite differences and can join canonical blocks. A clustered crossing can retain one reinforcing large-factor count; smallness alone is not a generic zero-cost removal.',
                         currentCofinalLiteralPopulationBoundCertified=False,
                         wholeFloorCertified=False), indent=2))


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Optional joined active-crossing probe; never part of builds or CI.

Actual squarefree labels retain the original count/window/owner/physical
masks, phase and factorial allocation. Match opposite Mobius ranks only
inside ONE original label, so their common weight is unchanged. Both
hinges, all unmatched incidences and the two previous zero deletions are
accounted for. Small orders do not certify the cofinal remaining population.
"""

import argparse
import cmath
import json
import math
import random

import numpy as np
from scipy.optimize import linear_sum_assignment
from sympy import isprime, nextprime

from probe_riesz_canonical_joint import allocation, core_mask
from probe_riesz_hinge_pair import subset_arrays
from probe_riesz_lower_radial import parameters
from probe_riesz_small_cofactor import prime_near_log, small_kernel


def crossing_transport(large_logs, small_logs, owner, length, order, height):
    axes, counts = subset_arrays(large_logs)
    small_span = math.fsum(small_logs)
    cofactor_log = small_span + math.fsum(large_logs)
    total = cofactor_log + owner
    first_args = total - length - axes
    second_args = cofactor_log - length - axes
    first = small_kernel(first_args, small_logs)
    second = small_kernel(second_args, small_logs)
    response = first - second
    parity = np.where((len(large_logs) - counts) % 2, -1, 1)

    # Literal selectors from ShortOrbit and UnpaidAffineOrbit. They
    # delete entire canonical blocks. Active nonzero blocks cannot be
    # falsely credited by the old zero deletions.
    short = ((axes + small_span < total - 3899 * order / 2000) &
             (axes + small_span <= total - length) &
             ((first_args <= owner) |
              (owner + axes + small_span <= total - length)) &
             (owner < 243 * order / 200))
    affine = ((axes + small_span <= total - length) &
              ((first_args <= owner) |
               (owner + axes + small_span <= total - length)) &
              (owner < 243 * order / 200) &
              (total - axes + owner <= 203 * order / 100) & ~short)
    assert np.max(np.abs(response[short | affine]), initial=0) < 1e-8
    active = np.flatnonzero((np.abs(response) > 1e-8) & ~(short | affine))
    positive = [i for i in active if parity[i] == 1]
    negative = [i for i in active if parity[i] == -1]
    separate = float(np.sum(np.abs(response[active])))
    signed = float(np.sum(parity[active] * response[active]))

    pairs = []
    saving = 0.
    matched = set()
    if positive and negative:
        distances = np.abs(np.asarray(axes[positive, None] - axes[negative], dtype=float))
        first_inactive = ((first_args[positive, None] >= small_span) &
                          (first_args[negative] >= small_span))
        second_inactive = ((second_args[positive, None] <= 0) &
                           (second_args[negative] <= 0))
        slopes = np.where(first_inactive | second_inactive, 1., 2.)
        costs = slopes * distances
        allowances = np.asarray(np.abs(response[positive, None]) +
                                np.abs(response[negative]), dtype=float)
        profits = np.maximum(0., allowances - costs)
        rows, cols = linear_sum_assignment(-profits)
        for row, col in zip(rows, cols):
            if profits[row, col] <= 1e-10:
                continue
            e, f = positive[row], negative[col]
            matched.update([e, f])
            joined = float(response[e] - response[f])
            cost = float(costs[row, col])
            assert abs(joined) <= cost + 1e-8
            saving += float(profits[row, col])
            pairs.append(dict(unsignedRanks=[int(counts[e]), int(counts[f])],
                              remainingLargePrimeRanks=[len(large_logs)-int(counts[e]),
                                                        len(large_logs)-int(counts[f])],
                              logDistance=float(distances[row, col]),
                              bothOriginalResponses=[float(response[e]), float(response[f])],
                              joinedResponse=joined,
                              signedTransportCost=cost,
                              separateAllowance=float(allowances[row, col]),
                              oneHingeInactive=bool(slopes[row, col] == 1)))
    unmatched = [i for i in active if i not in matched]
    transport = separate - saving
    assert abs(signed) <= transport + 1e-7
    histogram = {str(int(k)): int(np.sum(counts[active] == k))
                 for k in np.unique(counts[active])}
    return dict(activeCount=len(active), activeUnsignedCountHistogram=histogram,
                pairedBases=len(matched), unmatchedBases=len(unmatched),
                matchedPairs=pairs, separateCrossingAllowance=separate,
                wholeJoinedSignedResponse=signed,
                wholeTransportAllowance=transport,
                wholeTransportToSeparateRatio=(transport/separate if separate else None),
                actualJoinedToSeparateRatio=(abs(signed)/separate if separate else None),
                priorZeroOrbitCount=int(np.sum(short | affine)),
                priorZeroDeletionResidual=float(np.max(np.abs(response[short | affine]), initial=0)),
                retainedSignedIdentityResidual=float(abs(np.sum(parity*response)-signed)))


def actual_label(seed, clustered=False, height=54.):
    index = 1
    count_ceiling = 2**(index+3)
    order = 8*(index+4)*count_ceiling
    pars = parameters(order)
    small = [2, 3]
    small_logs = [math.log(p) for p in small]
    rng = random.Random(seed)
    ratios = [1.] * 12 if clustered else [rng.uniform(.06, 1.94) for _ in range(12)]
    mean = math.fsum(ratios)/12
    target_logs = [v/mean*(pars['length']-math.log(6)/2)/10 for v in ratios]
    large = []
    for value in target_logs:
        p = prime_near_log(value)
        while p in large:
            p = int(nextprime(p))
        large.append(p)
    owner = prime_near_log(1.99*order-math.log(math.prod(small+large)))
    primes = [owner, *small, *large]
    assert max(primes) == owner and len(primes) == len(set(primes))
    assert all(isprime(p) for p in primes)
    label = math.prod(primes)
    mask = core_mask(order, label, dict.fromkeys(primes, 1), pars, count_ceiling)
    assert mask == 'core', mask
    total = math.log(label)
    owner_log = math.log(owner)
    unallocated = 1-allocation(order, pars['orders'], 1-owner_log/total)
    source_log_weight = ((order+1)*math.log(10001/20000)-1.5*total+
                         (order+1)*math.log(total)-math.lgamma(order+1)-
                         math.log(pars['length'])+math.log(unallocated))
    phase = cmath.exp(-1j*height*total)
    profile = crossing_transport([math.log(p) for p in large], small_logs,
                                 owner_log, pars['length'], order, height)
    return dict(diagnosticOnly=True, actualPrimeLabel=True, seed=seed,
                background=('clustered' if clustered else 'spread'),
                N=order, countCeiling=count_ceiling, totalPrimeCount=len(primes),
                originalCoreMask=mask, centralWindow=1.97*order<total<=2.03*order,
                belowReducedCountCeiling=256*len(primes)<count_ceiling,
                abovePolynomialOwnerCut=owner_log>32*math.log(order+1),
                totalLogPerN=total/order, originalOwnerAllocatedFraction=1-unallocated,
                originalPhaseReal=phase.real, originalPhaseImag=phase.imag,
                sourceScaledCommonLogWeight=source_log_weight,
                floatingUnderflow=source_log_weight < -745,
                originalPhaseAndAllFactorialWeightsRetained=True,
                actualPrimeFactorLogarithms=sorted([math.log(p) for p in primes]),
                sourcePopulationMassCertified=False, **profile)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--height', type=float, default=54.)
    args = parser.parse_args()
    rows = [actual_label(seed, height=args.height) for seed in [1487, 1571, 398, 2, 1733]]
    rows.append(actual_label(0, clustered=True, height=args.height))
    print(json.dumps(dict(diagnosticOnly=True, ordinaryBuildOrCI=False,
                         wholeFloorCertified=False, labels=rows,
                         principle='Opposite parity transports the joined two-hinge profile; '
                                   'the cost is log distance, with no fixed count restriction.',
                         limitations=['These literal labels fail the later reduced-count crop.',
                                      'No arithmetic population cover or source-scale matching cost is certified.',
                                      'Separated parity layers may have no usable matching.',
                                      'Underflow is not cancellation.']), indent=2, allow_nan=False))


if __name__ == '__main__':
    main()

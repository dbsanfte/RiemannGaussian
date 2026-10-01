#!/usr/bin/env python3
"""Optional literal clipped-owner and normalization audit, outside CI.

Actual original core masks, full phase and allocation remain in the label
tests. Their order is below the eventual Chebyshev threshold; no population
mass, source-scale floor or effective starting order is certified. Cost
tables are normalized by the unevaluated fixed small-prime head constant.
"""

import argparse
import cmath
import json
import math

import mpmath as mp
from sympy import isprime, nextprime

from probe_riesz_canonical_joint import allocation, core_mask
from probe_riesz_hinge_pair import subset_arrays
from probe_riesz_lower_radial import parameters
from probe_riesz_small_cofactor import prime_near_log, small_kernel


def clipped_label(offset, index=1, height=54.):
    ceiling = 2 ** (index + 3)
    order = 8 * (index + 4) * ceiling
    pars = parameters(order)
    small = [2, 3]
    small_logs = [math.log(p) for p in small]
    # The last owner-pair cutoff is the only potentially active hinge.
    desired_cutoff = offset
    q = prime_near_log((pars['length'] - desired_cutoff) / 2)
    p = int(nextprime(q))
    target_middle_log = 1.99 * order - math.log(p * q * math.prod(small))
    middle = []
    for _ in range(7):
        b = prime_near_log(target_middle_log / 8)
        while b in middle:
            b = int(nextprime(b))
        middle.append(b)
    b = prime_near_log(target_middle_log - sum(math.log(v) for v in middle))
    while b in middle:
        b = int(nextprime(b))
    middle.append(b)
    primes = [p, q, *small, *middle]
    assert len(set(primes)) == len(primes) and all(isprime(v) for v in primes)
    assert max(primes) == p
    label = math.prod(primes)
    original_mask = core_mask(order, label, dict.fromkeys(primes, 1), pars, ceiling)
    assert original_mask == 'core', original_mask
    total = math.log(label)
    center = round(height * total / math.pi) * math.pi / height
    start = center - math.pi / height - math.log(label // p)
    clipped = math.log(q) > start
    assert clipped and math.log(p) - math.log(q) <= 1 / 8
    axes, counts = subset_arrays([math.log(v) for v in middle])
    cutoffs = [pars['length'], pars['length'] - math.log(p),
               pars['length'] - math.log(q), pars['length'] - math.log(p * q)]
    responses = []
    gaps = []
    for cutoff in cutoffs:
        args = cutoff - axes
        responses.append(float(sum(((-1) ** counts) * small_kernel(args, small_logs))))
        gaps.append(bool(all((args <= 0) | (args >= sum(small_logs)))))
    riesz_response = responses[0] - responses[1] - responses[2] + responses[3]
    unallocated = 1 - allocation(order, pars['orders'], 1 - math.log(p) / total)
    coefficient = -unallocated * total / pars['length'] * riesz_response
    log_kernel = (-1.5 * total + order * math.log(total) - math.lgamma(order + 1)
                  + (order + 1) * math.log(10001 / 20000))
    phase = cmath.exp(-1j * height * total)
    with mp.workdps(max(70, int(math.log(q) / math.log(10)) + 40)):
        tie_gap = mp.log(p) - mp.log(q)
    return dict(actualPrimeLabel=True, originalMask=original_mask, N=order,
                count=len(primes), countCeiling=ceiling,
                passesReducedCountCrop=256 * len(primes) < ceiling,
                totalLogPerN=total / order, actualOwnershipClip=clipped,
                twoOwnerLogGapHighPrecision=str(tie_gap),
                leastPrime=2, leastPrimeSurvivesDeletion=min(primes[2:]) == 2,
                fourTranslatedCutoffs=cutoffs, spectrumGapTests=gaps,
                fourJoinedRieszResponses=responses,
                fullRieszResponse=riesz_response,
                originalUnallocatedFraction=unallocated,
                fullArithmeticCoefficient=coefficient,
                originalPhaseReal=phase.real, originalPhaseImag=phase.imag,
                sourceScaledKernelLogNorm=log_kernel,
                floatingKernelUnderflow=log_kernel < -745,
                eventualChebyshevThresholdMet=start >= 5000)


def price_table():
    result = []
    for order in [256, 640, 1536, 4096, 8192, 65536, 1048576]:
        radial = 2 * (order + 1)
        b = math.log(order + 1)
        broad_displayed_price = 129088 / b**2
        new_supply_div_head = 504 * b * (1 + math.log(4 * (order + 1)) / math.log(2))
        result.append(dict(N=order, radialCenter=radial,
                           oldBroadDisplayedCoefficient=broad_displayed_price,
                           oldBroadActualSupplyCoefficient=radial * broad_displayed_price,
                           smallFlatAmplitudeCoefficientDivHead=new_supply_div_head / (order + 1),
                           smallFlatActualSupplyCoefficientDivHead=new_supply_div_head))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dyadic-index', type=int, default=1)
    args = parser.parse_args()
    labels = [clipped_label(offset, args.dyadic_index)
              for offset in [5., math.log(6) / 2, math.log(6) / 2 + .2 * math.log(2)]]
    report = dict(diagnosticOnly=True, ordinaryBuildOrCI=False,
                  currentCofinalPopulationFloorCertified=False,
                  smallPrimeHeadConstantNumericallyEvaluated=False,
                  actualLiteralOwnerClipTests=labels,
                  normalizationAndCostTable=price_table(),
                  conclusions=[
                      'The least prime survives deletion of the actual near-tied owner pair.',
                      'A joint four-cutoff gap gives exact zero; an active small-block hinge can survive.',
                      'The displayed decaying amplitude coefficient is not the actual supply coefficient.',
                      'The corrected all-count positive price grows; further signed cancellation is required.',
                      'Underflow and these finite labels certify no cofinal floor or population saving.'
                  ])
    print(json.dumps(report, indent=2, allow_nan=False))


if __name__ == '__main__':
    main()

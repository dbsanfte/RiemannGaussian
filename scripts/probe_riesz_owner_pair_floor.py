#!/usr/bin/env python3
"""Optional signed owner-allocation regression on actual inner-hinge labels.

Retains the rounded moving cutoff, full complex phase, factorial kernel,
actual eligible owner and signed population multipliers. The full allocation
and its exact nonowner difference are recorded separately. This is NOT a
native count56+ matching, interval certificate or floor certificate.
"""

import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import mpmath as mp
import sympy as sp
from probe_riesz_inner_hinge_transport import (
    atom, inner_conditions, number_string, setup, unpaid_orders,
)


def owner_weight(order, owner, primes):
    total_log = mp.fsum(mp.log(p) for p in primes)
    x = 1 - mp.log(owner) / total_log
    selected = mp.fsum(mp.binomial(order + 1, k) * x ** k *
                       (1 - x) ** (order + 1 - k) for k in unpaid_orders(order))
    lower = mp.fsum(mp.binomial(order + 1, k) * x ** k *
                    (1 - x) ** (order + 1 - k) for k in range(order // 5 + 2))
    assert lower <= 2 * mp.exp(-mp.mpf(order) / 25)
    return 1 - selected, x, lower


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    mp.mp.dps = 120
    rows = []
    for order, count in ((32, 2), (64, 4), (128, 6), (256, 8), (512, 10)):
        upper, length, owner, second, small = setup(order, count)
        inner_conditions(length, owner, second, small)
        primes = [owner, second, *small]
        for inserted in (2, 3, 5, 7):
            if inserted >= min(small):
                continue
            partner = int(sp.nextprime(owner // inserted))
            partners = [partner, second, inserted, *small]
            inner_conditions(length, partner, second, [inserted, *small])
            original_weight, x, lower = owner_weight(order, owner, primes)
            partner_weight, x_prime, lower_prime = owner_weight(order, partner, partners)
            error = 2 * mp.exp(-mp.mpf(order) / 25)
            assert mp.mpf(3) / 8 <= x <= x_prime <= 1
            assert original_weight <= partner_weight + error
            for height in (54, 65, 100):
                original, _, share = atom(order, length, height, primes, upper)
                other, _, other_share = atom(order, length, height, partners, upper)
                raw_original = original / (1 - share)
                raw_other = other / (1 - other_share)
                for multiplier in (mp.mpf(1), -mp.mpf(1) / 10):
                    F, G = raw_original, multiplier * raw_other
                    if F.real > 0:
                        continue
                    paired_owner = original_weight * F + partner_weight * G
                    envelope = abs(F) + abs(G)
                    mismatch_price = abs(F + G)
                    tail_price = error * abs(F)
                    # The positive allocation change is left signed.
                    assert paired_owner.real >= -(mismatch_price + tail_price) - envelope * mp.mpf('1e-90')
                    full_pair = original + multiplier * other
                    nonowner_difference = full_pair - paired_owner
                    rows.append({
                        'order': order, 'counts': [len(primes), len(partners)],
                        'height': height, 'signedMultipliers': ['1.0', number_string(multiplier)],
                        'cofactorShares': [number_string(x), number_string(x_prime)],
                        'ownerWeights': [number_string(original_weight), number_string(partner_weight)],
                        'lowerCumulativeMasses': [number_string(lower), number_string(lower_prime)],
                        'fullAllocationShares': [number_string(share), number_string(other_share)],
                        'ownerPairRealOverRawEnvelope': number_string(paired_owner.real / envelope),
                        'joinedRawMismatchOverEnvelope': number_string(mismatch_price / envelope),
                        'lowTailPriceOverEnvelope': number_string(tail_price / envelope),
                        'nonownerDifferenceOverEnvelope': number_string(abs(nonowner_difference) / envelope),
                        'absoluteAllocationDifferenceCharged': False,
                    })
    equal = [row for row in rows if row['signedMultipliers'] == ['1.0', '1.0']]
    assert equal and all(mp.mpf(row['ownerPairRealOverRawEnvelope']) >= 0 for row in equal)
    report = {
        'scope': 'Finite actual count4/5..12/13 inner-hinge pairs; signed owner-allocation gain with rounded native length and full original phases. Not native unpaid many-bin matching coverage.',
        'precisionDigits': 120, 'cases': rows, 'negativeFirstAtomCases': len(rows),
        'equalFundingOwnerPairNonnegativeInEveryTest': True,
        'equalFundingRawMismatchRatioRange': [number_string(min(mp.mpf(row['joinedRawMismatchOverEnvelope']) for row in equal)),
                                               number_string(max(mp.mpf(row['joinedRawMismatchOverEnvelope']) for row in equal))],
        'equalFundingOwnerPairRealRatioRange': [number_string(min(mp.mpf(row['ownerPairRealOverRawEnvelope']) for row in equal)),
                                                number_string(max(mp.mpf(row['ownerPairRealOverRawEnvelope']) for row in equal))],
        'nativeMovingLengthRetained': True, 'fullPhaseRetained': True,
        'signedFundingDifferencesRetained': True, 'nonownerDifferenceRecorded': True,
        'smallPrimesForbiddenByWholeCore': False,
        'oldFixedParityPacketRoughPrimeMaskSatisfied': False,
        'nativeCoreMembershipCertified': False,
        'nativeCount56ManyBinPopulationEvaluated': False,
        'fundingWitnessIncluded': False,
        'matchingCoverageCertified': False, 'weightedPrimeGapPriceCertified': False,
        'tinyRawResidualsMayBeBelowPrecision': True,
        'floatingResultsIntervalCertified': False, 'floorCertified': False,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k:report[k] for k in ('scope', 'negativeFirstAtomCases',
                                         'equalFundingOwnerPairNonnegativeInEveryTest',
                                         'equalFundingRawMismatchRatioRange',
                                         'equalFundingOwnerPairRealRatioRange', 'floorCertified')}, indent=2))


if __name__ == '__main__':
    main()

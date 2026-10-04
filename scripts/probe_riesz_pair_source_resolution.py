#!/usr/bin/env python3
"""Optional source-unit calibration for the existing joined-pair detector.

Collect the four ORIGINAL factorial slots before any floating evaluation.
The precision model is explicitly synthetic: it is not a prime-density
transport, a lower bound on the cost of every possible algorithm, or a
bound on prefixPairDefect. Frozen genuine-prime samples are read only to
audit coverage; no old sampling or discovery job is rerun.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path

import mpmath as mp

from probe_riesz_selberg_renewal import moving_length


TARGET = Fraction(399, 5000)
U = Fraction(10001, 20000)
FORMAL_ORDER_THRESHOLD = 65536
CACHES = (
    Path('.lake/riesz-pair-structure/scan.primes.json'),
    Path('.lake/riesz-pair-joint/new-primes.json'),
    Path('.lake/riesz-balanced-prime-sampling/result.primes.json'),
)


def number(value):
    return mp.nstr(value, 38)


def digest(path):
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def canonical(i, j, successor):
    """Both swapped order incidences, with each equal-order slot counted once."""
    return (min(i, j), max(i, j), successor)


def collect_original_slots(order):
    cutoff = 13 * order // 32
    mass = order + 1
    original = defaultdict(Fraction)
    replay = defaultdict(Fraction)
    slot_count = 0
    for k in range(cutoff + 1, mass - cutoff):
        original[canonical(k - 1, mass - k - 1, False)] += Fraction(mass, 2 * k * (mass - k))
        slot_count += 1
    for k in range(cutoff + 1, mass + 1 - cutoff):
        original[canonical(k - 1, mass - k, True)] -= Fraction(mass + 1, 2 * k * (mass + 1 - k))
        slot_count += 1
    for k in range(1, cutoff + 1):
        original[canonical(k - 1, mass - k, True)] -= Fraction(1, mass + 1 - k)
        slot_count += 1
    for k in range(order):
        original[canonical(k, order - 1 - k, False)] += Fraction(1, order)
        slot_count += 1

    # Independent replay of the exact three joined channels in harmonicEvaluation.
    for k in range(order):
        replay[canonical(k, order - 1 - k, False)] += Fraction(1, order)
    for k in range(cutoff + 1, order + 1 - cutoff):
        replay[canonical(k - 1, order - k, False)] += Fraction(1, order + 1 - k)
    for k in range(1, order + 2 - cutoff):
        replay[canonical(k - 1, order + 1 - k, True)] -= Fraction(1, order + 2 - k)

    assert dict(original) == dict(replay)
    assert all(i + j == order - 1 + int(shift) for i, j, shift in replay)
    assert all(value < 0 if shift else value > 0 for (_, _, shift), value in replay.items())
    # Logged order zero is genuine and retained in both surviving total orders.
    assert any(i == 0 and not shift for i, j, shift in replay)
    assert any(i == 0 and shift for i, j, shift in replay)
    # These are ORDER diagonals, not extra prime-square labels. The existing
    # whole square payment is not spent or changed by this calibration.
    return {
        'N': order, 'cutoff': cutoff, 'unjoinedSlots': slot_count,
        'collectedProducts': len(replay), 'exactRationalCollectionPassed': True,
        'loggedOrderZeroRetained': True,
        'collectedOrderDiagonals': sum(i == j for i, j, _ in replay),
        'newZeroCoefficientsFound': 0,
        'newCancellationIdentityFound': False,
    }


def harmonic(k):
    return mp.digamma(k + 1) + mp.euler


def calibration(order, u, source_margin):
    cutoff = 13 * order // 32
    length, floor_error, length_method = moving_length(order, u)
    positive = 1 + harmonic(order - cutoff) - harmonic(cutoff)
    negative = (order + 1) / (u * length) * (harmonic(order + 1) - harmonic(cutoff))
    selected = positive - negative
    growth = 2 * u

    # Synthetic reference array a_k = growth^(k+1) * phi_k, |phi_k|<=1.
    # This is NOT a proved exact formula for unsigned ordinary-prime moments.
    # Products in the two channels have total powers N+1 and N+2 respectively.
    reference_price = growth**(order + 1) * (positive + growth * negative)
    allowed_absolute_error = source_margin / 4
    q = allowed_absolute_error / reference_price
    # Stable positive root of eps^2 + 2 eps = q.
    phase_error = q / (mp.sqrt(1 + q) + 1)
    assert abs(reference_price * (2 * phase_error + phase_error**2)
               - allowed_absolute_error) < mp.mpf('1e-85')

    # A SUFFICIENT, deliberately conservative Hoeffding/union calibration
    # for bounded complex IID marks in this synthetic model. It is not a
    # minimum sample-size theorem and is NOT applied to cached prime draws.
    confidence_failure = mp.mpf('0.05')
    coordinate_count = order + 2
    sufficient_samples = 4 * mp.log(4 * coordinate_count / confidence_failure) / phase_error**2
    result = {
        'N': order, 'exactIntegerCutoff': cutoff,
        'formalOrderThresholdReached': order >= FORMAL_ORDER_THRESHOLD,
        'positiveJoinedCoefficientMass': number(positive),
        'negativeJoinedCoefficientMass': number(negative),
        'signedPureSelectedValue': number(selected),
        'pureSelectedValueAboveTarget': selected > mp.mpf(TARGET.numerator) / TARGET.denominator,
        'referenceAbsolutePrice': number(reference_price),
        'referenceArrayGrowth': number(growth),
        'referencePhaseErrorBudget': number(phase_error),
        'allowedSourceAbsoluteError': number(allowed_absolute_error),
        'sufficientIidSamplesLog10': number(mp.log10(sufficient_samples)),
        'sufficientIidSamplesIsNecessaryLowerBound': False,
        'iidModelAppliedToPrimeCaches': False,
        'movingLengthMethod': length_method,
        'movingLengthFloorErrorBound': number(floor_error),
        'actualUnsignedPrimeMomentMassComputed': False,
        'actualRetainedPrimeCarrierBounded': False,
    }
    if selected > mp.mpf(TARGET.numerator) / TARGET.denominator:
        critical = 1 - mp.sqrt((mp.mpf(TARGET.numerator) / TARGET.denominator) / selected)
        high_amplitude, low_amplitude = 1 - critical / 2, 1 - 2 * critical
        high_value = high_amplitude**2 * selected
        low_value = low_amplitude**2 * selected
        assert low_value < mp.mpf(TARGET.numerator) / TARGET.denominator < high_value
        result['syntheticSourceSensitivityRegression'] = {
            'criticalRelativeAmplitudeChange': number(critical),
            'aboveTargetValue': number(high_value), 'belowTargetValue': number(low_value),
            'bothReferencePhaseArraysHaveNormAtMostOne': True,
            'actualPrimeArraysOrZeroHypothesesUsed': False,
        }
    return result


def coverage():
    all_rows, distinct = [], set()
    for path in CACHES:
        data = json.loads(path.read_text())
        for index, row in enumerate(data['rows']):
            for side in ('left', 'right'):
                leg = row[side]
                assert leg['provedByFLINT']
                distinct.update(leg['primes'])
            logs = [mp.log(mp.mpf(p)) for side in ('left', 'right') for p in row[side]['primes']]
            all_rows.append((path, index, row, min(logs), max(logs)))
    levels = [('100', mp.log(100)), ('142', mp.log(142)),
              ('10^10000', 10000 * mp.log(10)), ('10^20000', 20000 * mp.log(10))]
    result = []
    for label, log_height in levels:
        pre_lattice = sum(log_height > hi for _, _, _, _, hi in all_rows)
        post_lattice = sum(log_height < lo for _, _, _, lo, _ in all_rows)
        result.append({
            'height': label, 'logAbsoluteHeight': number(log_height),
            'boxesWithHeightLargerThanEverySampledPrime': pre_lattice,
            'boxesWithHeightSmallerThanEverySampledPrime': post_lattice,
            'mixedBoxes': len(all_rows) - pre_lattice - post_lattice,
            'integerSpacingComparisonIsNotAPrimeGapEstimate': True,
        })
    return {
        'frozenInputs': [digest(path) for path in CACHES],
        'actualDistinctCachedPrimes': len(distinct), 'boxes': len(all_rows),
        'orders': sorted({row['N'] for _, _, row, _, _ in all_rows}),
        'boxesAtFormalOrderThreshold': sum(row['N'] >= FORMAL_ORDER_THRESHOLD for _, _, row, _, _ in all_rows),
        'sampledCartesianPairIncidences': sum(len(row['left']['primes']) * len(row['right']['primes'])
                                              for _, _, row, _, _ in all_rows),
        'cartesianPairsAreIndependentObservations': False,
        'knownCachePrimalityChecksRerun': False, 'newPrimeSamples': 0,
        'completePrimePopulationCovered': False,
        'heightRegimes': result,
    }


def run():
    mp.mp.dps = 120
    u = mp.mpf(U.numerator) / U.denominator
    source = 1 - (mp.log(mp.mpf(32) / 13) / (-2 * u * mp.log(u)) - mp.log(mp.mpf(19) / 13))
    target = mp.mpf(TARGET.numerator) / TARGET.denominator
    margin = source - target
    assert margin > 0
    orders = [256, 640, 1536, 65536, 131072, 425984, 1048576, 4194304]
    return {
        'classification': 'Exact joined-slot replay and source-unit detector calibration; no arithmetic saving',
        'sourceHead': '49db91eb2f5ea148c82b00bae9f241a836c272fe',
        'precisionDigits': mp.mp.dps, 'targetUnchanged': '399/5000',
        'radius': '10001/20000', 'selectedSimpleSource': number(source),
        'contradictionMarginNotMeasuredUnpaidMass': number(margin),
        'exactSlotRegressions': [collect_original_slots(n) for n in [32, 64, 256, 640, 1536, 8192]],
        'sourceCalibration': [calibration(n, u, margin) for n in orders],
        'actualFrozenCoverage': coverage(),
        'independentFloorProved': False, 'newZeroExclusion': False,
        'firstSourceThresholdCrossingCertified': False,
        'physicalOrFactorialMasksChanged': False,
        'calibrationConclusions': [
            'Cached phase precision does not imply population or source-unit resolution.',
            'The reference confidence cost is sufficient only, not an impossibility theorem.',
            'The model changes no literal packet and proves no arithmetic moment identity.',
            'Future discovery should target exact signed identities or a provable ordinary-prime constraint.',
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({
        'exactSlotRegressions': len(report['exactSlotRegressions']),
        'calibrationOrders': len(report['sourceCalibration']),
        'actualCachedPrimes': report['actualFrozenCoverage']['actualDistinctCachedPrimes'],
        'newPrimeSamples': 0, 'independentFloorProved': False,
    }))


if __name__ == '__main__':
    main()

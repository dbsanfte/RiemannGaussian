#!/usr/bin/env python3
"""Independent optional replay of source-unit calibration; no floor credit.

Imports no producer. Compare the complete factorial quadratic with the
joined logged evaluator on finite genuine-prime universes, then replay
the reported scalar prices and coverage from the frozen inputs.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path

import mpmath as mp


def close(left, right, tolerance=mp.mpf('1e-33')):
    assert abs(left - right) <= tolerance * max(1, abs(right)), (left, right)


def finite_prime_replay():
    primes = [2, 3, 5, 7, 11, 97, 257]
    assert all(all(p % d for d in range(2, math.isqrt(p) + 1)) for p in primes)
    errors = []
    u = mp.mpf(10001) / 20000
    for order, height in itertools.product([4, 16, 32, 64], [0, 54, 142]):
        cutoff, m = 13 * order // 32, order + 1
        damped = 20000**order // ((order + 1) * 10001**order)
        length = 2 * mp.log(damped + 2)
        moments = []
        for k in range(order + 3):
            moments.append(mp.fsum(mp.log(p)**k / mp.factorial(k)
                           * mp.exp((-mp.mpf(3) / 2 - 1j * height) * mp.log(p))
                           for p in primes))
        array = [u**(k + 1) * (k + 1) * moments[k + 1] for k in range(order + 2)]
        # Original four slots, not the collected coefficients in the producer.
        central = mp.mpf(m) / 2 * mp.fsum(moments[k] * moments[m - k]
                          for k in range(cutoff + 1, m - cutoff))
        successor = -mp.mpf(m) * (m + 1) / (2 * length) * mp.fsum(
            moments[k] * moments[m + 1 - k] for k in range(cutoff + 1, m + 1 - cutoff))
        prefix = -mp.mpf(m) / length * mp.fsum(k * moments[k] * moments[m + 1 - k]
                                             for k in range(1, cutoff + 1))
        trace = mp.fsum((k + 1) * (order - k) * moments[k + 1] * moments[order - k]
                        for k in range(order)) / order
        direct = u**m * (central + successor + prefix + trace)
        joined = mp.fsum(array[k] * array[order - 1 - k] for k in range(order)) / order
        joined += mp.fsum(array[k - 1] * array[order - k] / (order + 1 - k)
                          for k in range(cutoff + 1, order + 1 - cutoff))
        joined -= (order + 1) / (u * length) * mp.fsum(
            array[k - 1] * array[order + 1 - k] / (order + 2 - k)
            for k in range(1, order + 2 - cutoff))
        error = abs(direct - joined)
        assert error < mp.mpf('1e-95')
        errors.append(error)
    return len(errors), max(errors)


def replay(report):
    mp.mp.dps = 130
    u, target = mp.mpf(10001) / 20000, mp.mpf(399) / 5000
    source = 1 + mp.log(mp.mpf(19) / 13) + mp.log(mp.mpf(32) / 13) / (2 * u * mp.log(u))
    gap = source - target
    close(mp.mpf(report['selectedSimpleSource']), source)
    close(mp.mpf(report['contradictionMarginNotMeasuredUnpaidMass']), gap)
    assert report['independentFloorProved'] is False
    assert report['newZeroExclusion'] is False
    for row in report['sourceCalibration']:
        n, k = row['N'], 13 * row['N'] // 32
        # For these larger orders the stored length approximation has the
        # separate exponentially tiny floor error; it is not exact D_N.
        if n <= 4096:
            d = 20000**n // ((n + 1) * 10001**n)
            length = 2 * mp.log(d + 2)
            close(mp.mpf(row['movingLengthFloorErrorBound']), 0)
        else:
            log_d = -n * mp.log(u) - mp.log(n + 1)
            length = 2 * log_d
            close(mp.mpf(row['movingLengthFloorErrorBound']), 4 * mp.exp(-log_d))
        h = lambda j: mp.digamma(j + 1) + mp.euler
        # Split the two negative ORIGINAL slots independently.
        central = h(n - k) - h(k)
        successor = (n + 1) / (u * length) * (h(n + 1 - k) - h(k))
        prefix = (n + 1) / (u * length) * (h(n + 1) - h(n + 1 - k))
        positive, negative = 1 + central, successor + prefix
        close(mp.mpf(row['positiveJoinedCoefficientMass']), positive)
        close(mp.mpf(row['negativeJoinedCoefficientMass']), negative)
        close(mp.mpf(row['signedPureSelectedValue']), positive - negative)
        price = (2 * u)**(n + 1) * (positive + 2 * u * negative)
        close(mp.mpf(row['referenceAbsolutePrice']), price)
        epsilon = mp.mpf(row['referencePhaseErrorBudget'])
        close(price * (2 * epsilon + epsilon**2), gap / 4)
        samples = 4 * mp.log(80 * (n + 2)) / epsilon**2
        close(mp.mpf(row['sufficientIidSamplesLog10']), mp.log10(samples))
        assert row['sufficientIidSamplesIsNecessaryLowerBound'] is False
        assert row['iidModelAppliedToPrimeCaches'] is False
        assert row['actualRetainedPrimeCarrierBounded'] is False
        if 'syntheticSourceSensitivityRegression' in row:
            test = row['syntheticSourceSensitivityRegression']
            assert mp.mpf(test['belowTargetValue']) < target < mp.mpf(test['aboveTargetValue'])
            assert test['actualPrimeArraysOrZeroHypothesesUsed'] is False
    cache = report['actualFrozenCoverage']
    primes, rows, pairs = set(), [], 0
    for pin in cache['frozenInputs']:
        data = Path(pin['path']).read_bytes()
        assert hashlib.sha256(data).hexdigest() == pin['sha256']
        for row in json.loads(data)['rows']:
            rows.append(row)
            for side in ('left', 'right'):
                assert row[side]['provedByFLINT']
                primes.update(row[side]['primes'])
            pairs += len(row['left']['primes']) * len(row['right']['primes'])
    assert len(primes) == cache['actualDistinctCachedPrimes'] == 2080
    assert len(rows) == cache['boxes'] == 50
    assert pairs == cache['sampledCartesianPairIncidences'] == 48256
    assert all(r['N'] < 65536 for r in rows)
    assert cache['boxesAtFormalOrderThreshold'] == 0
    assert cache['completePrimePopulationCovered'] is False
    # Integer powers compare directly, independently of the producer's logs.
    all_primes = list(map(int, primes))
    for label, power in [('10^10000', 10000), ('10^20000', 20000)]:
        assert all(p < 10**power for p in all_primes)
        regime = next(row for row in cache['heightRegimes'] if row['height'] == label)
        assert regime['boxesWithHeightLargerThanEverySampledPrime'] == 50
    count, error = finite_prime_replay()
    return {
        'classification': 'Independent detector calibration replay, not a bound on the arithmetic target',
        'scalarCalibrationRows': len(report['sourceCalibration']),
        'finitePrimeFourSlotRegressions': count,
        'finitePrimeReplayMaximumError': mp.nstr(error, 20),
        'cachedDistinctPrimeCoverageReplayed': len(primes),
        'actualPrimePopulationErrorEstimated': False,
        'independentFloorProved': False, 'newZeroExclusion': False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = replay(json.loads(args.input.read_text()))
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()

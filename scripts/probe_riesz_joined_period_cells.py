#!/usr/bin/env python3
"""Optional complete-cofactor/full-period audit, outside ordinary CI.

All squarefree composite cofactors in the integer interval are factored.
The rounded native length, full original allocation, both parity signs,
all observed counts and actual complex phase are retained. These finite
orders do NOT instantiate the native many-bin/dyadic support or funding
witness. Floats and the large fixed-prime tests are not certificates.
"""

import argparse
from collections import Counter
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import mpmath as mp
import numpy as np
import sympy as sp
from scipy.special import gammaln

from probe_riesz_inner_hinge_transport import native_parameters
from probe_riesz_open_count_capacity import factor_cell, original_weights


def scan(order, heights):
    upper, length = native_parameters(order)
    base = int(mp.exp(length + mp.mpf('0.3') - mp.mpf('1.1') * order))
    owner = int(sp.nextprime(int(mp.exp(length - mp.log(base) + mp.mpf('0.06')))))
    second = int(sp.nextprime(int(mp.exp(2 * order - length - mp.mpf('0.06')))))
    origin = mp.log(owner) + mp.log(second) + mp.log(base)
    cuts = {}
    for y in heights:
        period = 2 * mp.pi / y
        start_shift = (mp.ceil(y * origin / (2 * mp.pi)) * period) - origin
        periods = int(mp.floor((mp.mpf('0.61') - start_shift) / period))
        assert periods >= 3
        shifts = [start_shift + k * period for k in range(periods + 1)]
        cuts[y] = [int(mp.ceil(base * mp.exp(t))) for t in shifts]
    start = min(c[0] for c in cuts.values())
    end = max(c[-1] for c in cuts.values())
    rows = factor_cell(start, end - start)
    assert rows and second < owner < upper
    values = np.array([b for b, _, _ in rows], dtype=np.int64)
    total_logs = float(origin) + np.log1p((values - base) / base)
    tau = float(mp.log(owner) + mp.log(base) - length) + np.log1p((values - base) / base)
    signs = np.array([mu for _, _, mu in rows])
    min_logs = np.array([math.log(factors[0]) for _, factors, _ in rows])
    assert np.all(tau >= 0) and np.all(tau <= min_logs)
    assert np.all(1.95 * order < total_logs) and np.all(total_logs <= 2.03 * order)
    assert np.all(float(mp.log(owner)) / total_logs < .60069)
    assert float(mp.log(second)) + math.log(end) <= float(length)
    assert math.log(end) <= float(mp.log(owner) + mp.log(second) - length) + math.log(start)
    assert all(b < second and max(factors) < upper and math.prod(factors) == b
               for b, factors, _ in rows)
    full_weight, _ = original_weights(order, owner, second, upper, rows, total_logs)
    log_amplitude = ((order + 1) * np.log(total_logs) - 1.5 * total_logs +
                     (order + 1) * float(mp.log(mp.mpf(10001) / 20000)) -
                     float(mp.log(length)) - gammaln(order + 1))
    amplitude = full_weight * tau * np.exp(log_amplitude)
    result = []
    for y, endpoints in cuts.items():
        phase_origin = complex(mp.exp(-1j * y * origin))
        atoms = signs * amplitude * phase_origin * np.exp(-1j * y * np.log1p((values - base) / base))
        periods = []
        for a, b in zip(endpoints, endpoints[1:]):
            index = (a <= values) & (values < b)
            current = atoms[index]
            original_indices = np.flatnonzero(index)
            total = complex(np.sum(current))
            absolute = float(np.sum(np.abs(current)))
            counts = Counter(len(rows[i][1]) + 2 for i in original_indices)
            negative = int(np.count_nonzero(current.real < 0))
            favorable = int(len(current) - negative)
            periods.append({
                'integerInterval': [int(a), int(b)],
                'squarefreeCompositeLabels': int(len(current)),
                'countHistogram': dict(sorted(counts.items())),
                'parityImbalance': int(np.sum(signs[index])),
                'negativeLabels': negative, 'favorableLabels': favorable,
                'signedSourceReal': total.real, 'signedSourceImag': total.imag,
                'absoluteSourceMass': absolute,
                'signedToAbsoluteRatio': abs(total) / absolute,
            })
        totals = [complex(p['signedSourceReal'], p['signedSourceImag']) for p in periods]
        joint = sum(totals, 0j)
        diagonal = math.fsum(abs(z)**2 for z in totals)
        all_abs = math.fsum(p['absoluteSourceMass'] for p in periods)
        result.append({
            'height': y, 'completePeriods': len(periods), 'periods': periods,
            'jointSignedSourceReal': joint.real, 'jointSignedSourceImag': joint.imag,
            'jointSignedToAbsoluteRatio': abs(joint) / all_abs,
            'jointEnergyOverPeriodDiagonal': abs(joint)**2 / diagonal,
            'signedOffDiagonalEnergy': abs(joint)**2 - diagonal,
            'noPeriodWasClippedBeforeJoining': True,
        })
    return {
        'order': order, 'integerLabelsFactored': end - start,
        'squarefreeCompositeLabels': len(rows),
        'nativeEventualLengthLowerBoundMet': bool(length >= mp.mpf(11) * order / 8),
        'nativeManyBinPopulation': False,
        'occupiedAboveHeadBins': 0,
        'fixedPrimeTests': 'Sympy probable-prime tests; no Lean certificates.',
        'physicalEligibilityAndInnerHingeCheckedNumerically': True,
        'fullOriginalAllocationAndPhaseRetained': True,
        'evaluations': result,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[64, 80])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    mp.mp.dps = 100
    report = {
        'diagnosticOnly': True,
        'scope': 'Complete finite integer-cofactor cells spanning consecutive full total-log phase periods; all observed counts joined.',
        'tests': [scan(n, (54, 65, 100)) for n in args.orders],
        'nativeManyBinEstimateProved': False,
        'originalFundingWitnessCertified': False,
        'sourceScaleAsymptoticBoundCertified': False,
        'floorCertified': False,
    }
    rendered = json.dumps(report, indent=2, allow_nan=False)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered + '\n')
    print(rendered)


if __name__ == '__main__':
    main()

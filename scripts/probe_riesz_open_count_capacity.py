#!/usr/bin/env python3
"""Optional complete integer-cofactor cell capacity audit.

Retains all squarefree composite cofactors, exact rounded L_N, actual prime
factorisations, full product phase and full original factorial allocation.
Finite orders do not instantiate the native dyadic/many-bin or eventual
length hypotheses. Numeric values are diagnostics, not interval certificates.
"""

import argparse
from collections import Counter
import itertools
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import mpmath as mp
import numpy as np
from scipy.special import bdtr, gammaln
import sympy as sp
from probe_riesz_inner_hinge_transport import native_parameters, unpaid_orders


def factor_cell(start, width):
    values = list(range(start, start + width))
    remaining = values.copy()
    factors = [[] for _ in values]
    mu = [1 for _ in values]
    for prime in sp.primerange(2, math.isqrt(values[-1]) + 1):
        prime = int(prime)
        for i in range((-start) % prime, width, prime):
            factors[i].append(prime)
            remaining[i] //= prime
            mu[i] *= -1
            if remaining[i] % prime == 0:
                mu[i] = 0
                while remaining[i] % prime == 0:
                    remaining[i] //= prime
    for i, rest in enumerate(remaining):
        if rest > 1:
            factors[i].append(rest)
            mu[i] *= -1
    return [(b, factors[i], mu[i]) for i, b in enumerate(values)
            if mu[i] != 0 and len(factors[i]) >= 2]


def original_weights(order, owner, second, upper, rows, total_logs):
    orders = unpaid_orders(order)
    assert orders == list(range(order // 5 + 2, 13 * order // 32 + 1))
    lo, hi = orders[0], orders[-1]
    allocated = np.zeros(len(rows))
    owner_allocated = None
    for fixed in (owner, second):
        x = 1 - float(mp.log(fixed)) / total_logs
        part = bdtr(hi, order + 1, x) - bdtr(lo - 1, order + 1, x)
        if fixed == owner:
            owner_allocated = part
        allocated += part
    for i, (_, factors, _) in enumerate(rows):
        for prime in factors:
            if order ** 2 < prime < upper:
                x = 1 - math.log(prime) / total_logs[i]
                allocated[i] += bdtr(hi, order + 1, x) - bdtr(lo - 1, order + 1, x)
    assert np.all(allocated >= -1e-13) and np.all(allocated <= 1 + 1e-13)
    return 1 - allocated, 1 - owner_allocated


def evaluation(order, length, owner, second, upper, rows, height):
    first = rows[0][0]
    relative_logs = np.array([float(mp.log(mp.mpf(b) / first)) for b, _, _ in rows])
    centre = mp.log(owner) + mp.log(second) + mp.log(first)
    total_logs = float(centre) + relative_logs
    tau = float(mp.log(owner) + mp.log(first) - length) + relative_logs
    signs = np.array([mu for _, _, mu in rows])
    full_weights, owner_weights = original_weights(order, owner, second, upper, rows, total_logs)
    u = mp.mpf(10001) / 20000
    log_amplitude = ((order + 1) * np.log(total_logs) - 1.5 * total_logs +
                     (order + 1) * float(mp.log(u)) - float(mp.log(length)) -
                     gammaln(order + 1))
    amplitude = tau * np.exp(log_amplitude)
    phase_origin = complex(mp.exp(-1j * height * centre))
    # This is the FULL phase; the centre is not frozen or replaced by1.
    raw = signs * amplitude * phase_origin * np.exp(-1j * height * relative_logs)
    atoms = full_weights * raw
    owner_atoms = owner_weights * raw
    negative = [i for i, value in enumerate(atoms) if value.real < 0]
    favorable = [i for i, value in enumerate(atoms) if value.real >= 0]
    candidates = {sign: [i for i in favorable if signs[i] == sign] for sign in (-1, 1)}
    cursor = {-1: 0, 1: 0}
    pairs = []
    matched = set()
    for i in negative:
        pool = candidates[-signs[i]]
        offset = cursor[-signs[i]]
        if offset < len(pool):
            j = pool[offset]
            cursor[-signs[i]] += 1
            assert rows[i][0] != rows[j][0]
            assert i not in matched and j not in matched
            matched.update((i, j))
            pairs.append((i, j))
    unmatched = [i for i in range(len(rows)) if i not in matched]
    pair_cost = math.fsum(abs(atoms[i] + atoms[j]) for i, j in pairs)
    full_sum = complex(np.sum(atoms))
    unmatched_sum = complex(np.sum(atoms[unmatched]))
    pair_sum = sum((atoms[i] + atoms[j] for i, j in pairs), 0j)
    absolute = math.fsum(abs(z) for z in atoms)
    assert abs(full_sum - unmatched_sum - pair_sum) <= 5e-13 * absolute
    max_gap = max((float(abs(mp.log(mp.mpf(rows[i][0]) / rows[j][0])))
                   for i, j in pairs), default=0)
    assert max_gap <= float(mp.exp(-mp.mpf(order) / 1000))
    higher_negative = [i for i in negative if len(rows[i][1]) >= 3]
    higher_positive = [i for i in favorable if len(rows[i][1]) >= 3]
    count_four_used = sum(len(rows[i][1]) == 2 or len(rows[j][1]) == 2 for i, j in pairs)
    return {
        'height': height, 'negativeLabels': len(negative),
        'favorableLabels': len(favorable), 'oppositeParityPairs': len(pairs),
        'negativeLabelsRemaining': int(sum(atoms[i].real < 0 for i in unmatched)),
        'countFourPartnerPairs': count_four_used,
        'withoutCountFourNegativeLabels': len(higher_negative),
        'withoutCountFourFavorableLabels': len(higher_positive),
        'maxActualLogGap': max_gap,
        'sourceScaledOriginalSignedReal': full_sum.real,
        'sourceScaledOriginalUnmatchedReal': unmatched_sum.real,
        'sourceScaledJoinedPairNormCost': pair_cost,
        'sourceScaledOriginalAbsoluteMass': absolute,
        'signedToAbsoluteRatio': abs(full_sum) / absolute if absolute else None,
        'maxFullVsOwnerAllocationDifference': float(np.max(abs(full_weights-owner_weights))),
        'exactIntegerLabelsDeduplicated': True, 'fullPhaseRetained': True,
        'originalFullAllocationRetained': True,
    }


def case(order, cell_offset):
    upper, length = native_parameters(order)
    centre_b = int(mp.exp(length + mp.mpf('0.3') - mp.mpf('1.1') * order))
    width = max(2, min(4096, centre_b // 1000))
    start = centre_b + cell_offset * width
    owner = int(sp.nextprime(int(mp.exp(length - mp.log(start) + mp.mpf('0.3')))))
    second = int(sp.nextprime(int(mp.exp(2 * order - length - mp.mpf('0.3')))))
    rows = factor_cell(start, width)
    assert rows
    assert second < owner < upper
    for b, factors, _ in rows:
        assert b < second and all(prime < upper for prime in factors)
        assert math.prod(factors) == b and len(set(factors)) == len(factors)
        T = mp.log(owner) + mp.log(second) + mp.log(b)
        tau = mp.log(owner) + mp.log(b) - length
        assert mp.log(second) + mp.log(b) <= length
        assert mp.log(b) <= T - length
        assert 0 <= tau <= mp.log(min(factors))
        assert mp.mpf('1.95') * order < T <= mp.mpf('2.03') * order
        assert mp.log(owner) < mp.mpf('0.60069') * T
    hist = Counter(len(factors) + 2 for _, factors, _ in rows)
    return {
        'order': order, 'cellOffset': cell_offset,
        'firstCofactor': str(start), 'integerCellWidth': width,
        'squarefreeCompositeLabels': len(rows),
        'fullPrimeCountHistogram': dict(sorted(hist.items())),
        'signedCofactorParityImbalance': sum(mu for _, _, mu in rows),
        'countFourLabelsIncluded': hist.get(4, 0),
        'allLiteralInnerHingeConditionsCheckedNumerically': True,
        'nativeEventualLengthLowerBoundMet': length >= mp.mpf(11) * order / 8,
        'evaluations': [evaluation(order, length, owner, second, upper, rows, height)
                        for height in (54, 65, 100)],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    mp.mp.dps = 100
    report = {
        'scope': 'All squarefree composite cofactor integers in complete finite cells, with both parity signs and all actual prime counts retained.',
        'cases': [case(order, offset) for order, offset in
                  itertools.product((64, 96, 128), (0, 2, 7))],
        'primeCountClassesStoppedNumerically': False,
        'nativeDyadicSupportCertified': False,
        'nativeCount56ManyBinPopulationEvaluated': False,
        'originalFundingWitnessCertified': False,
        'floatingResultsIntervalCertified': False,
        'allCofactorConfigurationsCoveredAsymptotically': False,
        'floorCertified': False,
        'actualPrimeTests': 'Deterministic for the segmented integer cofactors; Sympy probable-prime tests for large fixed owner primes. No Lean prime certificates.',
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()

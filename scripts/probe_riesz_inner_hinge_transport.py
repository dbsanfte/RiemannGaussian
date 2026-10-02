#!/usr/bin/env python3
"""Optional literal prime-replacement regression on the inner Riesz hinge.

Uses actual integer labels, the rounded native L_N, original finite prime
eligibility, exact unpaid factorial orders, boundedShare and full complex
phase. These finite pairs are NOT the unpaid count56+ many-bin population;
there is no original dyadic schedule or funding witness in the experiment.
Finite prime tests and floating evaluations are diagnostics, not Lean
certificates, asymptotic matching coverage or a whole-carrier floor.
"""

import argparse
import itertools
import json
import math
from pathlib import Path

import mpmath as mp
import sympy as sp


def number_string(value):
    return mp.nstr(value, 30)


def native_parameters(order):
    # u=10001/20000; this rounding is EXACT integer arithmetic.
    cutoff = (20000 ** order) // ((10001 ** order) * (order + 1))
    upper = (cutoff + 2) ** 2
    return upper, mp.log(upper)


def unpaid_orders(order):
    total = order + 1
    result = []
    for k in range(total + 1):
        lower = total < 8 * k < 7 * total and 32 * k <= 15 * order + 64
        reserve = 13 * order // 32 + 1 <= k <= (15 * order + 64) // 32
        high = 4 * order <= 5 * (total - k)
        if lower and not reserve and not high:
            result.append(k)
    return result


def allocation(order, primes, upper):
    total_log = mp.fsum(mp.log(p) for p in primes)
    mass = mp.mpf(0)
    for p in primes:
        if order ** 2 < p < upper:
            x = 1 - mp.log(p) / total_log
            mass += mp.fsum(mp.binomial(order + 1, k) * x ** k *
                            (1 - x) ** (order + 1 - k)
                            for k in unpaid_orders(order))
    assert 0 <= mass <= 1
    return mass


def riesz(length, primes):
    # Complete divisor enumeration; all subset signs and endpoints retained.
    logs = [mp.log(p) for p in primes]
    value = mp.mpf(0)
    for bits in itertools.product((0, 1), repeat=len(logs)):
        x = length - mp.fsum(a for a, included in zip(logs, bits) if included)
        if x > 0:
            value += (-1) ** sum(bits) * x
    return value


def atom(order, length, height, primes, upper):
    total_log = mp.fsum(mp.log(p) for p in primes)
    fraction = allocation(order, primes, upper)
    weight = ((1 - fraction) * total_log / length * total_log ** order /
              mp.factorial(order) * mp.exp(-(mp.mpf(3) / 2 + 1j * height) * total_log))
    return -riesz(length, primes) * weight, weight, fraction


def setup(order, count):
    upper, length = native_parameters(order)
    tau = mp.mpf(3) / 10
    target_b = length + tau - mp.mpf(11) / 20 * 2 * order
    candidate = max(5, int(mp.exp(target_b / count)))
    small = []
    while len(small) < count:
        candidate = int(sp.nextprime(candidate))
        small.append(candidate)
    log_b = mp.fsum(mp.log(r) for r in small)
    owner = int(sp.nextprime(int(mp.exp(length - log_b + tau))))
    second = int(sp.nextprime(int(mp.exp(2 * order - length - tau))))
    assert owner > second > max(small)
    return upper, length, owner, second, small


def inner_conditions(length, owner, second, small):
    b_log = mp.fsum(mp.log(r) for r in small)
    total_log = mp.log(owner) + mp.log(second) + b_log
    tau = mp.log(owner) + b_log - length
    assert mp.log(second) + b_log <= length
    assert b_log <= total_log - length
    assert 0 <= tau <= mp.log(min(small))
    return tau, total_log


def experiment(order, count, heights):
    upper, length, owner, second, small = setup(order, count)
    tau, log_n = inner_conditions(length, owner, second, small)
    rows = []
    for inserted in (2, 3, 5, 7):
        if inserted >= min(small):
            continue
        partner = int(sp.nextprime(owner // inserted))
        extended = [inserted, *small]
        tau_partner, log_partner = inner_conditions(length, partner, second, extended)
        assert partner > second > max(extended)
        gap = mp.log(partner * inserted) - mp.log(owner)
        assert abs(log_partner - log_n - gap) < mp.mpf('1e-100')
        assert mp.mpf('1.95') * order < min(log_n, log_partner)
        assert max(log_n, log_partner) <= mp.mpf('2.03') * order
        assert max(mp.log(owner) / log_n, mp.log(partner) / log_partner) < mp.mpf('0.60069')
        primes = [owner, second, *small]
        partner_primes = [partner, second, *extended]
        assert len(set(primes)) == len(primes)
        assert len(set(partner_primes)) == len(partner_primes)
        assert all(p < upper for p in primes + partner_primes)
        for height in heights:
            original, weight, share = atom(order, length, height, primes, upper)
            other, other_weight, other_share = atom(order, length, height, partner_primes, upper)
            for v, other_v in ((mp.mpf(1), mp.mpf(1)), (mp.mpf(1), -mp.mpf(1) / 10)):
                full = v * original + other_v * other
                joint = (-1) ** count * (v * tau * weight - other_v * tau_partner * other_weight)
                envelope = abs(v * original) + abs(other_v * other)
                assert abs(full - joint) / envelope < mp.mpf('1e-90')
                mismatch = (abs(tau - tau_partner) * abs(v * weight) +
                            abs(tau_partner) * abs(v * weight - other_v * other_weight))
                assert abs(full) <= mismatch + envelope * mp.mpf('1e-90')
                rows.append({
                    'order': order, 'counts': [len(primes), len(partner_primes)],
                    'height': height, 'signedMultipliers': [number_string(v), number_string(other_v)],
                    'length': number_string(length), 'tau': number_string(tau),
                    'ownerPrime': str(owner), 'replacementPrime': str(partner),
                    'insertedPrime': inserted, 'secondPrime': str(second),
                    'cofactorPrimes': small, 'totalLogGap': number_string(gap),
                    'boundedShares': [number_string(share), number_string(other_share)],
                    'pairToSeparateNormRatio': number_string(abs(full) / envelope),
                    'countFreeMismatchToSeparateNormRatio': number_string(mismatch / envelope),
                    'relativeIdentityError': number_string(abs(full - joint) / envelope),
                    'sourceScaledRealPair': number_string((mp.mpf(10001) / 20000) ** (order + 1) * full.real),
                })
    return rows


def owner_cell_capacity(order, count, width):
    _, _, owner, _, small = setup(order, count)
    end = owner + width
    negative = list(sp.primerange(owner, end + 1))
    incidences = []
    for inserted in sp.primerange(2, min(min(small), 44)):
        candidates = [int(p) for p in sp.primerange((owner + inserted - 1) // inserted,
                                                   end // inserted + 1)]
        incidences.extend((inserted * p, int(inserted), p) for p in candidates)
    assert len({(r, p) for _, r, p in incidences}) == len(incidences)
    # Every new least prime is smaller than every base-cofactor prime;
    # its deletion recovers that exact base. No count class is averaged.
    matched_count = min(len(negative), len(incidences))
    return {
        'order': order, 'originalCount': count + 2, 'insertedCount': count + 3,
        'integerOwnerCellWidth': width, 'originalPrimeCount': len(negative),
        'distinctOppositeParityLabels': len(incidences),
        'finiteCellCoverageFraction': matched_count / len(negative),
        'maxTotalLogGapInCell': number_string(mp.log(mp.mpf(end) / owner)),
        'completeCellMatchingExistsNumerically': len(incidences) >= len(negative),
        'literalUnpaidSupportCertified': False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--precision', type=int, default=120)
    args = parser.parse_args()
    if args.precision < 120:
        parser.error('at least120 digits are required for cancellation checks')
    mp.mp.dps = args.precision
    rows = []
    for order, count in ((32, 2), (64, 4), (128, 6), (256, 8), (512, 10)):
        rows.extend(experiment(order, count, (54, 65, 100)))
    cells = [owner_cell_capacity(32, 2, 8192), owner_cell_capacity(64, 4, 8192)]
    equal_weights = [mp.mpf(row['pairToSeparateNormRatio']) for row in rows
                     if row['signedMultipliers'] == ['1.0', '1.0']]
    reversed_weights = [mp.mpf(row['pairToSeparateNormRatio']) for row in rows
                        if row['signedMultipliers'] == ['1.0', '-0.1']]
    report = {
        'scope': 'Finite literal integer inner-hinge pairs with native moving length and allocation; not the unpaid count56+ many-bin funded carrier.',
        'precisionDigits': args.precision, 'pairCases': rows, 'finiteOwnerCells': cells,
        'nativeMovingLengthRetained': True, 'exactUnpaidFactorialOrdersRetained': True,
        'allocationPrimeEligibilityRetained': True, 'allPrimeCountSubsetsRetainedInRiesz': True,
        'fullComplexPhaseRetained': True,
        'actualPrimeTests': 'Sympy deterministic below2^64 and probable-prime tests above it; not kernel certificates.',
        'equalWeightRatioRange': [number_string(min(equal_weights)), number_string(max(equal_weights))],
        'differentSignedWeightRatioRange': [number_string(min(reversed_weights)), number_string(max(reversed_weights))],
        'nativeCount56ManyBinPopulationEvaluated': False,
        'oldFixedParityPacketRoughPrimeMaskSatisfied': False,
        'nativeCoreMembershipCertified': False,
        'fundingWitnessIncluded': False,
        'sourceScaleMatchingCostCertified': False, 'floorCertified': False,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: report[key] for key in ('scope', 'equalWeightRatioRange',
                                                 'differentSignedWeightRatioRange',
                                                 'finiteOwnerCells', 'floorCertified')}, indent=2))


if __name__ == '__main__':
    main()

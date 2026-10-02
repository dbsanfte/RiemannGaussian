#!/usr/bin/env python3
"""Optional literal disjoint-pair cost and finite partner-capacity regression.

The moving cutoff, actual squarefree integer labels, full phase and original
factorial allocation are retained. Frozen-cofactor cells are deliberately
small diagnostics; they are not native count56+ many-bin coverage, original
funding witnesses, prime-interval theorems or floor certificates.
"""

import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import mpmath as mp
import sympy as sp
from probe_riesz_inner_hinge_transport import (
    allocation, inner_conditions, native_parameters, number_string, setup,
)


def raw_atom(order, length, height, owner, second, small):
    """Use the proved inner-hinge coefficient, with its exact parity sign."""
    tau, total_log = inner_conditions(length, owner, second, small)
    return ((-1) ** len(small) * tau * total_log ** (order + 1) /
            (length * mp.factorial(order)) *
            mp.exp(-(mp.mpf(3) / 2 + 1j * height) * total_log))


def interval_case(order, count, width, height):
    upper, length, owner, second, small = setup(order, count)
    end = owner + width
    base = sorted(int(p) for p in sp.primerange(owner, end + 1))
    inserted_primes = list(sp.primerange(2, min(min(small), 44)))
    candidates = []
    capacities = {}
    for inserted in inserted_primes:
        partners = [int(p) for p in sp.primerange((owner + inserted - 1) // inserted,
                                                 end // inserted + 1)]
        partners = [p for p in partners if p > second and p not in small]
        capacities[str(inserted)] = len(partners)
        candidates.extend((inserted * p, int(inserted), p) for p in partners)
    candidates.sort()
    b = int(sp.prod(small))
    negative = [p for p in base if raw_atom(order, length, height, p, second, small).real <= 0]
    matched = list(zip(negative, candidates))
    vertices = set()
    raw_cost = mp.mpf(0)
    original_pair_sum = mp.mpc(0)
    signed_unmatched = mp.mpc(0)
    used = set()
    max_gap = mp.mpf(0)
    max_local_ratio = mp.mpf(0)
    for p, (product, inserted, partner) in matched:
        n, other_n = p * second * b, partner * second * inserted * b
        assert n != other_n and n not in vertices and other_n not in vertices
        vertices.update((n, other_n))
        used.add(p)
        primes = [p, second, *small]
        other_primes = [partner, second, inserted, *small]
        assert len(set(primes)) == len(primes)
        assert len(set(other_primes)) == len(other_primes)
        assert all(z < upper for z in primes + other_primes)
        F = raw_atom(order, length, height, p, second, small)
        G = raw_atom(order, length, height, partner, second, [inserted, *small])
        gap = abs(mp.log(mp.mpf(product) / p))
        # Exact log ratio, never subtraction of two large rounded logs.
        assert gap <= mp.exp(-mp.mpf(order) / 1000)
        assert gap >= 1 / mp.mpf(max(p, product))
        assert mp.log(max(p, product)) >= mp.mpf(order) / 1000
        radial_cap = (order + 1) * mp.mpf(2) ** (order + 1)
        local_price = 21 * (1 + abs(height)) * (order + 1) * radial_cap / n * gap
        assert abs(F + G) <= local_price * (1 + mp.mpf('1e-90'))
        raw_cost += abs(F + G)
        max_gap = max(max_gap, gap)
        if local_price:
            max_local_ratio = max(max_local_ratio, abs(F + G) / local_price)
        weight = 1 - allocation(order, primes, upper)
        other_weight = 1 - allocation(order, other_primes, upper)
        original_pair_sum += weight * F + other_weight * G
    for p in base:
        if p not in used:
            F = raw_atom(order, length, height, p, second, small)
            signed_unmatched += (1 - allocation(order, [p, second, *small], upper)) * F
    u = mp.mpf(10001) / 20000
    global_price = (168 * u * (1 + abs(height)) * (order + 1) ** 3 *
                    mp.exp(-mp.mpf(order) / 1250))
    scaled_cost = u ** (order + 1) * raw_cost
    assert scaled_cost <= global_price
    return {
        'order': order, 'baseCount': count + 2, 'partnerCount': count + 3,
        'height': number_string(height), 'integerCellWidth': width,
        'basePrimeLabels': len(base), 'negativeFirstLabels': len(negative),
        'partnerLabels': len(candidates), 'partnersByInsertedPrime': capacities,
        'disjointMatchedPairs': len(matched),
        'negativeFirstCoverage': len(matched) / len(negative) if negative else None,
        'allBaseCoverage': len(matched) / len(base) if base else None,
        'maxActualLogGap': number_string(max_gap),
        'requiredGapCeiling': number_string(mp.exp(-mp.mpf(order) / 1000)),
        'maxRawCostOverLocalBound': number_string(max_local_ratio),
        'totalSourceScaledRawPairCost': number_string(scaled_cost),
        'globalConditionalPrice': number_string(global_price),
        'sourceScaledOriginalAllocatedPairReal': number_string(
            u ** (order + 1) * original_pair_sum.real),
        'sourceScaledOriginalUnmatchedReal': number_string(
            u ** (order + 1) * signed_unmatched.real),
        'oneInsertedPrimeProvidesFullCapacity': any(
            value >= len(negative) for value in capacities.values()) if negative else None,
        'matchingVerticesDisjoint': True,
        'fundingMultipliers': [1, 1],
        'originalFundedPopulationMembershipCertified': False,
        'nativeManyBinPopulationCertified': False,
    }


def cofactor_split_case(order, width=2048, insertion_ceiling=2000):
    """Split a large cofactor prime; keep the owner and second prime fixed.

    The original cofactor contains2,3,5,7,11. An inserted prime need not be
    smaller than its least prime. Ordered matching retains increasing total
    log and hence increasing owner-cofactor share.
    """
    upper, length = native_parameters(order)
    common = [2, 3, 5, 7, 11]
    common_log = mp.fsum(mp.log(p) for p in common)
    target_b = length + mp.mpf('0.3') - mp.mpf('1.1') * order
    start = int(sp.nextprime(int(mp.exp(target_b - common_log))))
    end = start + width
    owner = int(sp.nextprime(int(mp.exp(length - common_log - mp.log(start) + mp.mpf('0.3')))))
    second = int(sp.nextprime(int(mp.exp(2 * order - length - mp.mpf('0.3')))))
    assert owner > second > end
    base = [int(v) for v in sp.primerange(start, end + 1)]
    height = next(mp.mpf(k) / 4 for k in range(216, 280)
                  if raw_atom(order, length, mp.mpf(k) / 4,
                              owner, second, [*common, start]).real < 0)
    candidates = []
    for inserted in sp.primerange(2, insertion_ceiling + 1):
        if inserted in common:
            continue
        for replacement in sp.primerange((start + inserted - 1) // inserted,
                                           end // inserted + 1):
            replacement = int(replacement)
            if replacement not in common and replacement != inserted:
                candidates.append((int(inserted) * replacement, int(inserted), replacement))
    candidates = sorted(set(candidates))
    # A candidate integer is counted once even if both legs lie in the
    # insertion universe. This is actual label capacity, not incidence count.
    unique = {}
    for candidate in candidates:
        unique.setdefault(candidate[0], candidate)
    candidates = sorted(unique.values())
    cursor = 0
    matched = []
    for v in base:
        while cursor < len(candidates) and candidates[cursor][0] < v:
            cursor += 1
        if cursor < len(candidates):
            matched.append((v, candidates[cursor]))
            cursor += 1
    raw_cost = mp.mpf(0)
    allocated_real = mp.mpf(0)
    unmatched_real = mp.mpf(0)
    max_gap = mp.mpf(0)
    vertices = set()
    used_base = set()
    common_integer = int(sp.prod(common))
    for v, (product, inserted, replacement) in matched:
        first_small = [*common, v]
        second_small = [*common, inserted, replacement]
        n = owner * second * common_integer * v
        other_n = owner * second * common_integer * product
        assert n != other_n and n not in vertices and other_n not in vertices
        assert len(set([owner, second, *first_small])) == len(first_small) + 2
        assert len(set([owner, second, *second_small])) == len(second_small) + 2
        assert all(p < upper for p in [owner, second, *first_small, *second_small])
        total_log = mp.log(n)
        other_log = mp.log(other_n)
        assert mp.mpf('1.95') * order < min(total_log, other_log)
        assert max(total_log, other_log) <= mp.mpf('2.03') * order
        assert 1 - mp.log(owner) / total_log >= mp.mpf(3) / 8
        assert mp.log(owner) / total_log < mp.mpf('0.60069')
        vertices.update((n, other_n))
        used_base.add(v)
        F = raw_atom(order, length, height, owner, second, first_small)
        G = raw_atom(order, length, height, owner, second, second_small)
        assert F.real < 0 and product >= v
        gap = mp.log(mp.mpf(product) / v)
        assert gap <= mp.exp(-mp.mpf(order) / 1000)
        assert gap >= 1 / mp.mpf(product)
        assert mp.log(product) >= mp.mpf(order) / 1000
        radial_cap = (order + 1) * mp.mpf(2) ** (order + 1)
        local_price = 21 * (1 + height) * (order + 1) * radial_cap / n * gap
        assert abs(F + G) <= local_price * (1 + mp.mpf('1e-90'))
        raw_cost += abs(F + G)
        max_gap = max(max_gap, gap)
        weight = 1 - allocation(order, [owner, second, *first_small], upper)
        other_weight = 1 - allocation(order, [owner, second, *second_small], upper)
        allocated_real += (weight * F + other_weight * G).real
    for v in base:
        if v not in used_base:
            first_small = [*common, v]
            F = raw_atom(order, length, height, owner, second, first_small)
            weight = 1 - allocation(order, [owner, second, *first_small], upper)
            unmatched_real += (weight * F).real
    u = mp.mpf(10001) / 20000
    global_price = 168 * u * (1 + height) * (order + 1) ** 3 * mp.exp(-mp.mpf(order) / 1250)
    scaled_cost = u ** (order + 1) * raw_cost
    assert scaled_cost <= global_price
    return {
        'order': order, 'height': number_string(height),
        'counts': [len(common) + 3, len(common) + 4],
        'commonPrimes': common, 'originalLeastPrime': 2,
        'ownerHeldFixed': True, 'secondPrimeHeldFixed': True,
        'cofactorPrimeCellWidth': width, 'insertionPrimeCeiling': insertion_ceiling,
        'originalPrimeLabels': len(base), 'distinctSemiprimePartnerLabels': len(candidates),
        'disjointMatchedPairs': len(matched),
        'coverageFraction': len(matched) / len(base) if base else None,
        'ownerCofactorShareOrderedInEveryPair': True,
        'maxActualLogGap': number_string(max_gap),
        'sourceScaledRawMismatchCost': number_string(scaled_cost),
        'sourceScaledOriginalAllocatedPairReal': number_string(u ** (order + 1) * allocated_real),
        'sourceScaledOriginalUnmatchedReal': number_string(u ** (order + 1) * unmatched_real),
        'nativeManyBinMembershipCertified': False,
        'originalFundedPopulationMembershipCertified': False,
        'allCofactorCollisionBudgetCertified': False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    mp.mp.dps = 160
    rows = []
    for order, count in ((32, 2), (64, 4)):
        _, length, owner, second, small = setup(order, count)
        # Include one explicit negative-first cell in each finite order,
        # alongside the fixed-height checks. This selection is diagnostic.
        negative_height = next(mp.mpf(k) / 4 for k in range(216, 280)
                               if raw_atom(order, length, mp.mpf(k) / 4,
                                           owner, second, small).real < 0)
        for height in (54, 65, 100, negative_height):
            rows.append(interval_case(order, count, 2048, height))
    report = {
        'scope': 'Finite actual disjoint inner-hinge pairs at equal funding; conditional gap-price regression and frozen-cofactor capacity diagnostic only.',
        'precisionDigits': mp.mp.dps, 'cases': rows,
        'cofactorSplitCases': [cofactor_split_case(order) for order in (128, 256)],
        'negativeHeightSelection': 'First negative base atom among quarter-integer heights54..69.75; diagnostics only, not a zeta ordinate.',
        'nativeMovingLengthRetained': True, 'fullComplexPhaseRetained': True,
        'originalAllocationRetained': True, 'actualLogGapRetained': True,
        'allComputedLocalAndGlobalPricesPassed': True,
        'actualPrimeTests': 'Sympy deterministic below2^64 and probable-prime tests above it; not Lean prime certificates.',
        'finiteNativePartnerCoverageProved': False,
        'fundingWitnessCertified': False, 'allCofactorCollisionBudgetCertified': False,
        'sourceScaleUnmatchedBoundProved': False,
        'floatingResultsIntervalCertified': False, 'floorCertified': False,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()

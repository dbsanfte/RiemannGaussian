#!/usr/bin/env python3
"""Optional unordered fixed-owner parity matching and collision diagnostic.

Retains actual distinct factorisations, rounded L_N, full phase and the
original full allocation in sampled pair evaluations. The finite counts
and equal funding are not a native count56+ many-bin funding witness.
"""

import argparse
import itertools
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import mpmath as mp
import sympy as sp
from probe_riesz_inner_gap_payment import raw_atom
from probe_riesz_inner_hinge_transport import (
    allocation, inner_conditions, native_parameters, number_string, unpaid_orders,
)


def owner_weight(order, owner, primes):
    total_log = mp.fsum(mp.log(p) for p in primes)
    x = 1 - mp.log(owner) / total_log
    mass = mp.fsum(mp.binomial(order + 1, k) * x ** k *
                   (1 - x) ** (order + 1 - k) for k in unpaid_orders(order))
    return 1 - mass, x


def actual_family(order, common, start, end, insertion_ceiling):
    common_integer = int(sp.prod(common))
    parents = {}
    for marked in sp.primerange((start + common_integer - 1) // common_integer,
                                 end // common_integer + 1):
        marked = int(marked)
        if marked not in common:
            parents[common_integer * marked] = [*common, marked]
    candidates = {}
    incidences = 0
    for inserted in sp.primerange(2, insertion_ceiling + 1):
        inserted = int(inserted)
        if inserted in common:
            continue
        divisor = common_integer * inserted
        for other in sp.primerange((start + divisor - 1) // divisor,
                                    end // divisor + 1):
            other = int(other)
            if other in common or other == inserted:
                continue
            small = sorted([*common, inserted, other])
            assert len(set(small)) == len(small)
            incidences += 1
            candidates.setdefault(common_integer * inserted * other, small)
    return parents, candidates, incidences


def test_pairs(order, upper, length, owner, second, parents, candidates, height, sample_limit):
    # The new theorem permits arbitrary orders of the two log coordinates.
    # Every pair lies in the same literal cofactor-integer cell.
    pairs = list(zip(sorted(parents), sorted(candidates)))
    assert set(parents).isdisjoint(candidates)
    sampled = pairs[:sample_limit]
    reverse_share_pairs = 0
    owner_norm_cost = mp.mpf(0)
    raw_norm_cost = mp.mpf(0)
    full_norm_cost = mp.mpf(0)
    nonowner_cost = mp.mpf(0)
    local_price = mp.mpf(0)
    max_gap = mp.mpf(0)
    vertices = set()
    for b, other_b in sampled:
        small, other_small = parents[b], candidates[other_b]
        n, other_n = owner * second * b, owner * second * other_b
        assert n != other_n and n not in vertices and other_n not in vertices
        vertices.update((n, other_n))
        primes = [owner, second, *small]
        other_primes = [owner, second, *other_small]
        assert max(small + other_small) < second < owner
        assert all(p < upper for p in primes + other_primes)
        F = raw_atom(order, length, height, owner, second, small)
        G = raw_atom(order, length, height, owner, second, other_small)
        T, U = mp.log(n), mp.log(other_n)
        gap = abs(mp.log(mp.mpf(other_b) / b))
        assert gap <= mp.exp(-mp.mpf(order) / 1000)
        assert mp.mpf('1.95') * order < min(T, U)
        assert max(T, U) <= mp.mpf('2.03') * order
        a, x = owner_weight(order, owner, primes)
        other_a, other_x = owner_weight(order, owner, other_primes)
        reverse_share_pairs += other_x < x
        assert abs(x - other_x) <= gap * (1 + mp.mpf('1e-90'))
        assert abs(a - other_a) <= 2 * (order + 1) * gap * (1 + mp.mpf('1e-90'))
        joint_owner = a * F + other_a * G
        gap_price = abs(F + G) + 2 * (order + 1) * gap * abs(G)
        assert abs(joint_owner) <= gap_price * (1 + mp.mpf('1e-90'))
        full = (1 - allocation(order, primes, upper)) * F
        other_full = (1 - allocation(order, other_primes, upper)) * G
        difference = full + other_full - joint_owner
        assert abs(full + other_full) <= gap_price + abs(difference)
        owner_norm_cost += abs(joint_owner)
        raw_norm_cost += abs(F + G)
        full_norm_cost += abs(full + other_full)
        nonowner_cost += abs(difference)
        local_price += gap_price
        max_gap = max(max_gap, gap)
    u = mp.mpf(10001) / 20000
    assert u ** (order + 1) * owner_norm_cost <= u ** (order + 1) * local_price
    return {
        'height': number_string(height), 'pairsSampled': len(sampled),
        'decreasingSharePairsInSample': reverse_share_pairs,
        'maxActualLogGap': number_string(max_gap),
        'sampleSourceScaledOwnerPairCost': number_string(u ** (order + 1) * owner_norm_cost),
        'sampleSourceScaledRawMismatch': number_string(u ** (order + 1) * raw_norm_cost),
        'sampleSourceScaledFullOriginalPairCost': number_string(u ** (order + 1) * full_norm_cost),
        'sampleSourceScaledNonownerDifference': number_string(u ** (order + 1) * nonowner_cost),
        'sampleSourceScaledCoupledPrice': number_string(u ** (order + 1) * local_price),
        'allLiteralPointwisePricesPassed': True,
        'originalFundingMultipliers': [1, 1],
        'fundingWitnessCertified': False,
    }


def single_case(order):
    upper, length = native_parameters(order)
    common = [2, 3, 5, 7, 11]
    log_b = length + mp.mpf('0.3') - mp.mpf('1.1') * order
    first = int(sp.nextprime(int(mp.exp(log_b - mp.fsum(mp.log(p) for p in common)))))
    common_integer = int(sp.prod(common))
    start, end = common_integer * first, common_integer * (first + 2048)
    owner = int(sp.nextprime(int(mp.exp(length - mp.log(start) + mp.mpf('0.3')))))
    second = int(sp.nextprime(int(mp.exp(2 * order - length - mp.mpf('0.3')))))
    parents, candidates, incidences = actual_family(order, common, start, end, 2000)
    assert len(candidates) >= len(parents)
    assert all(len(v) == 6 for v in parents.values())
    assert all(len(v) == 7 for v in candidates.values())
    return {
        'order': order, 'originalLeastPrime': 2, 'counts': [8, 9],
        'originalLabels': len(parents), 'distinctPartnerLabels': len(candidates),
        'partnerIncidences': incidences,
        'unorderedMatchingPairs': min(len(parents), len(candidates)),
        'finiteParentCoverage': 1.0,
        'evaluations': [test_pairs(order, upper, length, owner, second, parents,
                                   candidates, height, 10000) for height in (54, 65, 100)],
        'nativeManyBinFundingCoverageCertified': False,
    }


def collision_case(order):
    upper, length = native_parameters(order)
    cores = [[2, 3, 5, *pair] for pair in itertools.combinations([7, 11, 13, 17, 19], 2)]
    start = int(mp.exp(length + mp.mpf('0.3') - mp.mpf('1.1') * order))
    end = start + 256 * max(int(sp.prod(common)) for common in cores)
    owner = int(sp.nextprime(int(mp.exp(length - mp.log(start) + mp.mpf('0.3')))))
    second = int(sp.nextprime(int(mp.exp(2 * order - length - mp.mpf('0.3')))))
    parents = {}
    candidates = {}
    parent_occurrences = 0
    candidate_occurrences = 0
    multiplicities = {}
    for common in cores:
        old, new, _ = actual_family(order, common, start, end, 2000)
        parent_occurrences += len(old)
        candidate_occurrences += len(new)
        parents.update(old)
        candidates.update(new)
        for b in new:
            multiplicities[b] = multiplicities.get(b, 0) + 1
    assert parent_occurrences == len(parents)
    assert all(len(v) == 6 for v in parents.values())
    assert all(len(v) == 7 for v in candidates.values())
    paired = min(len(parents), len(candidates))
    return {
        'order': order, 'commonCofactorFamilies': len(cores),
        'originalLabels': len(parents),
        'partnerLabelsBeforeCrossCofactorDeduplication': candidate_occurrences,
        'distinctPartnerLabels': len(candidates),
        'crossCofactorPartnerCollisions': candidate_occurrences - len(candidates),
        'maxFamiliesGeneratingSamePartner': max(multiplicities.values(), default=0),
        'unorderedMatchingPairs': paired,
        'finiteParentCoverage': paired / len(parents) if parents else None,
        'evaluations': [test_pairs(order, upper, length, owner, second, parents,
                                   candidates, 54, 32)],
        'allCandidateLabelsDeduplicated': True,
        'exactSameOwnerAndSecondPrime': True,
        'nativeManyBinFundingCoverageCertified': False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    mp.mp.dps = 160
    report = {
        'scope': 'Finite actual unordered fixed-owner parity pairs and pooled partner collisions; not native unpaid count56+ many-bin/funding coverage.',
        'precisionDigits': mp.mp.dps,
        'singleCofactorCells': [single_case(order) for order in (128, 256)],
        'pooledCofactorCells': [collision_case(order) for order in (128, 256)],
        'exactMovingLengthRetained': True, 'fullComplexPhaseRetained': True,
        'sampledFullOriginalAllocationRetained': True,
        'distinctPartnerLabelsCountedOnce': True,
        'orderingOfOwnerSharesRequired': False, 'negativeFirstSignRequired': False,
        'nativeDyadicSupportCertified': False, 'fundingWitnessCertified': False,
        'nativeCount56ManyBinPopulationEvaluated': False,
        'allPrimeFactorConfigurationsCovered': False,
        'actualPrimeTests': 'Sympy deterministic below2^64, probable-prime tests above it; not Lean certificates.',
        'floatingResultsIntervalCertified': False, 'floorCertified': False,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()

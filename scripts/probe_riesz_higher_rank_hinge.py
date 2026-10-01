#!/usr/bin/env python3
"""Optional literal-label and exact rational probes of joined hinge ranks.

This verifies finite regressions, not a population floor or an effective
cofinal starting order. It is deliberately outside ordinary builds and CI.
All literal examples keep the original phase, owner allocation and masks.
The rational cube examples are explicitly not actual prime labels.
"""

import argparse
import cmath
from fractions import Fraction
import json
import math
from itertools import combinations

from sympy import isprime

from probe_riesz_canonical_joint import allocation, core_mask
from probe_riesz_lower_radial import make_prime, parameters


def subsets(values):
    for size in range(len(values) + 1):
        yield from combinations(values, size)


def rational_cube_regressions():
    results = []
    for count in range(2, 11):
        owner, offset = Fraction(1), Fraction(1, 10)
        increments = [Fraction(3, 5) + Fraction(i, 30) for i in range(count)]
        assert all(offset <= x <= owner and (owner + offset) / 2 <= x for x in increments)
        response = sum((-1) ** len(part) *
                       (max(0, owner + offset - sum(part)) - max(0, offset - sum(part)))
                       for part in subsets(increments))
        predicted = sum(increments) - (count - 1) * owner - count * offset
        assert response == predicted
        assert abs(response) <= (count - 1) * owner
        equal_centre = Fraction(1, count)
        centred = sum((-1) ** len(part) *
                      (max(0, owner + equal_centre - sum(part)) -
                       max(0, equal_centre - sum(part)))
                      for part in subsets([owner] * count))
        reinforcing = sum((-1) ** len(part) *
                          (max(0, 2 * owner - sum(part)) - max(0, owner - sum(part)))
                          for part in subsets([owner] * count))
        assert centred == 0 and reinforcing == -(count - 1) * owner
        results.append(dict(incrementCount=count, exactResponse=str(response),
                            exactFormula=str(predicted), exactCentreResponse=str(centred),
                            reinforcingEndpointResponse=str(reinforcing),
                            rationalModelOnly=True, actualPrimeLabel=False))
    return results


def literal_sample(index, count, height):
    ceiling = 2 ** (index + 3)
    order = 8 * (index + 4) * ceiling
    pars = parameters(order)
    primes = [make_prime(2 * order / count + (i - (count - 1) / 2) * order / 10000)
              for i in range(count)]
    assert len(set(primes)) == count and all(isprime(p) for p in primes)
    assert min(primes) > order ** 2
    label = math.prod(primes)
    assert core_mask(order, label, dict.fromkeys(primes, 1), pars, ceiling) == "core"
    logs = list(map(math.log, primes))
    total, owner = math.fsum(logs), logs[-1]
    cutoff = pars["length"]
    assert 1.97 * order < total <= 2.03 * order
    rank = next(k for k in range(2, count) if math.fsum(logs[:k]) >= cutoff)
    selected = logs[:rank]
    total_selected = math.fsum(selected)
    offset = total_selected - cutoff
    base_log = math.fsum(logs[rank:-1])
    pair_log = selected[0] + selected[1]
    assert 0 <= offset <= min(selected)
    assert all((owner + offset) / 2 <= x <= owner for x in selected)
    assert total - base_log + owner <= 2.03 * order
    first = pair_log - owner - 2 * offset
    rest = (rank - 2) * (owner + offset) - (total_selected - pair_log)
    sign = (-1) ** rank
    responses, retained, zero_old = [], [], []
    for marked in subsets(range(2, rank)):
        shift = math.fsum(selected[i] for i in marked)
        values = []
        for pair in subsets((0, 1)):
            tail = total_selected - shift - math.fsum(selected[i] for i in pair)
            values.append((-1) ** (rank - len(marked) - len(pair)) *
                          (max(0, owner + tail - cutoff) - max(0, tail - cutoff)))
        value = math.fsum(values)
        current_base = base_log + shift
        upper = total - cutoff - current_base
        affine_side = upper <= owner or owner + current_base + pair_log <= total - cutoff
        short = (current_base + pair_log < total - 1.9495 * order and
                 current_base + pair_log <= total - cutoff and
                 affine_side and owner < 1.215 * order)
        affine = (current_base + pair_log <= total - cutoff and affine_side and
                  owner < 1.215 * order and
                  total - current_base + owner <= 2.03 * order and not short)
        responses.append(value)
        if short or affine:
            assert abs(value) < 1e-8
            zero_old.append(value)
        else:
            retained.append(value)
    joined, literal_retained = math.fsum(responses), math.fsum(retained)
    predicted = sign * (total_selected - (rank - 1) * owner - rank * offset)
    assert abs(joined - predicted) < 1e-8 and abs(literal_retained - joined) < 1e-8
    assert abs(responses[0] - sign * first) < 1e-8
    assert abs(math.fsum(responses[1:]) + sign * rest) < 1e-8
    separate = abs(sign * first) + abs(sign * rest)
    old_pair_separate = math.fsum(map(abs, responses))
    assert abs(separate - old_pair_separate) < 1e-8
    quarter = 3 * first <= 5 * rest and 3 * rest <= 5 * first
    if quarter:
        assert abs(joined) <= separate / 4 + 1e-8
    allocated = allocation(order, pars["orders"], 1 - owner / total)
    assert 0 <= allocated < 1
    log_weight = ((order + 1) * math.log(10001 / 20000) - 1.5 * total +
                  (order + 1) * math.log(total) - math.lgamma(order + 1) -
                  math.log(cutoff) + math.log1p(-allocated))
    observation = cmath.exp(-1j * height * total)
    scaled_real = math.exp(log_weight) * joined * observation.real if log_weight > -745 else None
    return dict(N=order, K=ceiling, totalPrimeCount=count, blockRank=rank,
                totalLogPerN=total / order, offsetPerLeastLog=offset / min(selected),
                originalPairOrbits=len(responses), nonzeroPairOrbits=sum(abs(v) > 1e-8 for v in responses),
                originalIncidenceCount=4 * len(responses), filteredOldZeroOrbits=len(zero_old),
                filteredOldZeroResponse=math.fsum(zero_old),
                exactFirstAmplitude=first, exactOtherRanksAmplitude=rest,
                joinedResponse=joined, exactFormula=predicted,
                currentRetainedResponse=literal_retained,
                separateCanonicalAllowance=old_pair_separate, joinedAllowance=abs(joined),
                localAllowanceRatio=abs(joined) / separate, quarterSectorApplies=quarter,
                originalCoreMask="core", roughPhysicalPrimes=True, ownerGapFails=True,
                originalPhaseAndAllocationRetained=True, allocatedFraction=allocated,
                sourceScaledLogWeight=log_weight, floatingUnderflow=log_weight < -745,
                sourceScaledReal=scaled_real, belowReducedCountThreshold=256 * count < ceiling,
                eventualCropNotAFiniteCertificate=True, populationMassCertified=False,
                wholeFloorCertified=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--height", type=float, default=54.0)
    args = parser.parse_args()
    literal = [literal_sample(index, count, args.height)
               for index, counts in ((1, (7, 10, 14)), (2, (7, 10, 14, 20)))
               for count in counts]
    print(json.dumps(dict(exactRationalRegressions=rational_cube_regressions(), literal=literal,
                          wholeFloorCertified=False, outsideBuildsAndCI=True), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

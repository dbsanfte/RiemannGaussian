#!/usr/bin/env python3
"""Optional actual-label probe of the joined low-offset hinge floor.

The local eight-incidence saving is diagnostic. It is not a bound on
the population, a cofinal starting order, or the whole arithmetic floor.
The ideal large-order scan is explicitly separate from literal prime labels.
This script is not run by ordinary builds or CI.
"""

import argparse
import cmath
import json
import math
from itertools import combinations

from sympy import isprime

from probe_riesz_canonical_joint import allocation, core_mask
from probe_riesz_lower_radial import make_prime, parameters


def literal_sample(index, height):
    count_ceiling = 2 ** (index + 3)
    order = 8 * (index + 4) * count_ceiling
    # Seven distinct primes close to equal shares, with the largest as owner.
    logs = [2 * order / 7 + (i - 3) * order / 10000 for i in range(7)]
    primes = [make_prime(value) for value in logs]
    assert len(set(primes)) == 7 and all(isprime(p) for p in primes)
    owner = primes[-1]
    r, s, q, base = primes[:4]
    cofactor = math.prod(primes[:-1])
    label = owner * cofactor
    pars = parameters(order)
    assert core_mask(order, label, dict.fromkeys(primes, 1), pars, count_ceiling) == "core"
    total = math.log(label)
    assert 1.97 * order < total <= 2.03 * order
    cutoff = pars["length"]
    offset = math.log(cofactor // base) - cutoff
    alpha, beta, neighbour, owner_log = map(math.log, (r, s, q, owner))
    assert 0 < offset < alpha
    assert neighbour <= owner_log
    assert owner_log + offset < alpha + beta
    assert total - math.log(base) + owner_log <= 2.03 * order
    first_amplitude = alpha + beta - owner_log - 2 * offset
    second_amplitude = owner_log + offset - neighbour
    assert first_amplitude >= 0 and second_amplitude >= 0
    assert first_amplitude <= 5 * second_amplitude
    assert second_amplitude <= 5 * first_amplitude
    responses = []
    incidence_ids = []
    for unsigned, frozen in ((base, cofactor // base), (base * q, cofactor // (base * q))):
        values = []
        for subset_size in range(3):
            for subset in combinations((r, s), subset_size):
                divisor = math.prod(subset)
                b = frozen // divisor
                parity = sum(b % p == 0 for p in primes)
                hinge = max(0.0, math.log(owner * b) - cutoff) - max(0.0, math.log(b) - cutoff)
                values.append((-1) ** parity * hinge)
                incidence_ids.append((unsigned * divisor, b))
        responses.append(math.fsum(values))
    assert len(set(incidence_ids)) == 8
    assert all(d * b == cofactor for d, b in incidence_ids)
    assert abs(responses[0] + first_amplitude) < 1e-9
    assert abs(responses[1] - second_amplitude) < 1e-9
    observed = math.fsum(responses)
    predicted = -(alpha + beta + neighbour - 2 * owner_log - 3 * offset)
    assert abs(observed - predicted) < 1e-9
    separate = math.fsum(abs(value) for value in responses)
    assert abs(observed) <= 2 * separate / 3 + 1e-9
    allocated = allocation(order, pars["orders"], 1 - owner_log / total)
    assert 0 <= allocated < 1
    log_common = ((order + 1) * math.log(10001 / 20000) - 1.5 * total
                  + (order + 1) * math.log(total) - math.lgamma(order + 1)
                  - math.log(cutoff) + math.log1p(-allocated))
    phase = cmath.exp(-1j * height * total)
    scaled_real = math.exp(log_common) * observed * phase.real if log_common > -745 else None
    return dict(dyadicIndex=index, N=order, K=count_ceiling, primeCount=7,
                originalCoreMask="core", totalLogPerN=total / order,
                offsetPerLeastLog=offset / alpha, signedOldBlocks=responses,
                joinedCoefficient=observed, exactFormula=predicted,
                separateAllowance=separate, joinedAllowance=abs(observed),
                localAllowanceRatio=abs(observed) / separate,
                certifiedSectorRatio=2 / 3,
                oldOverlapSelectorApplies=neighbour <= offset,
                bothOldAffineSelectorsFail=True, originalOwnerGapFails=True,
                originalPhaseAndAllocationRetained=True,
                allocatedFraction=allocated, sourceScaledLogAmplitude=log_common,
                floatingUnderflow=log_common < -745, sourceScaledReal=scaled_real,
                belowReducedCountThreshold=256 * 7 < count_ceiling,
                eventualCountPaymentNotAFiniteCertificate=True,
                populationMassCertified=False, wholeFloorCertified=False)


def ideal_scan():
    results = []
    for index in (8, 12, 20):
        count = 2 ** (index + 3)
        order = 8 * (index + 4) * count
        u = 10001 / 20000
        # Ideal logarithmic coordinates only: no primes are constructed here.
        cutoff = 2 * (order * math.log(1 / u) - math.log(order + 1))
        share = 2 * order / 7
        offset = 5 * share - cutoff
        first, second = share - 2 * offset, offset
        assert first > 0 and second > 0 and first <= 5 * second
        results.append(dict(idealLogGeometryOnly=True, actualPrimeLabel=False,
                            dyadicIndex=index, N=order, K=count,
                            belowReducedCountThreshold=256 * 7 < count,
                            localAllowanceRatio=abs(first - second) / (first + second),
                            populationMassCertified=False, wholeFloorCertified=False))
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dyadic-index", type=int, default=1, choices=(1, 2))
    parser.add_argument("--height", type=float, default=54.0)
    args = parser.parse_args()
    print(json.dumps(dict(literal=literal_sample(args.dyadic_index, args.height),
                          idealLargeOrderScan=ideal_scan()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

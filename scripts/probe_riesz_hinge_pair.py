#!/usr/bin/env python3
"""Optional original-label test of pairing the two sides of a Riesz hinge.

The paired blocks use the SAME squarefree label, complex phase, owner and
factorial/allocation weight. The complete eight incidences are retained.
Samples follow the actual dyadic order/count schedule. Floating observations
are diagnostics, not a cofinal source-scale bound or a floor certificate.
This script is outside ordinary builds and CI.
"""

import argparse
import cmath
import json
import math
import random

import numpy as np

from sympy import isprime, nextprime

from probe_riesz_canonical_joint import allocation, core_mask
from probe_riesz_lower_radial import parameters, make_prime


def paired_label(j, offset, height):
    count_ceiling = 2**(j+3)
    n = 8*(j+4)*count_ceiling
    pars = parameters(n)
    r, s, q = 2, 3, 5
    width = math.log(r*s/q)
    midpoint = math.log(r*s*q)/2
    desired_d = midpoint+offset*width
    # Choose p and e with the owner largest, and the WHOLE based owner
    # gap failed. These inequalities leave room because 2.02 < 2.03.
    p = make_prime((4.05*n-2*pars['length']-2*desired_d)/4)
    middle_count = 7 if j == 1 else 11
    target_b = pars['length']+desired_d
    small_log = math.log(r*s*q)
    start = make_prime((target_b-small_log)/middle_count)
    middle = []
    for _ in range(middle_count-1):
        middle.append(start)
        start = int(nextprime(start))
    last = make_prime(target_b-small_log-sum(math.log(v) for v in middle))
    assert last not in middle
    middle.append(last)
    b = r*s*q*math.prod(middle)
    e = make_prime(2.02*n-math.log(p*b))
    a = b*e
    label = p*a
    primes = [p, r, s, q, e, *middle]
    assert len(set(primes)) == len(primes)
    assert all(isprime(v) for v in primes)
    assert max(primes) == p
    assert core_mask(n, label, dict.fromkeys(primes, 1), pars, count_ceiling) == 'core'
    total = math.log(label)
    d = math.log(b)-pars['length']
    assert math.log(q) < d < math.log(r*s)
    assert math.log(p*b)-pars['length'] >= math.log(r*s*q)
    assert total-math.log(e)+math.log(p) <= 2.03*n
    assert total-math.log(e*q)+math.log(p) <= 2.03*n
    blocks, original_incidences = [], []
    for base, frozen in [(e, b), (e*q, b//q)]:
        values = []
        for delta, parity in [(1, 1), (r, -1), (s, -1), (r*s, 1)]:
            cofactor = frozen//delta
            assert base*delta*cofactor == a
            hinge = max(0, math.log(p*cofactor)-pars['length'])-max(
                0, math.log(cofactor)-pars['length'])
            count = len([v for v in primes if cofactor % v == 0])
            values.append((-1)**count*hinge)
            original_incidences.append([base*delta, cofactor])
        blocks.append(math.fsum(values))
    assert len({v[0] for v in original_incidences}) == 8
    mu_b = (-1)**(len(primes)-2)
    predicted = -mu_b*(math.log(r*s*q)-2*d)
    joined = math.fsum(blocks)
    assert abs(joined-predicted) < 1e-9
    separate_cost = math.fsum(abs(v) for v in blocks)
    assert abs(separate_cost-width) < 1e-9
    allocation_weight = 1-allocation(n, pars['orders'], 1-math.log(p)/total)
    log_common = ((n+1)*math.log(10001/20000)-1.5*total+
                  (n+1)*math.log(total)-math.lgamma(n+1)-math.log(pars['length']))
    log_common += math.log(allocation_weight)
    phase = cmath.exp(-1j*height*total)
    # Do not report underflow as a zero-valued source observation.
    scaled_real = math.exp(log_common)*phase.real*joined if log_common > -745 else None
    return dict(dyadicIndex=j, N=n, countCeiling=count_ceiling, count=len(primes),
                originalCoreMask='core', totalLogPerN=total/n,
                primePair=[r, s], neighbouringPrime=q,
                crossing=d, crossingWidth=math.log(r*s),
                remainingOverlapWidth=width,
                midpoint=midpoint, requestedOffset=offset,
                signedFourIncidenceBlocks=blocks,
                joinedEightIncidences=joined, exactFormula=predicted,
                separateBlockAllowance=separate_cost,
                jointAllowance=abs(joined),
                localAllowanceRatio=abs(joined)/separate_cost,
                bothOriginalHingesRetained=True,
                bothFirstHingesFullySaturated=True,
                bothOriginalOwnerGapsFail=True,
                originalPhaseAndAllocationUnchanged=True,
                ownerAllocatedFraction=1-allocation_weight,
                sourceScaledLogAmplitude=log_common,
                floatingUnderflow=log_common < -745,
                sourceScaledReal=scaled_real,
                sourcePopulationMassCertified=False,
                wholeFloorCertified=False)


def other_hinge_regression():
    # A small KERNEL-ONLY test: cancelling the second-hinge midpoint is
    # invalid if the adjacent block still meets the first hinge.
    p, r, s, q = 13, 5, 7, 11
    b = r*s*q
    d = math.log(r*s*q)/2
    length = math.log(b)-d
    responses = []
    for frozen in (b, b//q):
        values = []
        for delta in (1, r, s, r*s):
            cofactor = frozen//delta
            count = sum(cofactor % v == 0 for v in (r, s, q))
            values.append((-1)**count*(max(0, math.log(p*cofactor)-length)-
                                         max(0, math.log(cofactor)-length)))
        responses.append(math.fsum(values))
    remaining_first = max(0, math.log(r*s*q)-math.log(p)-d)
    assert remaining_first > 0
    assert abs(abs(math.fsum(responses))-remaining_first) < 1e-12
    return dict(kernelOnly=True, notAnOriginalCoreSample=True,
                individualBlocks=responses, joined=math.fsum(responses),
                secondHingeOnlyPrediction=0., retainedFirstHinge=remaining_first,
                falseMidpointCancellationRejected=True)


def two_hinge_regressions():
    """The close-owner boundary moves the zero; keep its signed moments."""
    r, s, q = 5, 7, 11
    b = r*s*q
    total_small = math.log(b)
    width = math.log(r*s/q)
    cases = []
    for p in (13, 17, 19, 23, 29):
        centre = total_small/2+max(0., total_small-2*math.log(p))/6
        for offset in (-1/6, 0., 1/6):
            d = centre+offset*width
            length = math.log(b)-d
            values = []
            for divisor, sign in ((1, 1), (r, -1), (s, -1), (q, -1),
                                   (r*s, 1), (r*q, 1), (s*q, 1), (b, -1)):
                cofactor = b//divisor
                # mu(b)=-1, and the original cofactor parity is retained.
                values.append(-sign*(max(0., math.log(p*cofactor)-length)-
                                     max(0., math.log(cofactor)-length)))
            observed = math.fsum(values)
            predicted = total_small-2*d+max(0., total_small-math.log(p)-d)
            assert abs(observed-predicted) < 1e-12
            assert abs(observed) <= width/2+1e-12
            cases.append(dict(ownerPrime=p, adaptiveCentre=centre, offset=offset,
                              coefficient=observed, exactPrediction=predicted,
                              halfWidthBudget=width/2))
    # One original cofactor, different prime endpoints: keep BOTH moments
    # of the clipped subset, instead of attaching a positive boundary cost.
    d = total_small/2
    length = total_small-d
    primes = (13, 17, 19, 23, 29, 31)
    weights = {p: cmath.exp(-54j*math.log(p*b))*math.log(p*b)**7/(p*b)**1.5
               for p in primes}
    clipped = [p for p in primes if math.log(p) < total_small-d]
    m0 = sum(weights.values())
    clipped_m0 = sum(weights[p] for p in clipped)
    clipped_m1 = sum(math.log(p)*weights[p] for p in clipped)
    direct = sum(weights[p]*(total_small-2*d+
                            max(0., total_small-math.log(p)-d)) for p in primes)
    joined = (total_small-2*d)*m0+(total_small-d)*clipped_m0-clipped_m1
    assert abs(direct-joined) < 1e-12
    return dict(kernelOnly=True, notAnOriginalCoreSample=True, adaptiveCases=cases,
                clippedPrimeSubset=clipped,
                jointSignedMomentReal=joined.real,
                directReal=direct.real, equalityResidual=abs(direct-joined),
                separatelyAbsoluteMomentCost=(abs((total_small-2*d)*m0)+
                                               abs((total_small-d)*clipped_m0)+abs(clipped_m1)),
                sourcePopulationMassCertified=False, wholeFloorCertified=False)


def close_owner_label(j, height):
    """Original core label where the formerly excluded OTHER hinge cancels."""
    count_ceiling = 2**(j+3)
    n = 8*(j+4)*count_ceiling
    pars = parameters(n)
    count, frozen_count = (15, 12) if j == 1 else (28, 21)
    target_log = pars['length']/(frozen_count-5/3)
    primes = [make_prime(target_log)]
    while len(primes) < count:
        primes.append(int(nextprime(primes[-1])))
    r, s, q, p = *primes[:3], primes[-1]
    b = math.prod(primes[:frozen_count])
    e = math.prod(primes[frozen_count:-1])
    a, label = b*e, p*b*e
    assert len(set(primes)) == count and all(isprime(v) for v in primes)
    assert p == max(primes)
    assert core_mask(n, label, dict.fromkeys(primes, 1), pars, count_ceiling) == 'core'
    total_small = math.log(r*s*q)
    d = math.log(b)-pars['length']
    centre = total_small/2+max(0., total_small-2*math.log(p))/6
    width = math.log(r*s/q)
    assert math.log(q) < d < math.log(r*s)
    assert math.log(p*b)-pars['length'] < total_small
    assert math.log(label)-math.log(e)+math.log(p) <= 2.03*n
    responses = []
    for base, frozen in ((e, b), (e*q, b//q)):
        block = []
        for divisor in (1, r, s, r*s):
            cofactor = frozen//divisor
            cofactor_count = sum(cofactor % v == 0 for v in primes)
            assert base*divisor*cofactor == a
            block.append((-1)**cofactor_count*(max(0., math.log(p*cofactor)-pars['length'])-
                                              max(0., math.log(cofactor)-pars['length'])))
        responses.append(math.fsum(block))
    first_counter = max(0., total_small-math.log(p)-d)
    joined = math.fsum(responses)
    exact = -(-1)**frozen_count*(total_small-2*d+first_counter)
    assert first_counter > 0 and abs(joined-exact) < 1e-9
    assert abs(d-centre) < 1e-9 and abs(joined) < 1e-9
    total = math.log(label)
    unassigned = 1-allocation(n, pars['orders'], 1-math.log(p)/total)
    log_common = ((n+1)*math.log(10001/20000)-1.5*total+
                  (n+1)*math.log(total)-math.lgamma(n+1)-math.log(pars['length'])+
                  math.log(unassigned))
    return dict(N=n, count=count, countCeiling=count_ceiling,
                originalCoreMask='core', totalLogPerN=total/n,
                allPrimesBeyondPolynomialCap=all(v > n*n for v in primes),
                signedFourIncidenceBlocks=responses, joinedEightIncidences=joined,
                fullTwoHingePrediction=exact,
                oldSecondHingeOnlyPrediction=-(-1)**frozen_count*(total_small-2*d),
                remainingFirstHinge=first_counter, adaptiveCentre=centre,
                centreResidual=abs(d-centre), halfWidthBudget=width/2,
                firstHingesFullySaturated=False,
                bothOriginalOwnerGapsFail=True,
                originalPhaseAndAllocationUnchanged=True,
                originalPhaseReal=cmath.exp(-1j*height*total).real,
                sourceScaledLogAmplitude=log_common,
                floatingUnderflow=log_common < -745,
                diagnosticOnly=True, sourcePopulationMassCertified=False,
                wholeFloorCertified=False)


def subset_arrays(logs):
    values = np.array([0.], dtype=np.longdouble)
    counts = np.array([0], dtype=np.int16)
    for value in logs:
        values = np.concatenate((values, values+value))
        counts = np.concatenate((counts, counts+1))
    return values, counts


def profile_label(j, spread, height):
    """Sum EVERY original base in the crossing's middle half.

    Meet-in-the-middle prefix sums retain parity and the linear moment.
    No density model generates labels or evaluates their signed response.
    """
    count_ceiling = 2**(j+3)
    n = 8*(j+4)*count_ceiling
    pars = parameters(n)
    r, s, q = [make_prime(z) for z in (14., 15., 16.)] if j == 1 else [
        make_prime(z) for z in (16., 17., 18.)]
    smallest_logs = sum(math.log(v) for v in (r, s, q))
    width = math.log(r*s/q)
    m, k = (10, 2) if j == 1 else (24, 5)
    z = (pars['length']-smallest_logs/2+width/8)/(m-k)
    if spread:
        rng = random.Random(20261001+j)
        ratios = [rng.uniform(.4, 1.6) for _ in range(m)]
        mean = sum(ratios)/m
        target_logs = [z*v/mean for v in ratios]
    else:
        target_logs = [z]*m
    middle = []
    for target in target_logs:
        prime = make_prime(target)
        while prime in middle:
            prime = int(nextprime(prime))
        middle.append(prime)
    a = r*s*q*math.prod(middle)
    p = make_prime(2.02*n-math.log(a))
    label = p*a
    primes = [p, r, s, q, *middle]
    assert max(primes) == p and q < min(middle)
    assert len(set(primes)) == len(primes) and all(isprime(v) for v in primes)
    assert core_mask(n, label, dict.fromkeys(primes, 1), pars, count_ceiling) == 'core'
    # Restrict only ORIGINAL based blocks that satisfy the proved crossing
    # and failed-gap conditions. No outside bases are estimated here.
    centre = math.log(a)-pars['length']-smallest_logs/2
    lower = max(centre-width/4, math.log(label)+math.log(p)-2.03*n)
    upper = centre+width/4
    assert lower < upper
    assert math.log(p)+(smallest_logs/2-width/4) >= smallest_logs
    logs = [math.log(v) for v in middle]
    left, left_count = subset_arrays(logs[:m//2])
    right, right_count = subset_arrays(logs[m//2:])
    order = np.argsort(right)
    right, right_count = right[order], right_count[order]
    sign = np.where(right_count % 2 == 0, 1., -1.).astype(np.longdouble)
    prefix_sign = np.concatenate(([0.], np.cumsum(sign, dtype=np.longdouble)))
    prefix_signed_log = np.concatenate(([0.], np.cumsum(sign*right, dtype=np.longdouble)))
    prefix_log = np.concatenate(([0.], np.cumsum(right, dtype=np.longdouble)))
    lo = np.searchsorted(right, lower-left, side='left')
    hi = np.searchsorted(right, upper-left, side='right')
    middle_axis = np.searchsorted(right, centre-left, side='left')
    middle_axis = np.minimum(hi, np.maximum(lo, middle_axis))
    constant = np.longdouble(-2*centre)
    mu_a = (-1)**(m+3)
    left_sign = np.where(left_count % 2 == 0, 1., -1.)
    signed_rows = mu_a*left_sign*((constant+2*left)*(prefix_sign[hi]-prefix_sign[lo])+
                                2*(prefix_signed_log[hi]-prefix_signed_log[lo]))
    signed_profile = float(np.sum(signed_rows, dtype=np.longdouble))
    raw_rows = (constant+2*left)*(hi-lo)+2*(prefix_log[hi]-prefix_log[lo])
    below = (constant+2*left)*(middle_axis-lo)+2*(prefix_log[middle_axis]-prefix_log[lo])
    absolute_profile = float(np.sum(raw_rows-2*below, dtype=np.longdouble))
    count_table = {}
    for rc in range(m-m//2+1):
        prefix = np.concatenate(([0], np.cumsum(right_count == rc)))
        for lc in range(m//2+1):
            selected = left_count == lc
            count = int(np.sum((prefix[hi]-prefix[lo])[selected]))
            if count:
                cofactor_count = m+3-lc-rc
                count_table[cofactor_count] = count_table.get(cofactor_count, 0)+count
    card = int(np.sum(hi-lo))
    assert card == sum(count_table.values()) and card > 0
    assert abs(signed_profile) <= absolute_profile+1e-6
    total = math.log(label)
    unassigned = 1-allocation(n, pars['orders'], 1-math.log(p)/total)
    log_common = ((n+1)*math.log(10001/20000)-1.5*total+
                  (n+1)*math.log(total)-math.lgamma(n+1)-math.log(pars['length'])+
                  math.log(unassigned))
    return dict(N=n, count=len(primes), countCeiling=count_ceiling,
                geometry='spread prime logs' if spread else 'clustered prime logs',
                originalCoreMask='core', allPrimesBeyondPolynomialCap=all(v > n*n for v in primes),
                retainedBaseCount=card, distinctOriginalIncidences=8*card,
                cofactorCountHistogram=count_table,
                signedProfile=signed_profile, absoluteDisplacementProfile=absolute_profile,
                signedToAbsoluteRatio=abs(signed_profile)/absolute_profile,
                halfOverlapBudget=width/2*card,
                originalPhaseReal=cmath.exp(-1j*height*total).real,
                sourceScaledLogAmplitude=log_common,
                floatingUnderflow=log_common < -745,
                originalPhaseAndAllocationUnchanged=True,
                actualAllBaseProfileSummed=True,
                diagnosticOnly=True, globalBudgetCertified=False,
                wholeFloorCertified=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dyadic-index', type=int, choices=(1, 2), default=1)
    parser.add_argument('--height', type=float, default=54.)
    args = parser.parse_args()
    results = [paired_label(args.dyadic_index, offset, args.height)
               for offset in (-.25, 0., .25)]
    print(json.dumps(dict(diagnosticOnly=True, actualDyadicSchedule=True,
                         pairedCrossings=results,
                         allBaseProfiles=[profile_label(args.dyadic_index, spread, args.height)
                                          for spread in (False, True)],
                         otherHingeRegression=other_hinge_regression(),
                         twoHingeRegressions=two_hinge_regressions(),
                         closeOwnerOriginalLabel=close_owner_label(args.dyadic_index, args.height),
                         cofinalBoundCertified=False, wholeFloorCertified=False), indent=2))


if __name__ == '__main__':
    main()

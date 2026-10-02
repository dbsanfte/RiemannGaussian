#!/usr/bin/env python3
"""Optional unpaid-only ALL-COUNT product-inventory capacity audit.

The complete finite Riesz differences are joined with reciprocal-prime
product weights. The Bernoulli recurrence retains every insertion count.
Integer dynamic programming gives exact rational rounding brackets for
the supplied normalized logs; small cases have an independent signed
subset enumeration. These are virtual log geometries, NOT actual prime
owner inventories or a native floor/source-budget certificate.
"""

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
import mpmath as mp
import sympy as sp

from probe_riesz_clipped_insertions import inner_model, scope_context, text_number
from probe_riesz_generic_patterns import allocation_enclosure, finite_number
from riesz_subset_moments import binary_fraction


def hinge_average(primes, logs, d, grid, round_up):
    """Exact INTEGER probability numerators, including the empty state.

    Positive shifts cannot return to the hinge once past d. Such states
    have exactly zero response, rather than an omitted unknown count tail.
    No floating probability, renormalization or parity truncation is used.
    """
    cap = (d * grid).__floor__()
    numerator = [1] + [0] * cap
    denominator = 1
    for prime, log in zip(primes, logs):
        scaled = log * grid
        shift = scaled.__ceil__() if round_up else scaled.__floor__()
        numerator = [(prime - 1) * value + (numerator[i-shift] if i >= shift else 0)
                     for i, value in enumerate(numerator)]
        denominator *= prime
    return sum(Fraction(value, denominator) * (d - Fraction(i, grid))
               for i, value in enumerate(numerator))


def signed_enumeration(primes, logs, d):
    """Independent exact nested signed Riesz evaluation for small families."""
    n = len(primes)
    total = Fraction(0)
    absolute_counts = Fraction(0)
    layers = {k: Fraction(0) for k in range(n+1)}
    positive, negative = [], []
    knots = [Fraction(0)] * (1 << n)
    weights = [Fraction(1)] * (1 << n)
    for bits in range(1, 1 << n):
        low = bits & -bits
        i = low.bit_length()-1
        knots[bits] = knots[bits-low] + logs[i]
        weights[bits] = weights[bits-low] / primes[i]
    for bits in range(1 << n):
        value = Fraction(0)
        sub = bits
        while True:
            value += (-1)**sub.bit_count() * max(Fraction(0), d-knots[sub])
            if not sub:
                break
            sub = (sub-1) & bits
        term = (-1)**bits.bit_count() * weights[bits] * value
        total += term
        absolute_counts += abs(term)
        layers[bits.bit_count()] += term
        if term > 0:
            positive.append([bits,term,term])
        elif term < 0:
            negative.append([bits,-term,-term])
    bernoulli = sum(weights[bits] *
                    Fraction(math.prod(primes[i]-1 for i in range(n)
                                                    if not (bits >> i) & 1),
                             math.prod(primes[i] for i in range(n)
                                                    if not (bits >> i) & 1)) *
                    max(Fraction(0), d-knots[bits]) for bits in range(1 << n))
    assert total == bernoulli
    assert total >= max(Fraction(0), d-sum(x/prime for x,prime in zip(logs,primes)))
    assert total >= d * math.prod(Fraction(prime-1,prime) for prime in primes)
    # Maximally generous matching: EVERY opposite-sign coefficient may
    # pair, with no extra geometry restriction. Track column capacity
    # exactly; a node's original funded mass cannot be spent twice.
    i=j=0
    matched=Fraction(0)
    while i < len(positive) and j < len(negative):
        amount=min(positive[i][2],negative[j][2])
        positive[i][2]-=amount;negative[j][2]-=amount;matched+=amount
        if not positive[i][2]:i+=1
        if not negative[j][2]:j+=1
    assert all(0 <= remaining <= initial for _,initial,remaining in positive+negative)
    deficit=sum(v[2] for v in positive)-sum(v[2] for v in negative)
    assert deficit == total and sum(v[2] for v in negative) == 0
    capacity=dict(
        positiveCoefficientMassOverOriginal=text_number(sum(v[1] for v in positive)/d),
        negativeCoefficientMassOverOriginal=text_number(sum(v[1] for v in negative)/d),
        maximallyGenerousMatchedMassOverOriginal=text_number(matched/d),
        exactUnmatchedMassOverOriginal=text_number(deficit/d),
        allOppositeSignEdgesAllowed=True, everyNodeFundingCapacityRespected=True,
        exactPositiveCapacityDeficit=True, nativeMatchingCertified=False)
    return total, absolute_counts, layers, capacity


def case(count, seed, j, tau_ratio, pool_size, grids):
    pars, P, Q, base = inner_model(count, seed, j, tau_ratio)
    L, N = pars['length'], pars['N']
    _, original = scope_context(pars, P, [Q, *base])
    row = dict(baseCofactorCount=count, originalWholeCount=count+1,
               largestWholeCount=count+1+pool_size, nativeIndex=j, N=str(N),
               tauToBaseHead=str(tau_ratio), poolSize=pool_size, original=original,
               primePopulation=False, nativeFloorCredit=False)
    if not original['unpaidScope']['eligible']:
        row['status'] = 'skipped_paid_before_coefficient_work'
        return row
    p, q, length = map(binary_fraction, (P,Q,L))
    bs = list(map(binary_fraction,base))
    B, head = sum(bs), min(bs)
    tau = p+B-length
    T = p+q+B
    d = tau/head
    primes = list(map(int, sp.primerange(2, 10000)))[:pool_size]
    assert len(primes) == pool_size
    # Exact finite-input virtual logs below the OLD base head. The
    # underlying reciprocal weights are 1/prime, not arbitrary beta=1.
    logs = [binary_fraction(mp.mpf(9)/10*mp.log(prime)/mp.log(primes[-1]))
            for prime in primes]
    inserted = [head*x for x in logs]
    new_p = p-sum(inserted)
    _, endpoint = scope_context(pars, finite_number(new_p),
                                [finite_number(q), *base, *map(finite_number,inserted)])
    # All subsets have the SAME exact total log. Count and owner extrema,
    # largest coordinates and pre-existing occupied bins bound the family.
    guards = dict(
        originalUnpaid=original['unpaidScope']['eligible'],
        maximalInsertionUnpaid=endpoint['unpaidScope']['eligible'],
        countsInsideUnpaidBand=count+1+pool_size < 5*mp.log(N+1)+2,
        allCoordinatesDistinct=len(set(bs+[q]+inserted)) == len(bs)+1+len(inserted),
        smallestVirtualPrimeAbovePhysicalRough=min(inserted) > binary_fraction(2*mp.log(N)),
        ownerStillLargest=new_p > max([q,*bs,*inserted]),
        upperHingeSaturation=q+B+sum(inserted) <= length,
        lowerHingeSaturation=B+sum(inserted) <= T-length,
        unchangedOldBaseHead=0 <= tau <= head,
        insertedLogsBelowOldBaseHead=all(0 < x < head for x in inserted))
    row['allSubsetGuardExtrema'] = {k:bool(v) for k,v in guards.items()}
    if not all(guards.values()):
        row['status'] = 'skipped_before_coefficient_work'
        return row
    row['status'] = 'complete_product_inventory_model'
    original['allocation'] = allocation_enclosure(pars,[P,Q,*base],finite_number(T))
    endpoint['allocation'] = allocation_enclosure(pars,
        [finite_number(new_p),finite_number(q),*base,*map(finite_number,inserted)],finite_number(T))
    row['maximalInsertion'] = endpoint
    row['representedInsertionSubsets'] = str(2**pool_size)
    row['countRangeComplete'] = [count+1,count+1+pool_size]
    row['countTailTruncated'] = False
    row['meanInsertedShare'] = text_number(sum(x/prime for x,prime in zip(logs,primes)))
    row['meanDeficitLowerBoundOverOriginal'] = text_number(
        max(Fraction(0), d-sum(x/prime for x,prime in zip(logs,primes)))/d)
    empty = math.prod(Fraction(prime-1,prime) for prime in primes)
    row['emptyChannelLowerBoundOverOriginal'] = text_number(empty)
    estimates = []
    for grid in grids:
        lower = hinge_average(primes, logs, d, grid, True)
        upper = hinge_average(primes, logs, d, grid, False)
        assert 0 < lower <= upper <= d
        estimates.append(dict(grid=grid, exactRationalLowerOverOriginal=text_number(lower/d),
                              exactRationalUpperOverOriginal=text_number(upper/d),
                              coefficientProbabilityArithmeticExact=True,
                              sourceOrLiteralPrimeInventoryCertified=False))
    row['roundingBrackets'] = estimates
    if pool_size <= 8:
        exact, absolute, layers, capacity = signed_enumeration(primes, logs, d)
        for grid in grids:
            assert hinge_average(primes,logs,d,grid,True) <= exact <= hinge_average(primes,logs,d,grid,False)
        row['independentSignedEnumeration'] = dict(
            exactEquality=True, allCountsRetained=True,
            joinedOverOriginal=text_number(exact/d),
            separateAbsoluteCountsOverOriginal=text_number(absolute/d),
            completeSignedLayers={k:text_number(v/d) for k,v in layers.items()})
        row['completeFiniteCapacityAudit'] = capacity
    row['phase'] = []
    for y in (54,65,100):
        phase = (-1)**len(bs)*mp.exp(-1j*y*finite_number(T))
        row['phase'].append(dict(height=y, originalRealPhase=text_number(phase.real),
                                 adverseOriginal=bool(phase.real < 0),
                                 residualHasSamePhase=True, exactEqualTotalLogModel=True,
                                 actualPrimePartnersProved=False))
    row['fullAllocatedTransportEvaluated'] = False
    row['allocationEnclosuresRetainedAtExtrema'] = True
    row['globalMatchingCapacityCertified'] = False
    return row


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--counts',type=int,nargs='+',default=[20,55,64,300,4000])
    parser.add_argument('--pools',type=int,nargs='+',default=[8,32,64])
    parser.add_argument('--grids',type=int,nargs='+',default=[1024,4096])
    parser.add_argument('--native-j',type=int,default=1024)
    parser.add_argument('--output',type=Path,default=Path('.lake/riesz-insertion-capacity/scan.json'))
    args=parser.parse_args()
    if args.native_j < 0 or any(k < 3 for k in args.counts) or any(not 1 <= k <= 128 for k in args.pools) or any(g < 16 for g in args.grids):
        parser.error('nonnegative native index; counts>=3; pool in 1..128; grid>=16')
    rows=[case(count,317,args.native_j,tau,pool,args.grids)
          for count in args.counts for tau in (Fraction(1,4),Fraction(3,4),Fraction(99,100))
          for pool in args.pools]
    completed=[r for r in rows if r['status']=='complete_product_inventory_model']
    sources={}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    for file in (Path(__file__),Path('RiemannGaussian/ZetaRieszInsertionCapacity.lean'),
                 Path('RiemannGaussian/ZetaRieszCenteredInsertionPayment.lean'),
                 Path('scripts/probe_riesz_clipped_insertions.py'),
                 Path('scripts/probe_riesz_generic_patterns.py'),Path('scripts/riesz_subset_moments.py')):
        data=file.read_bytes();sha=hashlib.sha256(data).hexdigest()
        snapshot=args.output.parent/f'source-{sha}{file.suffix}';snapshot.write_bytes(data)
        sources[str(file)]=dict(sha256=sha,snapshot=str(snapshot))
    summary=dict(families=len(rows),completeUnpaidModelFamilies=len(completed),
                 skippedBeforeCoefficientWork=len(rows)-len(completed),
                 independentExactSignedRegressions=sum('independentSignedEnumeration' in r for r in completed),
                 everyCompletedModelHasPositiveResidual=True,nativeFloorCredit=False)
    report=dict(schemaVersion=1,head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
                sources=sources,summary=summary,families=rows,
                scope=dict(optionalOutsideBuildsCI=True,unpaidGuardBeforeCoefficientWork=True,
                           completeFiniteCountRange=True,virtualLogsNotActualPrimeInventory=True,
                           exactRationalProductWeights=True,fullPhaseRetainedInEqualLogModel=True,
                           nativeSupportChecksIntervalCertified=False,
                           allocationNotSilentlySetToZero=True,fullAllocatedTransportEvaluated=False,
                           sourceBudgetOrNativePopulationCertified=False))
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    main()

#!/usr/bin/env python3
"""Joined clipped-hinge transport in the UNPAID many-bin log models.

Optional local research, outside builds/CI. Every model keeps the moving
length, original count/physical/allocation conditions, total-log factorial
kernel and full complex phase. All subsets are represented by the exact
signed recursion. Paid/out-of-support inputs are rejected before it runs.

The finite candidate inventory and fractional weights are CONSTRUCTED
models. Neither prime existence/density nor whole-population matching
capacity follows from them. No source-scale floor payment is claimed.
"""

import argparse
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
import mpmath as mp

from probe_riesz_generic_patterns import (
    actual_bins, allocation_enclosure, finite_number, generic_unpaid_record,
    native_parameters, record_context, unpaid_scope,
)
from riesz_subset_moments import SubsetMoments, binary_fraction


def text_number(x):
    return mp.nstr(finite_number(x), 28)


def subset_response(logs, left, right, budget):
    """Exact cutoffs as rational linear combinations of the supplied logs.

    Do NOT round a tiny total-log mismatch to zero. The existing backend's
    integer-coordinate recursion accepts these exact rational cutoffs.
    Failure to finish leaves the response unresolved, never guessed.
    """
    profile = SubsetMoments(logs, grid=1, recursion_budget=budget)
    a, aa = profile.recursive_response(left/profile.unit)
    b, ab = profile.recursive_response(right/profile.unit)
    complete = aa['complete'] and ab['complete']
    return ((a-b)*profile.unit if complete else None), dict(
        complete=complete, representedSubsets=str(2**len(logs)),
        left=aa, right=ab, cutoffsRounded=False)


def scope_context(pars, owner, cofactors):
    total = mp.fsum([owner, *cofactors])
    logs = [owner, *cofactors]
    L, N = pars['length'], pars['N']
    bins, cap = actual_bins(cofactors, N)
    rough = [x for x in logs if x > 2*mp.log(N)]
    mask = dict(
        coreWindow=mp.mpf('1.95')*N < total <= mp.mpf('2.03')*N,
        squarefreeDistinctLogModel=len(set(logs)) == len(logs),
        canonicalLargestOwner=owner > max(cofactors),
        nonDominant=owner < mp.mpf('.65')*total,
        allPhysicalUpper=max(logs) < L,
        allPhysicalRough=min(logs) > 2*mp.log(N),
        roughCountAtLeastTwo=len(rough) >= 2,
        smoothMassBelowLength=mp.fsum(x for x in logs if x not in rough) < L,
        narrowWindow=L < total < 2*L,
        cofactorAboveTrial=min(total-x for x in logs) > pars['logTrial'],
        originalCount=3 <= len(logs) < pars['originalCountCeiling'],
        reducedNativeCount=3 <= len(logs) < pars['currentCountCeiling'])
    scope = unpaid_scope(pars, cofactors, owner, total, bins, cap, mask)
    return total, dict(wholeCount=len(logs), occupiedBins=len(bins),
                       fewBinCeiling=cap, masks={k: bool(v) for k,v in mask.items()},
                       unpaidScope=scope, subsetCalculationPerformed=False)


def inner_model(count, seed, j, tau_ratio):
    anchor = generic_unpaid_record(count, seed, j)
    pars, _, xs, P, T, *_ = record_context(anchor)
    i = xs.index(max(xs))
    base = xs[:i]+xs[i+1:]
    ratio = finite_number(tau_ratio)
    scale = (pars['length']-P)/(mp.fsum(base)-ratio*min(base))
    base = [x*scale for x in base]
    tau = ratio*min(base)
    Q = T-pars['length']-tau
    return pars, P, Q, base


def family(count, seed, j, tau_ratio, gap, heights, budget):
    pars, P, Q, base = inner_model(count, seed, j, tau_ratio)
    L, N = pars['length'], pars['N']
    _, original = scope_context(pars, P, [Q, *base])
    row = dict(cofactorCount=count, nativeIndex=j, N=str(N), seed=seed,
               tauToBaseHead=str(tau_ratio), inputGap=text_number(gap),
               eventualCountPaymentRegime=j >= 1024, original=original,
               primePopulation=False, nativeFloorCredit=False)
    if not original['unpaidScope']['eligible']:
        row['status'] = 'skipped_before_subset_calculation'
        return row
    p, q, length = map(binary_fraction, [P, Q, L])
    bs = list(map(binary_fraction, base))
    B, head = sum(bs), min(bs)
    tau = p+B-length
    T = p+q+B
    assert q+B <= length and B <= T-length and 0 <= tau <= head
    row['innerGeometryExactForSuppliedLogs'] = True
    row['tauOverTotalLog'] = text_number(tau/T)
    row['lengthRoundingLogBound'] = text_number(pars['lengthErrorLog'])
    mu = (-1)**len(base)
    value, audit = subset_response([Q, *base], length-p, length, budget)
    original['subsetCalculationPerformed'] = True
    original['recursion'] = audit
    if value is None:
        row['status'] = 'unresolved_original'
        return row
    assert value == mu*tau
    original['exactClippedIdentityVerified'] = True
    original['allocation'] = allocation_enclosure(pars, [P, Q, *base], finite_number(T))
    candidates = []
    signs = (-1, 1) if gap else (0,)
    for ratio, sign in itertools.product(
            (Fraction(1,4), Fraction(1,2), Fraction(3,4), Fraction(3,2)), signs):
        R = finite_number(tau*ratio)
        newP = P-R+sign*gap
        total, context = scope_context(pars, newP, [Q, R, *base])
        item = dict(insertedLogOverTau=str(ratio), gapSign=sign, context=context)
        candidates.append(item)
        if not context['unpaidScope']['eligible']:
            item['status'] = 'skipped_before_subset_calculation'
            continue
        pp, rr = map(binary_fraction, [newP, R])
        newT = pp+q+rr+B
        newTau = pp+rr+B-length
        geometry = (q+rr+B <= length and rr+B <= newT-length and
                    0 <= newTau <= head)
        item['innerGeometryExactForSuppliedLogs'] = geometry
        if not geometry:
            item['status'] = 'outside_clipped_geometry'
            continue
        clip = min(newTau, rr)
        value, audit = subset_response([Q, R, *base], length-pp, length, budget)
        context['subsetCalculationPerformed'] = True
        context['recursion'] = audit
        if value is None:
            item['status'] = 'unresolved_candidate'
            continue
        assert value == -mu*clip
        item.update(status='verified', exactClippedIdentityVerified=True,
                    actualTotalLogGap=text_number(newT-T),
                    clipOverOriginalTau=text_number(clip/tau),
                    oldInsertedInnerHingeWouldFail=bool(newTau > rr),
                    allocation=allocation_enclosure(pars, [newP,Q,R,*base], total))
        item['_clip'], item['_gap'], item['_T'] = clip, newT-T, newT
    row['candidates'] = candidates
    if any(c.get('status') != 'verified' for c in candidates):
        row['status'] = 'incomplete_family_no_cost_claim'
        for c in candidates:
            for key in ('_clip','_gap','_T'):
                c.pop(key, None)
        return row
    # This is a constructed finite inventory, NOT a native capacity proof.
    if gap:
        # Fund each two-sided MODEL pair so its exact first log-gap moment
        # is zero. The finite-binary gaps need not be perfectly symmetric.
        # Existence of native pairs on both sides remains an open obligation.
        coefficients = []
        for minus, plus in zip(candidates[::2], candidates[1::2]):
            dm, dp = minus['_gap'], plus['_gap']
            assert dm < 0 < dp
            coefficients += [tau/4*dp/(dp-dm), tau/4*(-dm)/(dp-dm)]
    else:
        beta = tau/sum(c['_clip'] for c in candidates)
        coefficients = [beta*c['_clip'] for c in candidates]
    betas = [coeff/c['_clip'] for c,coeff in zip(candidates,coefficients)]
    assert all(0 <= beta <= 1 for beta in betas)
    assert sum(coefficients) == tau
    moment = sum(coeff*c['_gap'] for c,coeff in zip(candidates,coefficients))
    if gap:
        assert moment == 0
    # Increase precision for exact sum/difference conversion and phase use.
    # The supplied finite-binary logs and their exact response are unchanged.
    mp.mp.prec += 128
    phase_rows = []
    for y in heights:
        F = mu*mp.exp(-1j*y*finite_number(T))
        transport = mp.mpc(0)
        separate = mp.mpf(0)
        Gs = []
        first_gap_moment = Fraction(0)
        for c, coeff in zip(candidates, coefficients):
            delta = finite_number(c['_gap'])
            amplitude = mp.exp((N+1)*mp.log1p(delta/finite_number(T))-mp.mpf('1.5')*delta)
            G = F*amplitude*mp.exp(-1j*y*delta)
            normalized_c = finite_number(coeff/tau)
            transport += normalized_c*(F-G)
            separate += normalized_c*abs(F-G)
            Gs.append(G)
            first_gap_moment += coeff*c['_gap']
        phase_rows.append(dict(
            height=y, originalUnweightedReal=text_number(F.real),
            negativeOriginal=bool(F.real <= 0),
            everyInsertedUnweightedPhaseFavorable=all(G.real <= 0 for G in Gs),
            joinedTransportOverOriginalMagnitude=text_number(abs(transport)),
            separateTransportOverOriginalMagnitude=text_number(separate),
            joinedToSeparateTransport=text_number(abs(transport)/separate) if separate else None,
            combinedUnallocatedRealOverOriginalMagnitude=text_number(transport.real),
            weightedGapMomentOverTau=text_number(first_gap_moment/tau),
            fullFactorialAmplitudeRatioRetained=True, phaseFrozen=False,
            transportUsesUnallocatedSmoothAmplitude=True,
            originalAllocationEnclosureRetained=True,
            fullAllocatedTransportEvaluated=False,
            allocationBoundsReportedSeparately=True, intervalCertified=False))
    for c in candidates:
        for key in ('_clip','_gap','_T'):
            c.pop(key)
    row.update(status='complete_model_family',
               constructedFundingPerCandidate=[text_number(beta) for beta in betas],
               finiteModelCoverageExact=True, globalPartnerCapacityProved=False,
               firstTotalLogGapMomentExactlyZero=moment == 0,
               actualPrimePartnersProved=False, phaseRows=phase_rows,
               aggregatePrimeMassBound=False, floorProved=False)
    return row


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--counts', type=int, nargs='+', default=[55,56,63,64],
                   help='cofactor count; whole count adds one owner')
    p.add_argument('--seeds', type=int, nargs='+', default=[317])
    p.add_argument('--native-j', type=int, default=1024)
    p.add_argument('--recursion-budget', type=int, default=32768)
    p.add_argument('--heights', type=int, nargs='+', default=[54,65,100])
    p.add_argument('--output', type=Path, default=Path('.lake/riesz-clipped-insertion/scan.json'))
    args = p.parse_args()
    if args.native_j < 0 or any(c < 3 for c in args.counts) or args.recursion_budget < 0:
        p.error('nonnegative native index/budget and cofactor counts>=3 required')
    if any(y < 54 for y in args.heights):
        p.error('retain fixed heights>=54')
    rows = []
    for count, seed, tau, gap in itertools.product(
            args.counts, args.seeds, (Fraction(1,4),Fraction(3,4),Fraction(99,100)),
            ('0','0.001','0.000001')):
        # Initialize sufficient precision BEFORE constructing the gap.
        native_parameters(args.native_j, .50005)
        rows.append(family(count, seed, args.native_j, tau, mp.mpf(gap),
                           args.heights, args.recursion_budget))
    complete = [r for r in rows if r['status'] == 'complete_model_family']
    phases = [v for r in complete for v in r['phaseRows']]
    old_failures = sum(c['oldInsertedInnerHingeWouldFail'] for r in complete for c in r['candidates'])
    output = args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    sources = {}
    for file in (Path(__file__), Path('scripts/probe_riesz_generic_patterns.py'),
                 Path('scripts/riesz_subset_moments.py'),
                 Path('RiemannGaussian/ZetaRieszClippedInsertionFloor.lean')):
        data = file.read_bytes()
        sha = hashlib.sha256(data).hexdigest()
        snapshot = output.parent/f'source-{sha}{file.suffix}'
        snapshot.write_bytes(data)
        sources[str(file)] = dict(sha256=sha,snapshot=str(snapshot))
    summary = dict(families=len(rows), completeModelFamilies=len(complete),
                   skippedBeforeSubsetCalculation=sum(r['status']=='skipped_before_subset_calculation' for r in rows),
                   unfinishedFamilies=len(rows)-len(complete)-sum(r['status']=='skipped_before_subset_calculation' for r in rows),
                   exactClippedInsertions=sum(len(r['candidates']) for r in complete),
                   formerlyExcludedShortInsertions=old_failures,
                   negativeOriginalPhaseCases=sum(v['negativeOriginal'] for v in phases),
                   nativePrimeMatchingOrFloorCertified=False)
    report = dict(schemaVersion=1, head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
                  sources=sources, summary=summary, families=rows,
                  scope=dict(optionalOutsideBuildsCI=True, unpaidGuardBeforeSubsetCalculation=True,
                             continuousLogModelsNotPrimes=True, arbitraryFractionalInventory=True,
                             movingLengthAndOriginalMasks=True, sourceBudget=False,
                             discardedUnknownSubsets=False, fixedHeightFullPhase=True))
    output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__ == '__main__':
    main()

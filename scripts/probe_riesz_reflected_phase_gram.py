#!/usr/bin/env python3
"""Optional native-mask finite-subset signed Gram diagnostic.

Construct distinct probable prime factors with known products on the native
N=256/640 schedules. Retain the actual moving length, core mask, allocation
and phase. Select adverse cutoffs ONCE using the entire constructed subset,
not the unavailable full core. Sum divisor intervals BEFORE inspecting the
Gram. Divisor reflection is checked on every interval.

This is a floating regression on a tiny constructed SUBSET of the core.
It is not population sampling, a large-prime certificate, a cofinal energy
bound or a floor. The original growing-count/many-bin frontier is not tested.
No squarefree or prime-density approximation generates the labels.
"""

import argparse
from collections import defaultdict
from fractions import Fraction
import json
import math
from pathlib import Path
import random
import time

import mpmath as mp
import numpy as np
from sympy import isprime, nextprime

from probe_riesz_canonical_joint import allocation, core_mask
from probe_riesz_fixed_count_period import unpaid_orders


def factor_divisors(primes):
    rows = [(1, 1)]
    for p in primes:
        rows += [(d*p, -sign) for d, sign in list(rows)]
    return sorted(rows)


def native_subset(order, count_ceiling, samples, seed):
    # The older small-order sampler also constructs floating integer-bin
    # endpoints; those overflow at N=640. No bin endpoints are needed here.
    cutoff = 20000**order // (10001**order * (order+1))
    physical = (cutoff+2)**2
    length = math.log(physical)
    u = mp.mpf(10001)/20000
    tilt = 1/(-2*mp.log(u))
    log_rate = (2-2*tilt)*mp.log(u)-mp.log(tilt)
    trial = min(int(mp.exp(-order*log_rate/(2*(tilt+mp.mpf('2.5'))))), cutoff+1)
    pars = dict(N=order, physical=physical, length=length, trial=trial,
                orders=unpaid_orders(order).tolist())
    rng = random.Random(seed)
    rows = []
    for i in range(samples):
        count = 3+i % min(count_ceiling-3, 8)
        total = order*(1.955+.07*(i+.5)/samples)
        owner_share = .35+.2*((i//3) % 5)/4
        rest = np.array([.5+rng.random() for _ in range(count-1)])
        shares = [(1-owner_share)*float(v/rest.sum()) for v in rest]
        shares.append(owner_share)
        primes = [int(nextprime(int(mp.exp(mp.mpf(str(total*x)))))) for x in shares]
        assert len(set(primes)) == count
        assert all(isprime(p) for p in primes)
        label = math.prod(primes)
        factors = {p: 1 for p in primes}
        assert core_mask(order, label, factors, pars, count_ceiling) == 'core'
        logs = [math.log(p) for p in primes]
        true_total = math.log(label)
        assigned = math.fsum(allocation(order, pars['orders'], 1-v/true_total)
                             for p, v in zip(primes, logs)
                             if order**2 < p < pars['physical'])
        assert -.00000001 <= assigned <= 1.00000001
        unassigned = max(1-assigned, 0.)
        log_amplitude = ((order+1)*math.log(float(Fraction(10001, 20000)))
                         -1.5*true_total+(order+1)*math.log(true_total)
                         -math.lgamma(order+1)-math.log(pars['length'])
                         +math.log(unassigned))
        rows.append(dict(label=label, primes=primes, logs=logs, count=count,
                         mu=(-1)**count, total=true_total,
                         log_amplitude=log_amplitude, assigned=assigned,
                         divisors=factor_divisors(primes)))
    assert len({r['label'] for r in rows}) == samples
    return pars, rows


def span(a, b):
    # psi(b)-psi(a) equals this expression up to <1/(12*a^2).
    # That endpoint is enormous here; floats are still NOT a certificate.
    return float(mp.log(mp.mpf(b)/a)+(mp.mpf(1)/a-mp.mpf(1)/b)/2)


def experiment(order, count_ceiling, samples, seed, heights):
    start = time.monotonic()
    pars, rows = native_subset(order, count_ceiling, samples, seed)
    physical, endpoint = pars['physical'], max(r['label'] for r in rows)
    events = defaultdict(list)
    columns = np.zeros(samples, dtype=np.int32)
    for i, row in enumerate(rows):
        for d, sign in row['divisors']:
            if d < physical:
                columns[i] += sign
            elif d < endpoint:
                events[d].append((i, sign))
    points = sorted({physical, endpoint, *events})
    logs = np.array([r['total'] for r in rows])
    mus = np.array([r['mu'] for r in rows])
    counts = np.array([r['count'] for r in rows])
    max_log_amplitude = max(r['log_amplitude'] for r in rows)
    amplitudes = np.exp([r['log_amplitude']-max_log_amplitude for r in rows])
    cosines = np.cos(np.array(heights)[:, None]*logs[None, :])
    weights = -amplitudes[None, :]*cosines
    grams = np.zeros((len(heights), samples, samples))
    joined = np.zeros(len(heights))
    profiles = np.zeros(len(heights))
    atomic_costs = np.zeros(len(heights))
    period_blocks = [defaultdict(float) for _ in heights]
    reflection_checks = 0
    # Sparse actual divisor intervals, not an exponentially large integer loop.
    for a, b in zip(points, points[1:]):
        for i, sign in events.get(a, []):
            columns[i] += sign
        for i, row in enumerate(rows):
            reflected_cut = (row['label']-1)//a
            small = sum(sign for d, sign in row['divisors'] if d <= reflected_cut)
            assert int(columns[i]) == -row['mu']*small
            reflection_checks += 1
        harmonic = span(a, b)
        increment_log = math.log(b)-math.log(a)
        correlations = weights @ columns
        joined -= correlations*increment_log
        atomic_costs += np.maximum(correlations, 0.)*increment_log
        outer = np.outer(columns, columns)
        for h, correlation in enumerate(correlations):
            # Join the ENTIRE signed correlation before any clipping. This
            # uses its piecewise-constant interpolation in log(k); integer
            # period-boundary rounding is not certified by this probe.
            period = 2*math.pi/abs(heights[h])
            left, right = math.log(a), math.log(b)
            while left < right:
                block = math.floor(left/period)
                edge = min(right, (block+1)*period)
                if edge <= left:
                    block += 1
                    edge = min(right, (block+1)*period)
                period_blocks[h][block] -= correlation*(edge-left)
                left = edge
            if correlation > 0:
                grams[h] += harmonic*outer
                profiles[h] += harmonic  # difference from exact price <=O(1/physical)
    # Independent original divisor atom regression.
    responses = np.array([math.fsum(sign*max(pars['length']-math.log(d), 0.)
                                    for d, sign in r['divisors']) for r in rows])
    direct = weights @ responses
    regression = float(np.max(np.abs(joined-direct)))
    assert regression < 1e-7*max(1., float(np.max(np.abs(direct))))
    gap = logs[:, None]-logs[None, :]
    labels = [r['label'] for r in rows]
    gcd_small = np.array([[math.log(math.gcd(n, m)) <= order/1000
                          for m in labels] for n in labels])
    distance = np.array([[abs(n-m)/min(n, m) for m in labels] for n in labels])
    distinct = ~np.eye(samples, dtype=bool)
    separated = distinct & gcd_small & (distance > math.exp(-order/1000))
    cases = []
    for i, height in enumerate(heights):
        g, cos = grams[i], cosines[i]
        phase_product = cos[:, None]*cos[None, :]
        mass = amplitudes[:, None]*amplitudes[None, :]*g
        cross = mass*phase_product
        old_width = math.exp(-order/1000)/(1+abs(height))
        periods = np.rint(height*gap/(2*math.pi))
        old_orbit = np.abs(gap-2*math.pi*periods/height) <= old_width
        base = separated & ~old_orbit
        width = math.exp(-order/10000)/(1+abs(height))
        odd = np.rint((height*gap-math.pi)/(2*math.pi))
        anti = np.abs(gap-(2*odd+1)*math.pi/height) <= width
        wide_aligned = np.abs(gap-2*math.pi*periods/height) <= width
        favorable_positive = base & (g >= 0) & (phase_product < 0)
        favorable_negative = base & (g < 0) & (phase_product > 0)
        anti_credit_edges = base & (g >= 0) & anti
        aligned_negative_edges = base & (g < 0) & wide_aligned
        square_sum = (cos[:, None]**2+cos[None, :]**2)/2
        anti_reserve = float(np.sum((mass*square_sum)[anti_credit_edges]))
        aligned_reserve = float(np.sum((-mass*square_sum)[aligned_negative_edges]))
        anti_leak = float(np.sum((mass*(cos[:, None]+cos[None, :])**2/2)[anti_credit_edges]))
        aligned_leak = float(np.sum((-mass*(cos[:, None]-cos[None, :])**2/2)[aligned_negative_edges]))
        total_favorable = -float(np.sum(cross[favorable_positive | favorable_negative]))
        reinforcing = float(np.sum(cross[base & ~(favorable_positive | favorable_negative)]))
        remaining = float(np.sum(cross[base]))
        assert abs(remaining-reinforcing+total_favorable) < 1e-8*max(1., abs(remaining))
        abs_mass = np.abs(mass)
        gauge_coherent = base & (mus[:, None]*mus[None, :]*g >= 0)
        denominator = float(np.sum(abs_mass[base]))
        period_total = math.fsum(period_blocks[i].values())
        period_cost = math.fsum(max(-value, 0.) for value in period_blocks[i].values())
        tolerance = 1e-7*max(1., atomic_costs[i])
        assert abs(period_total-joined[i]) <= tolerance
        assert period_cost >= max(-joined[i], 0.)-tolerance
        assert period_cost <= atomic_costs[i]+tolerance
        cases.append(dict(N=order, height=height, labels=samples,
                          countsPresent=sorted({r['count'] for r in rows}),
                          sourceAmplitudeLogScale=max_log_amplitude,
                          scaledJoinedReal=float(joined[i]),
                          scaledAtomicCutoffCost=float(atomic_costs[i]),
                          scaledJoinedLogPeriodCost=period_cost,
                          logPeriodCancellationFraction=1-period_cost/atomic_costs[i]
                              if atomic_costs[i] else None,
                          scaledPostHingeAdverseProfile=float(profiles[i]),
                          retainedOrderedPairs=int(np.count_nonzero(base)),
                          scaledRemainingEnergy=remaining,
                          scaledReinforcingEnergy=reinforcing,
                          scaledTotalFavorableCredit=total_favorable,
                          scaledPositiveGramAntiphaseCredit=anti_reserve,
                          scaledNegativeGramAlignedCredit=aligned_reserve,
                          scaledAntiphaseLeakage=anti_leak,
                          scaledAlignedLeakage=aligned_leak,
                          antiphaseFractionOfAllFavorableCredit=(anti_reserve-anti_leak)/total_favorable
                              if total_favorable else None,
                          alignedNegativeFractionOfAllFavorableCredit=(aligned_reserve-aligned_leak)/total_favorable
                              if total_favorable else None,
                          moebiusGaugeFractionOfAbsoluteGramMass=float(np.sum(abs_mass[gauge_coherent]))/denominator
                              if denominator else None,
                          favorableDifferentCountEnergy=-float(np.sum(cross[
                              (favorable_positive | favorable_negative)
                              & (counts[:, None] != counts[None, :])])),
                          favorableOppositeParityEnergy=-float(np.sum(cross[
                              (favorable_positive | favorable_negative)
                              & (mus[:, None]*mus[None, :] == -1)])),
                          originalMasksNumericallyChecked=True,
                          fullCorePopulationUsed=False))
    return dict(order=order, nativeCountCeiling=count_ceiling, seed=seed, samples=samples,
                seconds=time.monotonic()-start, divisorIntervals=len(points)-1,
                exactIntegerReflectionChecks=reflection_checks,
                originalDivisorRegressionAbsoluteError=regression,
                cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[256, 640])
    parser.add_argument('--samples', type=int, default=24)
    parser.add_argument('--heights', type=float, nargs='+', default=[54, 65, 100])
    parser.add_argument('--seed', type=int, default=20261002)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if any(n not in (256, 640) for n in args.orders) or args.samples < 8:
        parser.error('only native orders256/640 and at least8 labels are supported')
    mp.mp.dps = 80
    rows = []
    for n in args.orders:
        row = experiment(n, 8 if n == 256 else 16, args.samples, args.seed, args.heights)
        rows.append(row)
        print(json.dumps({k:row[k] for k in ['order','seconds','divisorIntervals',
                                           'exactIntegerReflectionChecks']}), flush=True)
    report = dict(scope=__doc__, nativeOrdersUsed=True,
                  fullPopulationOrDensityEstimate=False, lowCountsOnly=True,
                  negativeCutoffsSelectedOnSubsetNotFullCore=True,
                  eventualLeanOrderThresholdSatisfied=False,
                  actualAmplitudesRescaledByCommonPositiveFactor=True,
                  cutoffPeriodSplittingUsesLogInterpolation=True,
                  formalPrimeCertificate=False, rigorousIntervalArithmetic=False,
                  sourceScalePopulationBound=False, floorProved=False, rows=rows)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()

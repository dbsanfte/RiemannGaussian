#!/usr/bin/env python3
"""Optional complete finite-universe count/coprime correlation diagnostic.

Enumerate EVERY squarefree subset of each of two disjoint, explicitly
constructed probable-prime universes. Apply the original core masks,
factorial allocation and phase. Select adverse cutoffs once on the entire
retained population, then integrate its joined signed prefix and Gram.

This finite population is NOT the full core or a density sample. Native
orders 256/640 are below the eventual estimates' threshold; the eventual
K/864 crop is not applied prematurely. Common amplitude rescaling and log
interpolation are used, so no source-scale numerical floor is certified.
"""

import argparse
from collections import Counter, defaultdict
import itertools
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
from probe_riesz_reflected_phase_gram import factor_divisors, span


LEVELS = [.025, .04, .06, .085, .12, .17, .24, .32, .43, .62, .655, .68]


def population(order, count_ceiling, seed):
    cutoff = 20000**order // (10001**order * (order+1))
    physical = (cutoff+2)**2
    u = mp.mpf(10001)/20000
    tilt = 1/(-2*mp.log(u))
    log_rate = (2-2*tilt)*mp.log(u)-mp.log(tilt)
    trial = min(int(mp.exp(-order*log_rate/(2*(tilt+mp.mpf('2.5'))))), cutoff+1)
    pars = dict(N=order, physical=physical, length=math.log(physical), trial=trial,
                orders=unpaid_orders(order).tolist())
    rng, rows, excluded, universes = random.Random(seed), [], Counter(), []
    for pool in range(2):
        levels = [v+rng.uniform(-.0015, .0015) for v in LEVELS]
        primes = [int(nextprime(int(mp.exp(mp.mpf(str(order*v)))))) for v in levels]
        assert len(set(primes)) == len(primes) and all(isprime(p) for p in primes)
        assert all(math.log(p) > order/4096 for p in primes)
        # Two retained labels in the SAME pool cannot be coprime: their
        # combined log exceeds the entire universe's log. Hence coprime
        # cross terms are precisely the cross-pool terms, before old masks.
        assert math.log(math.prod(primes)) < 3.9*order
        universes.append(primes)
        for count in range(3, min(count_ceiling, len(primes)+1)):
            for factors in itertools.combinations(primes, count):
                label = math.prod(factors)
                mask = core_mask(order, label, dict.fromkeys(factors, 1), pars, count_ceiling)
                if mask != 'core':
                    excluded[mask] += 1
                    continue
                total = math.log(label)
                assigned = math.fsum(allocation(order, pars['orders'], 1-math.log(p)/total)
                                     for p in factors if order**2 < p < physical)
                assert -.00000001 <= assigned <= 1.00000001
                unassigned = max(1-assigned, 0.)
                if not unassigned:
                    excluded['zero_unassigned'] += 1
                    continue
                log_amplitude = ((order+1)*math.log(float(u))-1.5*total
                                 +(order+1)*math.log(total)-math.lgamma(order+1)
                                 -math.log(pars['length'])+math.log(unassigned))
                rows.append(dict(label=label, factors=factors, total=total,
                                 count=count, pool=pool, mu=(-1)**count,
                                 divisors=factor_divisors(factors),
                                 log_amplitude=log_amplitude))
    assert set(universes[0]).isdisjoint(universes[1])
    assert rows and len({r['label'] for r in rows}) == len(rows)
    return pars, rows, excluded


def pair_gram(nrow, mrow, physical, endpoint, cumulative):
    """Exact divisor-prefix steps, integrated against joined adverse mass.

    cumulative maps integer event endpoints to the common adverse harmonic
    integral; it never reselects adverse cutoffs for this pair/count.
    """
    events = defaultdict(lambda: [0, 0])
    cn = cm = 0
    for side, row in enumerate([nrow, mrow]):
        for d, sign in row['divisors']:
            if d < physical:
                if side == 0:
                    cn += sign
                else:
                    cm += sign
            elif d < endpoint:
                events[d][side] += sign
    points = sorted({physical, endpoint, *events})
    answer = np.zeros_like(cumulative[physical])
    for a, b in zip(points, points[1:]):
        dn, dm = events[a]
        cn, cm = cn+dn, cm+dm
        answer += cn*cm*(cumulative[b]-cumulative[a])
    return answer


def experiment(order, seed, heights):
    started = time.monotonic()
    ceiling = {256: 8, 640: 16, 1536: 32}[order]
    pars, rows, excluded = population(order, ceiling, seed)
    physical, endpoint = pars['physical'], max(r['label'] for r in rows)
    counts = sorted({r['count'] for r in rows})
    counts_index = {c: i for i, c in enumerate(counts)}
    scale = max(r['log_amplitude'] for r in rows)
    amplitude = np.exp([r['log_amplitude']-scale for r in rows])
    weights = -amplitude[None, :]*np.cos(np.array(heights)[:, None]
                                       *np.array([r['total'] for r in rows]))
    hcount, ncount = len(heights), len(counts)
    events = defaultdict(list)
    columns = np.zeros(len(rows), dtype=np.int32)
    for i, row in enumerate(rows):
        for d, sign in row['divisors']:
            if d < physical:
                columns[i] += sign
            elif d < endpoint:
                events[d].append((i, sign))
    points = sorted({physical, endpoint, *events})
    pool_count_phi = np.zeros((hcount, 2, ncount))
    for i, row in enumerate(rows):
        pool_count_phi[:, row['pool'], counts_index[row['count']]] += weights[:, i]*columns[i]
    joined, atomic, adverse_mass = (np.zeros(hcount) for _ in range(3))
    full_energy, diagonal = np.zeros(hcount), np.zeros(hcount)
    diagonal_value = np.sum((weights*columns[None, :])**2, axis=1)
    coprime_count_gram = np.zeros((hcount, ncount, ncount))
    complete_count_gram = np.zeros_like(coprime_count_gram)
    cumulative, blocks = {}, [defaultdict(float) for _ in heights]
    balanced_triples = [i for i, row in enumerate(rows) if row['count'] == 3
                        and row['total']-math.log(min(row['factors'])) < pars['length']]
    balanced_energy = np.zeros(hcount)
    for a, b in zip(points, points[1:]):
        for i, sign in events.get(a, []):
            old = columns[i]
            columns[i] += sign
            pool_count_phi[:, rows[i]['pool'], counts_index[rows[i]['count']]] += weights[:, i]*sign
            diagonal_value += weights[:, i]**2*(columns[i]**2-old**2)
        cumulative[a] = adverse_mass.copy()
        count_phi = pool_count_phi.sum(axis=1)
        phi = count_phi.sum(axis=1)
        lo, hi = math.log(a), math.log(b)
        width, harmonic = hi-lo, span(a, b)
        joined -= phi*width
        atomic += np.maximum(phi, 0.)*width
        adverse = phi > 0
        mass = harmonic*adverse
        adverse_mass += mass
        full_energy += mass*phi**2
        diagonal += mass*diagonal_value
        complete_count_gram += mass[:, None, None]*np.einsum('hc,hd->hcd', count_phi, count_phi)
        coprime_count_gram += mass[:, None, None]*(
            np.einsum('hc,hd->hcd', pool_count_phi[:, 0], pool_count_phi[:, 1])
            +np.einsum('hc,hd->hcd', pool_count_phi[:, 1], pool_count_phi[:, 0]))
        if balanced_triples:
            psi = np.sum(weights[:, balanced_triples]*columns[None, balanced_triples], axis=1)
            balanced_energy += mass*psi**2
        for ih, height in enumerate(heights):
            period = 2*math.pi/abs(height)
            left = lo
            while left < hi:
                block = math.floor(left/period)
                right = min(hi, (block+1)*period)
                if right <= left:
                    block, right = block+1, min(hi, (block+2)*period)
                blocks[ih][block] -= phi[ih]*(right-left)
                left = right
    cumulative[endpoint] = adverse_mass.copy()
    assert np.allclose(complete_count_gram.sum(axis=(1, 2)), full_energy)
    raw_coprime = coprime_count_gram.sum(axis=(1, 2))
    removed, removal_counts = np.zeros(hcount), np.zeros(hcount, dtype=int)
    removed_count_gram = np.zeros_like(coprime_count_gram)
    for i, row in enumerate(rows):
        for m in range(i+1, len(rows)):
            other = rows[m]
            if row['pool'] == other['pool']:
                assert math.log(math.gcd(row['label'], other['label'])) > order/4096
                continue
            assert math.gcd(row['label'], other['label']) == 1
            gap = row['total']-other['total']
            near = abs(row['label']-other['label'])/min(row['label'], other['label']) <= math.exp(-order/1000)
            masks = np.array([near or abs(gap-2*math.pi*round(height*gap/(2*math.pi))/height)
                              <= math.exp(-order/1000)/(1+abs(height)) for height in heights])
            if not masks.any():
                continue
            gram = pair_gram(row, other, physical, endpoint, cumulative)
            half = weights[:, i]*weights[:, m]*gram*masks
            removed += 2*half
            ci, cm = counts_index[row['count']], counts_index[other['count']]
            removed_count_gram[:, ci, cm] += half
            removed_count_gram[:, cm, ci] += half
            removal_counts += 2*masks
    remaining_count_gram = coprime_count_gram-removed_count_gram
    assert np.allclose(remaining_count_gram.sum(axis=(1, 2)), raw_coprime-removed)
    literal = weights @ np.array([math.fsum(sign*max(pars['length']-math.log(d), 0.)
                                           for d, sign in r['divisors']) for r in rows])
    assert np.allclose(joined, literal, rtol=1e-8, atol=1e-7)
    cases = []
    for ih, height in enumerate(heights):
        split = float(np.trace(complete_count_gram[ih]))
        coprime = float(raw_coprime[ih])
        retained_same_count = float(np.trace(remaining_count_gram[ih]))
        retained_all_counts = float(np.sum(remaining_count_gram[ih]))
        block_cost = math.fsum(max(-value, 0.) for value in blocks[ih].values())
        cases.append(dict(height=height, rescaledLiteralJoined=float(joined[ih]),
                          rescaledAtomicCost=float(atomic[ih]), rescaledPeriodCost=block_cost,
                          rescaledWholeAdverseEnergy=float(full_energy[ih]),
                          rescaledCountDiagonalEnergy=split,
                          joinedToSeparateCountEnergyRatio=float(full_energy[ih])/split if split else None,
                          rescaledSignedCrossCountEnergy=float(full_energy[ih])-split,
                          rescaledLabelDiagonalEnergy=float(diagonal[ih]),
                          rescaledRawCoprimeEnergy=coprime,
                          rescaledOldMaskRemoval=float(removed[ih]),
                          rescaledRemainingSmallGcdEnergy=coprime-float(removed[ih]),
                          rescaledRemainingSameCountContribution=retained_same_count,
                          rescaledRemainingCrossCountContribution=retained_all_counts-retained_same_count,
                          removedOrderedCoprimePairs=int(removal_counts[ih]),
                          rescaledBalancedTripleEnergy=float(balanced_energy[ih]),
                          counts=counts, rescaledCompleteCountGram=complete_count_gram[ih].tolist(),
                          rescaledCoprimeCountGram=coprime_count_gram[ih].tolist(),
                          rescaledRemainingCountGram=remaining_count_gram[ih].tolist()))
    return dict(N=order, seed=seed, nativeOriginalCountCeiling=ceiling,
                prematurelyApplyingEventualCountCrop=False, primeUniverseSize=len(LEVELS),
                pools=2, selectedLabels=len(rows), counts=sorted(counts),
                labelsByCount=dict(Counter(r['count'] for r in rows)), excludedMasks=dict(excluded),
                allSubsetsInChosenUniversesEnumerated=True, sourceAmplitudeLogScale=scale,
                balancedTripleLabels=len(balanced_triples), divisorIntervals=len(points)-1,
                seconds=time.monotonic()-started, cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[256, 640])
    parser.add_argument('--seeds', nargs='+', type=int, default=[317, 919])
    parser.add_argument('--heights', nargs='+', type=float, default=[54., 65., 100.])
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-joined-count-probe.json'))
    args = parser.parse_args()
    report = dict(scope='complete constructed finite prime universes, not full core',
                  floatingDiagnostic=True, fullPopulationUsed=False,
                  primeCertificates=False, intervalArithmetic=False,
                  logInterpolationNotIntegerEnergy=True, adverseCutoffsSelectedOnce=True,
                  originalMasksAndPhaseRetained=True, floorBudgetCompared=False,
                  growingManyBinOrCofinalPopulationCertified=False,
                  cases=[experiment(n, seed, args.heights) for n in args.orders for seed in args.seeds])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'cases'}))
    for batch in report['cases']:
        print(json.dumps({k: batch[k] for k in ['N', 'seed', 'selectedLabels', 'counts', 'balancedTripleLabels', 'seconds']}))
        for case in batch['cases']:
            print(json.dumps({k: case[k] for k in ['height', 'joinedToSeparateCountEnergyRatio',
                             'rescaledRemainingSmallGcdEnergy', 'rescaledSignedCrossCountEnergy',
                             'rescaledRemainingSameCountContribution', 'rescaledRemainingCrossCountContribution',
                             'rescaledAtomicCost', 'rescaledPeriodCost']}))


if __name__ == '__main__':
    main()

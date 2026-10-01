#!/usr/bin/env python3
"""Optional actual-integer diagnostic for the canonical joined signed main.

Sample integers uniformly inside exact integer bins, factor them, and retain
the original finite core cuts, owner allocation, factorial kernel and phase.
The density model includes its nonsquarefree labels; the literal remainder
includes only original squarefree core incidences. Prime density is never
used to generate labels. Squarefree density uses its floating Euler formula.

This is Monte Carlo, not a certificate: floating endpoints/weights and
sampling error are unproved. These small N are not the cofinal schedule and
need not satisfy the eventual length hypothesis of the Lean comparison.
No empirical confidence interval or asymptotic floor is asserted.
"""

import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations
import json
import math
import random
import time

import numpy as np
from scipy.stats import binom
from sympy import factorint, isprime

from probe_riesz_fixed_count_period import unpaid_orders


CHANNELS = (
    'literal', 'owner_literal', 'density', 'literal_selected',
    'remaining', 'endpoint', 'joined_main',
    'density_prime_b', 'density_composite_b',
    'free_density', 'clipped_density', 'joined_without_free',
    'density_owner_boundary', 'density_unsigned_boundary',
    'density_saturation_boundary', 'joined_unpaid',
)


def parameters(n, bins):
    cutoff = 20000**n // (10001**n * (n+1))
    physical = (cutoff+2)**2
    length = math.log(physical)
    u = 10001/20000
    tilt = 1/(-2*math.log(u))
    log_rate = (2-2*tilt)*math.log(u)-math.log(tilt)
    trial = min(math.floor(math.exp(-n*log_rate/(2*(tilt+2.5)))), cutoff+1)
    edges = [math.floor(math.exp((1.95+.08*i/bins)*n)) for i in range(bins+1)]
    return dict(N=n, physical=physical, length=length, trial=trial,
                edges=edges, orders=unpaid_orders(n).tolist())


def allocation(n, orders, share):
    return sum(float(binom.pmf(k, n+1, share)) for k in orders)


def core_mask(n, label, factors, pars, count_ceiling):
    """Factor-level predicates of the original core on this radius.

    For squarefree labels with count >=3, the paired-label and semiprime
    deletions are empty. All earlier logarithmic windows contain the core
    window. The two one-rough-prime deletions combine into the rough count
    check; the large-smooth-factor deletion checks the full smooth product.
    Strict owner share also excludes the older cancelling share sector.
    """
    if any(e != 1 for e in factors.values()):
        return 'nonsquarefree'
    primes = sorted(factors)
    if not 3 <= len(primes) < count_ceiling:
        return 'count'
    total = math.log(label)
    if not 1.95*n < total <= 2.03*n:
        return 'core_window'
    if not n*math.log(2)/4 < total <= 32*n*math.log(2):
        return 'original_band'
    if not pars['physical'] < label < pars['physical']**2:
        return 'annulus'
    if any(p >= pars['physical'] for p in primes):
        return 'physical_prime'
    if any(label//p <= pars['trial'] for p in primes):
        return 'tilted_cofactor'
    rough = [p for p in primes if p > n*n]
    if len(rough) <= 1:
        return 'smooth_or_one_rough'
    smooth = math.prod(p for p in primes if p <= n*n)
    if smooth >= pars['physical']:
        return 'large_smooth_factor'
    if math.log(primes[-1]) >= .65*total:
        return 'dominant'
    return 'core'


def subset_rows(a_factors):
    primes = sorted(a_factors)
    for count in range(len(primes)+1):
        for subset in combinations(primes, count):
            b = math.prod(subset)
            yield b, count, (-1)**count


def atom(n, label, factors, pars, count_ceiling):
    total = math.log(label)
    p = max(factors)
    logs = {q: math.log(q) for q in factors}
    p_log = logs[p]
    eligible_owner = n*n < p < pars['physical'] and factors[p] == 1
    owner_allocated = allocation(n, pars['orders'], 1-p_log/total) if eligible_owner else 0.
    full_allocated = sum(allocation(n, pars['orders'], 1-logs[q]/total)
                         for q, e in factors.items()
                         if e == 1 and n*n < q < pars['physical'])
    assert owner_allocated >= -1e-12
    mask = core_mask(n, label, factors, pars, count_ceiling)
    a = label//p
    a_factors = dict(factors)
    a_factors[p] -= 1
    if a_factors[p] == 0:
        del a_factors[p]
    response = selected = endpoint = density = prime_density = composite_density = free_density = 0.
    owner_boundary = unsigned_boundary = saturation_boundary = 0.
    divisor_ledger_error = 0.
    for b, count, sign in subset_rows(a_factors):
        d = a//b
        b_log = math.log(b)
        hinge = max(p_log+b_log-pars['length'], 0.)-max(b_log-pars['length'], 0.)
        if mask == 'core':
            response += sign*hinge
        if not eligible_owner or b == 1 or hinge == 0. or any(q >= p for q in a_factors):
            continue
        # These are literal integer endpoints of the canonical row.
        lo_log = max(n/10, 1.95*n-p_log-b_log, (20/13)*p_log-p_log-b_log)
        hi_log = min(2.03*n-p_log-b_log, pars['length']-b_log)
        low = math.ceil(math.exp(lo_log))
        high = math.floor(math.exp(hi_log))
        if low > high:
            continue
        if mask == 'core' and d == low:
            endpoint += sign*hinge
        if low < d <= high:
            if mask == 'core':
                selected += sign*hinge
            marked_primes = [p, *[q for q in a_factors if b % q == 0]]
            squarefree_density = 6/math.pi**2*math.prod(q/(q+1) for q in marked_primes)
            contribution = sign*hinge*squarefree_density
            density += contribution
            if (p_log+b_log <= 1.85*n and p_log <= 1.2675*n
                    and 2.03*n <= p_log+pars['length']):
                free_density += contribution
            elif p_log >= 1.2675*n:
                owner_boundary += contribution
            elif p_log+b_log > 1.85*n:
                unsigned_boundary += contribution
            else:
                assert p_log+pars['length'] < 2.03*n
                saturation_boundary += contribution
            if count == 1:
                prime_density += contribution
            elif count >= 2:
                composite_density += contribution
    if mask == 'core':
        # Independent direct divisor expansion of the original Riesz atom.
        riesz = sum(sign*max(pars['length']-math.log(b), 0.)
                    for b, _, sign in subset_rows(factors))
        # The original coefficient is -(log n/L)*R_L(n). Reflection
        # already moved its parity into the complemented divisor sign.
        expected = -riesz
        divisor_ledger_error = abs(response-expected)
        assert divisor_ledger_error <= 1e-8*max(1., abs(response), abs(expected))
    amplitude = math.exp((n+1)*math.log(10001/20000)-1.5*total+
                         (n+1)*math.log(total)-math.lgamma(n+1))/pars['length']
    owned = 1-owner_allocated
    vals = np.array([
        (1-full_allocated)*response, owned*response, owned*density,
        owned*selected, owned*(response-selected), owned*endpoint,
        owned*(response-selected-endpoint+density),
        owned*prime_density, owned*composite_density,
        owned*free_density, owned*(density-free_density),
        owned*(response-selected-endpoint+density-free_density),
        owned*owner_boundary, owned*unsigned_boundary,
        owned*saturation_boundary,
        owned*(response-selected-endpoint+unsigned_boundary+saturation_boundary),
    ])*amplitude
    assert abs(vals[6]-(vals[4]-vals[5]+vals[2])) <= 1e-12*max(amplitude, abs(vals[6]))
    assert abs(vals[2]-(vals[9]+vals[12]+vals[13]+vals[14])) <= 1e-12*max(amplitude, abs(vals[2]))
    assert abs(vals[15]-(vals[4]-vals[5]+vals[13]+vals[14])) <= 1e-12*max(amplitude, abs(vals[15]))
    return vals, total, mask, len(factors), divisor_ledger_error


def batch(task):
    n, seed, start, size, bins, heights, count_ceiling = task
    pars = parameters(n, bins)
    sums = np.zeros((len(heights), len(CHANNELS)))
    squares = np.zeros((len(heights), len(CHANNELS), len(CHANNELS)))
    masks, counts = Counter(), Counter()
    model_nonsquarefree = np.zeros(len(heights))
    ledger_error = 0.
    examples = []
    for i in range(start, start+size):
        # Index-specific seeds make results independent of process scheduling.
        rng = random.Random((seed << 48)+(n << 32)+i)
        cell = rng.randrange(bins)
        low, high = pars['edges'][cell:cell+2]
        label = rng.randrange(low+1, high+1)
        factors = {int(p): int(e) for p, e in factorint(label).items()}
        assert math.prod(p**e for p, e in factors.items()) == label
        assert all(isprime(p) for p in factors)
        vals, total, mask, count, error = atom(n, label, factors, pars, count_ceiling)
        importance = bins*(high-low)
        phased = np.cos(np.array(heights)*total)[:, None]*vals[None, :]*importance
        sums += phased
        squares += np.einsum('hi,hj->hij', phased, phased)
        if mask == 'nonsquarefree':
            model_nonsquarefree += phased[:, 2]
        masks[mask] += 1
        if mask == 'core':
            counts[count] += 1
            if len(examples) < 2:
                examples.append(dict(label=str(label), factors=factors, total_log=total))
        ledger_error = max(ledger_error, error)
    return dict(sums=sums.tolist(), squares=squares.tolist(), masks=dict(masks),
                counts=dict(counts), model_nonsquarefree=model_nonsquarefree.tolist(),
                ledger_error=ledger_error, examples=examples)


def run(n, seed, samples, bins, heights, count_ceiling, workers):
    started = time.monotonic()
    jobs = [(n, seed, i, min(64, samples-i), bins, heights, count_ceiling)
            for i in range(0, samples, 64)]
    sums = np.zeros((len(heights), len(CHANNELS)))
    squares = np.zeros((len(heights), len(CHANNELS), len(CHANNELS)))
    masks, counts = Counter(), Counter()
    nonsquarefree = np.zeros(len(heights))
    examples, ledger_error = [], 0.
    with ProcessPoolExecutor(max_workers=workers) as pool:
        for result in pool.map(batch, jobs):
            sums += np.array(result['sums'])
            squares += np.array(result['squares'])
            masks.update(result['masks'])
            counts.update(result['counts'])
            nonsquarefree += result['model_nonsquarefree']
            ledger_error = max(ledger_error, result['ledger_error'])
            examples += result['examples']
    means = sums/samples
    covariance = (squares-samples*np.einsum('hi,hj->hij', means, means))/(samples-1)
    pars = parameters(n, bins)
    return dict(N=n, seed=seed, samples=samples, seconds=time.monotonic()-started,
                moving_length=pars['length'], eventual_length_hypothesis_met=pars['length'] >= 11*n/8,
                literal_count_ceiling=count_ceiling, core_masks=masks, core_counts=counts,
                source_normalized_estimates={str(y): dict(zip(CHANNELS, means[i].tolist()))
                                             for i, y in enumerate(heights)},
                diagnostic_standard_errors={str(y): dict(zip(CHANNELS, np.sqrt(
                    np.maximum(covariance[i].diagonal(), 0)/samples).tolist()))
                                            for i, y in enumerate(heights)},
                density_remaining_covariance={str(y): float(covariance[i, 2, 4])
                                               for i, y in enumerate(heights)},
                nonsquarefree_density_estimates=dict(zip(map(str, heights), (nonsquarefree/samples).tolist())),
                exact_divisor_float_ledger_max_error=ledger_error,
                factorized_core_examples=examples[:3])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[28, 32])
    parser.add_argument('--seeds', type=int, nargs='+', default=[0, 1])
    parser.add_argument('--samples', type=int, default=1024)
    parser.add_argument('--bins', type=int, default=32)
    parser.add_argument('--heights', type=float, nargs='+', default=[54., 60., 100.])
    parser.add_argument('--count-ceiling', type=int, default=64)
    parser.add_argument('--workers', type=int, default=4)
    args = parser.parse_args()
    if min(args.orders) < 16 or args.samples < 2 or args.bins < 1 or args.workers < 1:
        parser.error('orders>=16, samples>=2, bins>=1 and workers>=1 required')
    rows = []
    for n in args.orders:
        for seed in args.seeds:
            result = run(n, seed, args.samples, args.bins, args.heights,
                         args.count_ceiling, args.workers)
            rows.append(result)
            print(json.dumps(result), flush=True)
    print(json.dumps(dict(scope=__doc__, rows=rows), indent=2), flush=True)

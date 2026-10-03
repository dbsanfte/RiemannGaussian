#!/usr/bin/env python3
"""Optional density-correct finite-population Riesz diagnostic.

Kalai's decreasing-chain rejection sampler returns uniform factored integers
in each computed integer log bin. Bin-size importance weights estimate the
literal signed sum; squarefree/count/owner/physical/allocation masks stay
inside each atom. No prime-density approximation or manufactured prime pool
is used. All counts join before complete cutoff periods are clipped.

This is numerical research, NOT a floor certificate. Large primality tests,
bin endpoints, logarithms, phases, and factorial probabilities are uncertified.
The finite (N,K) inputs are not the eventual native dyadic count crop. The
sampled positive-part cost is noisy and upward biased; it is not a native
bound. The script is outside builds and CI.

Reference: Adam Kalai, Generating Random Factored Numbers, Easily, SODA 2002,
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/
2003-Generating_Random_Factored_Numbers_Easily-SODA.pdf
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path
import random
import subprocess
import sys
import time

sys.dont_write_bytecode = True
import mpmath as mp
import numpy as np
from scipy.stats import binom
from sympy import isprime

from probe_riesz_canonical_joint import core_mask
from probe_riesz_complex_null_profiles import period_edge
from probe_riesz_fixed_count_period import unpaid_orders


class FactoredSampler:
    """Exact integer rejection steps, assuming the primality oracle is exact."""
    def __init__(self, seed):
        self.rng = random.Random(seed)
        self.trials = self.prime_tests = self.chain_steps = 0

    def interval(self, low, high):
        assert 0 <= low < high
        while True:
            self.trials += 1
            bound, label, factors = high, 1, Counter()
            while True:
                q = self.rng.randrange(1, bound+1)
                self.chain_steps += 1
                if q == 1:
                    break
                self.prime_tests += 1
                if isprime(q):
                    label *= q
                    factors[q] += 1
                    if label > high:
                        break  # Later factors cannot undo this rejected product.
                bound = q  # Inclusive: repetitions must NOT be suppressed.
            if low < label <= high and self.rng.randrange(high) < label:
                assert label == math.prod(p**e for p, e in factors.items())
                return label, dict(factors)


def parameters(order, bins):
    cutoff = 20000**order // (10001**order*(order+1))
    physical = (cutoff+2)**2
    u = mp.mpf(10001)/20000
    tilt = 1/(-2*mp.log(u))
    rate = (2-2*tilt)*mp.log(u)-mp.log(tilt)
    orders = unpaid_orders(order)
    assert len(orders) and np.all(np.diff(orders) == 1)
    return dict(N=order, physical=physical, length=math.log(physical),
        trial=min(int(mp.exp(-order*rate/(2*(tilt+mp.mpf('2.5'))))), cutoff+1),
        orders=orders.tolist(), edges=[int(mp.exp(mp.mpf(order)*
            (mp.mpf(195)/100+mp.mpf(8)*i/(100*bins)))) for i in range(bins+1)])


def divisors(factors):
    out = [(1, 1)]
    for p in factors:
        out += [(d*p, -mu) for d, mu in out]
    return out


def exact_sampler_regressions():
    """Solve the truncated chain law over Q, independently of random draws.

    The inclusive self-loop at a prime contributes P_j(n/j)/j. At a
    composite it contributes P_j(n)/j and must be solved, not omitted.
    Probability beyond the product ceiling is rejection mass.
    """
    checked = 0
    for ceiling in range(1, 33):
        laws = {1: [Fraction(0)]*(ceiling+1)}
        laws[1][1] = Fraction(1)
        for bound in range(2, ceiling+1):
            law = [Fraction(0)]*(ceiling+1)
            for n in range(1, ceiling+1):
                # Drawing 1 terminates; drawing q>1 resumes at q.
                value = Fraction(int(n == 1), bound)
                for q in range(2, bound):
                    multiplier = q if isprime(q) else 1
                    if n % multiplier == 0:
                        value += laws[q][n//multiplier]/bound
                if isprime(bound):
                    if n % bound == 0:
                        value += law[n//bound]/bound
                else:
                    value /= 1-Fraction(1, bound)
                law[n] = value
            laws[bound] = law
        normalizer = math.prod(Fraction(p-1, p)
                              for p in range(2, ceiling+1) if isprime(p))
        for n in range(1, ceiling+1):
            assert laws[ceiling][n] == normalizer/n
            assert laws[ceiling][n]*Fraction(n, ceiling) == normalizer/ceiling
            checked += 1
        for low in range(ceiling):
            mass = sum(laws[ceiling][n]*Fraction(n, ceiling)
                       for n in range(low+1, ceiling+1))
            assert all(laws[ceiling][n]*Fraction(n, ceiling)/mass
                       == Fraction(1, ceiling-low) for n in range(low+1, ceiling+1))
    return dict(exactRationalChainLabels=checked, ceilings=[1, 32],
                inclusivePrimeAndCompositeSelfLoops=True,
                everySubintervalAcceptanceChecked=True, leanCertificate=False)


def atom(order, count_ceiling, pars, label, factors, log_importance):
    status = core_mask(order, label, factors, pars, count_ceiling)
    if status != 'core':
        return None, status
    total, primes = math.log(label), list(factors)
    shares = [1-math.log(p)/total for p in primes
              if order**2 < p < pars['physical']]
    assigned = float(np.sum(binom.cdf(pars['orders'][-1], order+1, shares)
                         - binom.cdf(pars['orders'][0]-1, order+1, shares)))
    assert -1e-8 <= assigned <= 1+1e-8
    unassigned = max(1-assigned, 0.)
    if unassigned == 0:
        return None, 'floating_zero_unassigned'
    amplitude = math.exp((order+1)*math.log(10001/20000)-1.5*total
        +(order+1)*math.log(total)-math.lgamma(order+1)-math.log(pars['length'])
        +math.log(unassigned)+log_importance)
    ds = divisors(primes)
    response = math.fsum(mu*max(pars['length']-math.log(d), 0.) for d, mu in ds)
    return dict(label=label, primes=primes, total=total, count=len(primes),
        owner=math.log(max(primes))/total, amplitude=amplitude,
        response=response, divisors=ds), 'core'


def cutoff_prices(rows, pars, heights, phase_offsets=None):
    if not rows:
        return [dict(joinedPeriodCost=0., splitCountCost=0., periods=0) for _ in heights]
    counts = sorted({r['count'] for r in rows})
    count_index = {count: i+1 for i, count in enumerate(counts)}
    events = defaultdict(lambda: np.zeros((len(heights), len(counts)+1), complex))
    endpoint = max(r['label'] for r in rows)
    literal = np.zeros(len(heights), complex)
    for i, row in enumerate(rows):
        offset = 0. if phase_offsets is None else phase_offsets[i]
        weight = -row['amplitude']*np.exp(-1j*(np.array(heights)*row['total']+offset))
        literal += weight*row['response']
        for d, mu in row['divisors']:
            if d < endpoint:
                events[d][:, [0, count_index[row['count']]]] += mu*weight[:, None]
    points = sorted({1, pars['physical'], endpoint, *events})
    prefix = np.zeros((len(heights), len(counts)+1), complex)
    periods = [defaultdict(lambda: np.zeros(len(counts)+1)) for _ in heights]
    for left, right in zip(points, points[1:]):
        prefix += events.get(left, 0)
        if left < pars['physical']:
            continue
        lo, hi = math.log(left), math.log(right)
        for ih, height in enumerate(heights):
            unit, cursor = 2*math.pi/height, lo
            period = math.floor(lo/unit)
            while cursor < hi:
                edge = min(hi, period_edge(period, unit))
                if edge <= cursor:
                    period += 1
                    continue
                periods[ih][period] -= prefix[ih].real*(edge-cursor)
                cursor, period = edge, period+1
    output = []
    for ih, grouped in enumerate(periods):
        blocks = np.asarray(list(grouped.values()))
        tolerance = 1e-7*max(1., float(np.abs(blocks[:, 0]).sum()))
        error = abs(blocks[:, 0].sum()-literal[ih].real)
        assert error <= tolerance
        assert np.max(np.abs(blocks[:, 1:].sum(axis=1)-blocks[:, 0])) <= tolerance
        cost = float(np.maximum(-blocks[:, 0], 0).sum())
        split = float(np.maximum(-blocks[:, 1:], 0).sum())
        assert cost <= split+tolerance
        output.append(dict(joinedPeriodCost=cost, splitCountCost=split,
            countCancellation=split-cost, periods=len(blocks), literalIdentityError=float(error)))
    return output


def experiment(order, count_ceiling, seed, samples, bins, heights, null_repeats):
    start, sampler = time.monotonic(), FactoredSampler(seed)
    pars, rng = parameters(order, bins), random.Random(seed+1234567)
    cache = Path('.lake/riesz-factored-population/inputs')/f'N{order}-seed{seed}-M{samples}-bins{bins}.json'
    cache.parent.mkdir(parents=True, exist_ok=True)
    reused = cache.exists()
    if reused:
        inputs = json.loads(cache.read_text())
        assert inputs['edges'] == [str(x) for x in pars['edges']]
        draws = inputs['draws']
        assert len(draws) == samples
    else:
        draws = []
        for _ in range(samples):
            cell = rng.randrange(bins)
            label, factors = sampler.interval(*pars['edges'][cell:cell+2])
            draws.append(dict(cell=cell, label=str(label),
                              factors={str(p): e for p, e in factors.items()}))
        inputs = dict(N=order, seed=seed, samples=samples, bins=bins,
                      edges=[str(x) for x in pars['edges']], draws=draws,
                      sampler=dict(trials=sampler.trials, primalityTests=sampler.prime_tests,
                                   chainSteps=sampler.chain_steps))
        cache.write_text(json.dumps(inputs, indent=2)+'\n')
    masks, count_hist, selected_hist, rows = Counter(), Counter(), Counter(), []
    values = np.zeros((samples, len(heights)))
    signed_counts = defaultdict(lambda: np.zeros(len(heights)))
    absolute_counts = defaultdict(lambda: np.zeros(len(heights)))
    for i in range(samples):
        cell = draws[i]['cell']
        low, high = pars['edges'][cell:cell+2]
        label = int(draws[i]['label'])
        factors = {int(p): e for p, e in draws[i]['factors'].items()}
        assert low < label <= high
        assert label == math.prod(p**e for p, e in factors.items())
        assert all(e > 0 and isprime(p) for p, e in factors.items())
        count_hist[len(factors)] += 1
        row, status = atom(order, count_ceiling, pars, label, factors,
                           math.log(bins)+math.log(high-low)-math.log(samples))
        masks[status] += 1
        if row:
            row['sampleIndex'] = i
            rows.append(row)
            selected_hist[row['count']] += 1
            value = -row['amplitude']*row['response']*np.cos(np.array(heights)*row['total'])
            values[i] = value
            signed_counts[row['count']] += value
            absolute_counts[row['count']] += np.abs(value)
    prices = cutoff_prices(rows, pars, heights)
    half_prices = []
    for parity in range(2):
        half_rows = [dict(row, amplitude=2*row['amplitude']) for row in rows
                     if row['sampleIndex'] % 2 == parity]
        half_prices.append(cutoff_prices(half_rows, pars, heights))
    phase_rng = random.Random(seed+7654321)
    null_prices = [cutoff_prices(rows, pars, heights,
        [phase_rng.uniform(0., 2*math.pi) for _ in rows]) for _ in range(null_repeats)]
    cases = []
    for ih, height in enumerate(heights):
        half_mean = (half_prices[0][ih]['joinedPeriodCost']
                    +half_prices[1][ih]['joinedPeriodCost'])/2
        assert half_mean+1e-7 >= prices[ih]['joinedPeriodCost']
        cases.append(dict(height=height, signedEstimate=float(values[:, ih].sum()),
            standardError=float(values[:, ih].std(ddof=1)*math.sqrt(samples)),
            signedByCount={k: float(v[ih]) for k, v in signed_counts.items()},
            absoluteByCount={k: float(v[ih]) for k, v in absolute_counts.items()},
            meanHalfSampleCost=half_mean,
            samplePoolingGap=half_mean-prices[ih]['joinedPeriodCost'],
            independentPhaseControls=[p[ih] for p in null_prices], **prices[ih]))
    return dict(N=order, K=count_ceiling, seed=seed, samples=samples, bins=bins,
        masks=dict(masks), countHistogram=dict(count_hist), selectedCountHistogram=dict(selected_hist),
        selectedLabels=len(rows), minimumOwnerShare=min((r['owner'] for r in rows), default=None),
        maximumOwnerShare=max((r['owner'] for r in rows), default=None),
        inputReceipt=dict(path=str(cache), sha256=hashlib.sha256(cache.read_bytes()).hexdigest(),
                          reused=reused), sampler=inputs['sampler'],
        seconds=time.monotonic()-start, cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[32, 64])
    parser.add_argument('--count-ceiling', type=int, default=16)
    parser.add_argument('--samples', type=int, default=512)
    parser.add_argument('--bins', type=int, default=16)
    parser.add_argument('--phase-null-repeats', type=int, default=3,
                        help='negative controls only; never the literal prime phase')
    parser.add_argument('--regressions-only', action='store_true')
    parser.add_argument('--seeds', nargs='+', type=int, default=[317, 919])
    parser.add_argument('--heights', nargs='+', type=float, default=[54., 65., 100.])
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-factored-population/report.json'))
    args = parser.parse_args()
    if (min(args.orders) < 24 or args.samples < 2 or args.samples % 2 or args.bins < 1
            or args.phase_null_repeats < 0
            or args.count_ceiling < 4 or any(not math.isfinite(y) or y < 54 for y in args.heights)):
        parser.error('N>=24, even samples>=2, bins>=1, K>=4, finite heights>=54 required')
    regressions = exact_sampler_regressions()
    if args.regressions_only:
        print(json.dumps(regressions))
        return
    mp.mp.dps = max(100, int(max(args.orders)*2.03/math.log(10))+80)
    report = dict(schemaVersion=1, sourceSHA256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        baseHead=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        scope=dict(outsideBuildsCI=True, uniformWithinComputedIntegerBins=True,
            exactIntegerRejection=True, probablePrimality=True, floatingWeightsAndMasks=True,
            uniformLawRequiresExactPrimality=True,
            physicalAndFactorialMasksRetained=True, everyCountJoinedBeforeClipping=True,
            finitePopulationDensityImportance=True, manufacturedPrimeInventory=False,
            eventualNativeCountCropApplied=False, sampledCostUpwardBiased=True,
            independentErrorBoundProved=False, phaseControlsAreNotArithmeticCarriers=True,
            cofinalBound=False, floorClosed=False), exactRegressions=regressions, batches=[])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for order in args.orders:
        for seed in args.seeds:
            batch = experiment(order, args.count_ceiling, seed, args.samples, args.bins,
                               args.heights, args.phase_null_repeats)
            report['batches'].append(batch)
            args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
            print(json.dumps(dict(N=order, seed=seed, selected=batch['selectedLabels'],
                estimates=[(c['signedEstimate'], c['standardError']) for c in batch['cases']],
                sampledCosts=[c['joinedPeriodCost'] for c in batch['cases']],
                seconds=batch['seconds']), allow_nan=False), flush=True)


if __name__ == '__main__':
    main()

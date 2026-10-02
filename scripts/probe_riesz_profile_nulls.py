#!/usr/bin/env python3
"""Optional profile-null diagnostic on native-mask constructed subsets.

Reuse actual probable-prime products and all weights from the reflected
phase probe. Compare the original flat-before-L profile with its continuous
log-quadratic least-energy correction. Recompute adverse cutoffs for the
ENTIRE subset for each profile. Exact columns and all counts stay joined.

The log interpolation is a floating diagnostic, NOT the integer Lean
profile energy. The constructed subset is not the full core or a density
sample. Amplitudes have one common positive rescaling for underflow.
No comparison with the native numerical floor budget is certified.
"""

import argparse
from collections import defaultdict
import json
import math
from pathlib import Path
import time

import mpmath as mp
import numpy as np
from scipy.optimize import minimize

from probe_riesz_reflected_phase_gram import native_subset


def profile_cost(left, right, correlation, length, linear, quadratic):
    """Integrate each linear derivative exactly in the log interpolation."""
    mid = (left + right) / 2
    constant = linear - (mid < length)
    slope = 2 * quadratic
    g0 = constant + slope * left
    g1 = constant + slope * right
    c0, c1 = correlation * g0, correlation * g1
    lower, upper = left.copy(), right.copy()
    negative = (c0 <= 0) & (c1 <= 0)
    positive = (c0 >= 0) & (c1 >= 0)
    if slope:
        root = -constant / slope
        lower = np.where((c0 < 0) & (c1 > 0), root, lower)
        upper = np.where((c0 > 0) & (c1 < 0), root, upper)
    assert np.all(positive | negative | (c0 * c1 < 0))
    active = (~negative) & (upper > lower)
    lower, upper = lower[active], upper[active]
    constant, phi = constant[active], correlation[active]
    width = upper - lower
    first = width * (lower + upper) / 2
    second = width * (lower**2 + lower * upper + upper**2) / 3
    adverse_cost = float(np.sum(phi * (constant * width + slope * first)))
    adverse_energy = float(np.sum(phi**2 * width))
    adverse_profile = float(np.sum(constant**2 * width
                                   + 2 * constant * slope * first
                                   + slope**2 * second))
    complete_first = (right-left) * (left+right) / 2
    complete_second = (right-left) * (left**2+left*right+right**2) / 3
    complete_constant = linear - (mid < length)
    total_profile = float(np.sum(complete_constant**2 * (right-left)
                                + 2 * complete_constant * slope * complete_first
                                + slope**2 * complete_second))
    joined = -float(np.sum(correlation * (complete_constant * (right-left)
                                         + slope * complete_first)))
    assert adverse_cost >= -1e-8
    return dict(joined=joined, atomicCost=adverse_cost,
                adverseEnergy=adverse_energy, adverseProfile=adverse_profile,
                cauchyCost=math.sqrt(max(adverse_energy*adverse_profile, 0)),
                completeProfile=total_profile)


def experiment(order, samples, seed, heights):
    started = time.monotonic()
    pars, rows = native_subset(order, 8 if order == 256 else 16, samples, seed)
    endpoint = max(r['label'] for r in rows)
    log_endpoint = math.log(endpoint)
    length = pars['length']
    lam = length/log_endpoint
    linear = 4*lam-3*lam**2
    quadratic = 3*lam*(lam-1)/log_endpoint
    events = defaultdict(list)
    for i, row in enumerate(rows):
        for d, sign in row['divisors']:
            events[d].append((i, sign))
    points = sorted({1, endpoint, *events})
    columns = np.zeros(samples, dtype=np.int32)
    scale = max(r['log_amplitude'] for r in rows)
    amplitude = np.exp([r['log_amplitude']-scale for r in rows])
    weights = -amplitude[None, :]*np.cos(np.array(heights)[:, None]
                                       *np.array([r['total'] for r in rows]))
    left, right, phis = [], [], []
    for a, b in zip(points, points[1:]):
        for i, sign in events[a]:
            columns[i] += sign
        lo, hi = math.log(a), math.log(b)
        cuts = [lo, hi] if not lo < length < hi else [lo, length, hi]
        for lo, hi in zip(cuts, cuts[1:]):
            left.append(lo)
            right.append(hi)
            phis.append(weights @ columns)
    left, right = np.array(left), np.array(right)
    phis = np.array(phis).T
    core_responses = np.array([math.fsum(sign*max(length-math.log(d), 0.)
                                        for d, sign in row['divisors'])
                               for row in rows])
    literal = weights @ core_responses
    cases = []
    for i, height in enumerate(heights):
        phi = phis[i]
        baseline = profile_cost(left, right, phi, length, 1., 0.)
        corrected = profile_cost(left, right, phi, length, linear, quadratic)
        candidate = profile_cost(left, right, phi, length, 4/3, -1/(3*order))
        # The optimizer is diagnostic; no optimality or rational certificate.
        def objective(v):
            return profile_cost(left, right, phi, length,
                                float(v[0]), float(v[1])/log_endpoint)['atomicCost']
        fits = [minimize(objective, v, method='Powell',
                         options={'xtol':1e-7, 'ftol':1e-9, 'maxiter':200})
                for v in [[1., 0.], [linear, quadratic*log_endpoint]]]
        best = min(fits, key=lambda f: f.fun)
        optimized = profile_cost(left, right, phi, length,
                                 float(best.x[0]), float(best.x[1])/log_endpoint)
        for row in [baseline, corrected, candidate, optimized]:
            assert abs(row['joined']-literal[i]) < 1e-7*max(1., abs(literal[i]))
        expected_profile = log_endpoint*lam*(1-lam)*(1-3*lam*(1-lam))
        assert abs(corrected['completeProfile']-expected_profile) < 1e-7
        early = right <= math.log(min(p for r in rows for p in r['primes']))
        common = float(weights[i].sum())
        assert np.allclose(phi[early], common, atol=1e-12)
        cases.append(dict(N=order, height=height, samples=samples,
                          commonPrefix=common, literalJoined=float(literal[i]),
                          original=baseline, leastProfile=corrected,
                          fixedCandidate=candidate,
                          optimizedAtomic=optimized,
                          leastProfileLinear=linear, leastProfileQuadratic=quadratic,
                          fittedLinear=float(best.x[0]),
                          fittedQuadratic=float(best.x[1])/log_endpoint,
                          correctedProfileRatio=corrected['completeProfile']/baseline['completeProfile'],
                          correctedCauchyRatio=corrected['cauchyCost']/baseline['cauchyCost'],
                          candidateCauchyRatio=candidate['cauchyCost']/baseline['cauchyCost'],
                          candidateProfileRatio=candidate['completeProfile']/baseline['completeProfile'],
                          correctedAtomicRatio=corrected['atomicCost']/baseline['atomicCost']
                              if baseline['atomicCost'] else None,
                          optimizedAtomicRatio=optimized['atomicCost']/baseline['atomicCost']
                              if baseline['atomicCost'] else None))
    return dict(N=order, seed=seed, sourceAmplitudeLogScale=scale,
                allOriginalSubsetMasksRetained=True, fullPopulationUsed=False,
                exactIntegerPrefixColumnsUsed=True,
                logInterpolationNotIntegerEnergy=True,
                primeCertificatesOrIntervals=False,
                seconds=time.monotonic()-started, cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[256, 640])
    parser.add_argument('--samples', type=int, default=24)
    parser.add_argument('--seed', type=int, default=20261002)
    parser.add_argument('--heights', type=float, nargs='+', default=[54, 65, 100])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if any(n not in (256, 640) for n in args.orders) or args.samples < 8:
        parser.error('only native orders256/640 and at least8 labels supported')
    mp.mp.dps = 80
    rows = []
    for n in args.orders:
        row = experiment(n, args.samples, args.seed, args.heights)
        rows.append(row)
        print(json.dumps({'N':n, 'seconds':row['seconds'],
                          'profileRatios':[c['correctedProfileRatio'] for c in row['cases']],
                          'cauchyRatios':[c['correctedCauchyRatio'] for c in row['cases']],
                          'fixedCandidateCauchyRatios':[c['candidateCauchyRatio'] for c in row['cases']],
                          'optimizedAtomicRatios':[c['optimizedAtomicRatio'] for c in row['cases']]}),
              flush=True)
    report = dict(scope=__doc__, floorProved=False, nativeFullPopulationBudget=False,
                  rigorousIntervalCertificate=False, rows=rows)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()

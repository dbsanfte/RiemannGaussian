#!/usr/bin/env python3
"""Optional sign-capacity diagnostic; NOT an arithmetic prime-sum bound.

At the single radial slice T=2N, integrate the exact signed Riesz subset
coefficient against the UNPROVED ordinary-prime-density model. Keep its
moving length and the model's binomial allocation. This rough-sector
diagnostic omits primes <=N^2, all counts above nine, and radial/phase
transport. It cannot establish a signed floor or a no-go theorem.
"""
import hashlib
import json
import math
from itertools import combinations
from functools import lru_cache
from pathlib import Path

import numpy as np
from scipy.stats import binom, qmc

from probe_riesz_joint_core import length


@lru_cache(maxsize=None)
def cutoff_ratio(N):
    return length(N)/(2*N)


def row(N, count, seed):
    power = 16 if count < 7 else 14
    lam = cutoff_ratio(N)
    least = math.log(N)/N
    free = 1-count*least
    points = qmc.Sobol(count-1, scramble=True, seed=seed).random_base2(power)
    cuts = np.sort(points, axis=1)
    shares = least+free*np.diff(np.column_stack((np.zeros(len(points)), cuts,
                                                np.ones(len(points)))), axis=1)
    coefficient = np.zeros(len(points))
    for first in range(0, len(points), 512):
        xs = shares[first:first+512]
        sums, signs = np.zeros((len(xs), 1)), np.ones(1)
        for col in xs.T:
            sums = np.concatenate((sums, sums+col[:, None]), axis=1)
            signs = np.concatenate((signs, -signs))
        coefficient[first:first+len(xs)] = -2/lam*np.sum(
            signs*np.maximum(lam-sums, 0), axis=1)
    allocated = np.sum(binom.cdf(13*N//32, N+1, 1-shares)
                       -binom.cdf((N+5)//5, N+1, 1-shares), axis=1)
    assert np.min(allocated) >= -1e-10 and np.max(allocated) <= 1+1e-10
    unassigned = np.clip(1-allocated, 0, 1)
    valid = np.max(shares, axis=1) < .65
    weight = free**(count-1)/(math.factorial(count)*math.factorial(count-1))
    weight = weight/np.prod(shares, axis=1)*valid*unassigned
    positive = np.mean(weight*np.maximum(coefficient, 0))
    negative = np.mean(weight*np.maximum(-coefficient, 0))
    balanced = (np.max(shares, axis=1) <= .35) & (np.min(shares, axis=1) >= .30)
    result = dict(N=N, count=count, seed=seed, samples=2**power,
                  cutoff_ratio=lam, sign_transition_share=2*lam-1,
                  positive=float(positive), negative=float(negative),
                  net=float(positive-negative),
                  balanced_triple_positive=float(np.mean(weight*np.maximum(coefficient, 0)*balanced)))
    if count == 4:
        gap = np.max(shares, axis=1)+1-2*lam
        lower, upper = -2/lam*np.maximum(-gap, 0), 2/lam*np.maximum(gap, 0)
        excess_balance = 3*lam-2-np.sum(np.maximum(shares-(1-lam), 0), axis=1)
        exact_negative = 2/lam*np.maximum(excess_balance, 0)
        result['old_gap_negative_cost'] = float(np.mean(weight*(-lower)))
        result['exact_negative_formula_cost'] = float(np.mean(weight*exact_negative))
        result['floating_max_negative_formula_error'] = float(np.max(np.abs(
            exact_negative-np.maximum(-coefficient, 0))))
        assert result['floating_max_negative_formula_error'] < 1e-10
        result['floating_max_bound_violation'] = float(max(np.max(lower-coefficient),
                                                          np.max(coefficient-upper)))
        assert result['floating_max_bound_violation'] < 1e-10
    if count == 5:
        ordered = np.sort(shares, axis=1)[:, ::-1]
        gap = np.minimum(2*ordered[:, 0]+1-3*lam,
                         ordered[:, 0]-ordered[:, 1]+1-2*lam)
        upper = 2/lam*np.maximum(gap, 0)
        result['floating_max_bound_violation'] = float(np.max(coefficient-upper))
        result['gap_upper_positive_cost'] = float(np.mean(weight*upper))
        clipped_upper = np.minimum(upper, 2/lam*3*ordered[:, -1])
        result['least_clipped_upper_positive_cost'] = float(np.mean(weight*clipped_upper))
        assert np.max(coefficient-clipped_upper) < 1e-10
        exact_balance = 2*ordered[:, 0]+1-3*lam-np.sum(
            np.maximum(ordered[:, 1:]-(lam-ordered[:, 0])[:, None], 0), axis=1)
        exact_positive = 2/lam*np.maximum(exact_balance, 0)
        result['exact_positive_formula_cost'] = float(np.mean(weight*exact_positive))
        result['floating_max_positive_formula_error'] = float(np.max(np.abs(
            exact_positive-np.maximum(coefficient, 0))))
        assert result['floating_max_positive_formula_error'] < 1e-10
        # Rejected exploratory bound: dropping the positive three-subset
        # hinges provides favorable mass but did not improve the old floor.
        reflected = 1-lam
        pair_loss = sum(np.maximum(reflected-shares[:, i]-shares[:, j], 0)
                        for i, j in combinations(range(count), 2))
        pair_balance = 3-4*lam+np.sum(np.maximum(shares-reflected, 0)
                                    -np.maximum(shares-lam, 0), axis=1)-pair_loss
        pair_floor = 2/lam*pair_balance
        old_floor = np.maximum(-coefficient, 0)-clipped_upper
        result['pair_bound_favorable_mass'] = float(np.mean(weight*np.maximum(pair_floor, 0)))
        result['pair_bound_joint_improvement'] = float(np.mean(
            weight*(np.maximum(old_floor, pair_floor)-old_floor)))
        result['favorable_negative_credit'] = float(negative)
        result['balanced_negative_credit'] = float(np.mean(
            weight*np.maximum(-coefficient, 0)*(ordered[:, 0] <= 0.5)))
        result['adverse_support_sample_fraction'] = float(np.mean(gap > 0))
        result['total_sample_fraction_positive'] = float(np.mean(coefficient > 1e-12))
        assert result['floating_max_bound_violation'] < 1e-10
    return result


def main():
    rows = []
    for N in (4096, 65536, 1048576):
        for count in range(3, 10):
            for seed in (17, 29):
                entry = row(N, count, seed)
                rows.append(entry)
                print({k: entry[k] for k in ('N', 'count', 'seed', 'positive', 'negative')}, flush=True)
    payload = dict(
        scope="uncertified sign-capacity model on one rough-sector radial slice",
        normalization="coefficient/N; common radial and phase factors not included",
        rows=rows,
        limitations=[
            "Prime measures are replaced by a continuum density; no literal counting transport is proved.",
            "Only T=2N is sampled. No radial integration or fixed-height phase estimate follows.",
            "Only the rough sector with every prime >N^2 is modeled; the full core also has small prime factors.",
            "Counts above nine are omitted without a tail bound.",
            "Two Sobol scrambles are diagnostics, not certified integration errors; high-count variance is visible.",
            "Positive/negative columns refer to coefficient sign, not the real arithmetic sum at a zero ordinate.",
            "Insufficient modeled four-prime capacity is not an arithmetic impossibility theorem.",
            "The separate Lean four/five-prime inequalities and exact adverse-part identities use no numerical output.",
            "The discarded pair-hinge bound is only a numerical experiment; no universal dominance theorem is asserted."],
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    output = Path(__file__).resolve().parents[1]/"docs/riesz-joint-capacity-probe.json"
    output.write_text(json.dumps(payload, indent=2)+"\n")


if __name__ == '__main__':
    main()

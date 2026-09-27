#!/usr/bin/env python3
"""Optional four-prime debit diagnostic; not a signed arithmetic certificate.

The ordinary-prime-density model is evaluated at T=2N. This deliberately
does not estimate the literal prime sum or its radial/phase transport.
Lean checks the coefficient identities independently of this script.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

import numpy as np
from scipy.stats import binom, qmc

from probe_riesz_joint_core import length


def row(N, seed, power):
    lam = length(N)/(2*N)
    lower = math.log(N)/N
    free = 1-4*lower
    assert free > 0
    cuts = np.sort(qmc.Sobol(3, scramble=True, seed=seed).random_base2(power), axis=1)
    shares = lower+free*np.diff(np.column_stack(
        (np.zeros(len(cuts)), cuts, np.ones(len(cuts)))), axis=1)
    sums, signs = np.zeros((len(shares), 1)), np.ones(1)
    for column in shares.T:
        sums = np.concatenate((sums, sums+column[:, None]), axis=1)
        signs = np.concatenate((signs, -signs))
    coefficient = -2/lam*np.sum(signs*np.maximum(lam-sums, 0), axis=1)
    ordered = np.sort(shares, axis=1)[:, ::-1]
    largest = ordered[:, 0]
    deletion_cutoff = lam-largest
    old = 2/lam*np.maximum(largest+1-2*lam, 0)
    exact = 2/lam*np.maximum(largest+1-2*lam-np.sum(
        np.maximum(ordered[:, 1:]-deletion_cutoff[:, None], 0), axis=1), 0)
    negative = 2/lam*np.maximum(3*lam-2-np.sum(
        np.maximum(shares-(1-lam), 0), axis=1), 0)
    allocation = np.sum(
        binom.cdf(13*N//32, N+1, 1-shares)
        -binom.cdf((N+5)//5, N+1, 1-shares), axis=1)
    assert allocation.min() >= -1e-10 and allocation.max() <= 1+1e-10
    weight = free**3/(math.factorial(4)*math.factorial(3))/np.prod(shares, axis=1)
    weight *= (largest < .65)*np.clip(1-allocation, 0, 1)
    second_large = ordered[:, 1] >= 1-lam
    errors = dict(
        positive_identity=float(np.max(abs(exact-np.maximum(coefficient, 0)))),
        negative_identity=float(np.max(abs(negative-np.maximum(-coefficient, 0)))),
        marked_log_bound=float(np.max(abs(coefficient)-2/lam*ordered[:, -1])),
        second_large_positive=float(np.max(np.maximum(coefficient[second_large], 0))))
    assert all(value < 1e-10 for value in errors.values())
    return dict(N=N, seed=seed, samples=2**power, cutoff_ratio=lam,
                old_positive_debit=float(np.mean(weight*old)),
                exact_positive_debit=float(np.mean(weight*exact)),
                old_debit_on_zero_charge_sector=float(np.mean(weight*old*second_large)),
                exact_negative_debit=float(np.mean(weight*negative)),
                floating_max_errors=errors)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[4096, 65536, 1048576])
    parser.add_argument('--power', type=int, default=16)
    parser.add_argument('--seeds', nargs='+', type=int, default=[17, 29])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rows = []
    for N in args.orders:
        for seed in args.seeds:
            entry = row(N, seed, args.power)
            rows.append(entry)
            print({k: entry[k] for k in ('N', 'seed', 'old_positive_debit',
                                        'exact_positive_debit')}, flush=True)
    sources = [Path(__file__), Path(__file__).with_name('probe_riesz_joint_core.py')]
    report = dict(
        scope='Uncertified density diagnostic; no actual prime-sum bound',
        normalization='Coefficient/N at T=2N; common radial and phase factors omitted',
        rows=rows,
        source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
        limitations=[
            'No prime-measure transport is proved or assumed by the Lean results.',
            'Only the four-prime rough sector with every prime>N^2 is sampled.',
            'No radial integration, actual phase correlation, or remaining-count bound is computed.',
            'Independent Sobol scrambles are diagnostics, not certified integration error bars.',
            'The separate small-four-prime-head estimate is proved in Lean, not inferred from this rough-sector probe.',
            'No cofinal numerical floor, source decay, RH contradiction or zero exclusion follows.' ])
    args.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()

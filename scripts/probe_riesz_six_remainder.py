#!/usr/bin/env python3
"""Optional angular-cost diagnostic for the unpaid six-prime sector.

This is a continuum importance-sampling model, not a certificate or a
literal prime-sum estimate. It evaluates the complete signed Riesz divisor
response before splitting its signs. No result is spent in the Lean ledger.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path

import numpy as np
from scipy.special import gammaincinv, gammaln
from scipy.stats import qmc


def sample(count, power, alpha, seed, cutoff):
    """Symmetric density integral divided by count!, hence unordered labels."""
    uniform = qmc.Sobol(count, scramble=True, seed=seed).random_base2(power)
    raw = gammaincinv(alpha, np.maximum(uniform, np.finfo(float).tiny))
    shares = raw / raw.sum(axis=1, keepdims=True)
    del raw, uniform
    total = 1 << power
    sums = np.zeros((4, 9), dtype=np.longdouble)
    for begin in range(0, total, 8192):
        x = shares[begin:begin+8192].astype(np.longdouble)
        keep = (x.max(axis=1) < np.longdouble(119)/200) & (x.min(axis=1) > 1e-8)
        x = x[keep]
        if not len(x):
            continue
        D = 1-np.longdouble(cutoff)
        outer = (x >= D).sum(axis=1)
        response = np.zeros(len(x), dtype=np.longdouble)
        for k in range(count+1):
            for subset in itertools.combinations(range(count), k):
                shifted = D - (x[:, subset].sum(axis=1) if subset else 0)
                response += (-1)**k * np.maximum(0, shifted)
        coefficient = -(-1)**count * response / np.longdouble(cutoff)
        # The independently proved three-outer coefficient is identically zero.
        coefficient[outer >= 3] = 0
        # Dirichlet(alpha,...,alpha) importance weight for prod(dx_i/x_i).
        log_weight = (count*gammaln(alpha)-gammaln(count*alpha)
                      -gammaln(count+1)-alpha*np.log(x).sum(axis=1))
        weight = np.exp(log_weight)
        least_unit = x.min(axis=1)/np.longdouble(cutoff)
        center_charge = np.minimum(3*x.min(axis=1),
            4*np.abs(x.max(axis=1)+1-2*np.longdouble(cutoff)))/np.longdouble(cutoff)
        active = np.sort(x, axis=1)[:, :5]
        second_cutoff = active.sum(axis=1)-D
        second_large = (active >= second_cutoff[:, None]).sum(axis=1)
        second_total = np.where(active < second_cutoff[:, None], active, 0).sum(axis=1)
        lower_units = np.full(len(x), 3, dtype=np.longdouble)
        upper_units = np.full(len(x), 3, dtype=np.longdouble)
        lower_units[second_large == 1] = 2
        lower_units[second_large == 2] = 1
        lower_units[second_large == 3] = 0
        upper_units[(1 <= second_large) & (second_large <= 3)] = 1
        outer_thirds = ((3*second_cutoff <= second_total) |
                        (2*second_total <= 3*second_cutoff))
        lower_units[(second_large == 1) & outer_thirds] = 1
        second_lower = np.minimum(center_charge, lower_units*least_unit)
        second_upper = np.minimum(center_charge, upper_units*least_unit)
        # This check concerns the exact continuous logarithm model only.
        # Lean proves its literal integer counterpart independently.
        one_large = outer == 1
        assert np.max(np.abs(coefficient[one_large])-center_charge[one_large], initial=0) < 1e-10
        assert np.min(coefficient[one_large]+second_lower[one_large], initial=0) > -1e-10
        assert np.min(second_upper[one_large]-coefficient[one_large], initial=0) > -1e-10
        for o in range(4):
            index = outer == o
            pos = np.maximum(coefficient[index], 0)*weight[index]
            neg = np.maximum(-coefficient[index], 0)*weight[index]
            unit = least_unit[index]*weight[index]
            previous = 3*unit.sum() if o == 1 else 0
            centered = (center_charge[index]*weight[index]).sum() if o == 1 else 0
            lower = (second_lower[index]*weight[index]).sum() if o == 1 else 0
            upper = (second_upper[index]*weight[index]).sum() if o == 1 else 0
            sums[o] += (pos.sum(), neg.sum(), (pos-neg).sum(), unit.sum(),
                        index.sum(), previous, centered, lower, upper)
    sums[:, [0, 1, 2, 3, 5, 6, 7, 8]] /= total
    return sums.astype(float)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--power', type=int, default=18)
    parser.add_argument('--replicates', type=int, default=4)
    parser.add_argument('--alpha', type=float, default=0.6)
    parser.add_argument('--cutoff', type=float, default=0.6931)
    parser.add_argument('--output', type=Path, default=Path('docs/riesz-six-remainder-probe.json'))
    args = parser.parse_args()
    assert 1 <= args.power <= 23 and args.replicates >= 2
    assert args.alpha > 0 and 0.693 <= args.cutoff <= 0.6932
    results = np.array([sample(6, args.power, args.alpha, 20260928+j, args.cutoff)
                        for j in range(args.replicates)])
    rows = []
    names = ['positive_coefficient_cost', 'negative_coefficient_cost',
             'signed_coefficient_integral', 'least_prime_unit_cost', 'retained_sample_count',
             'one_large_previous_charge', 'one_large_centered_charge',
             'one_large_second_lower_charge', 'one_large_second_upper_charge']
    for outer in range(4):
        means = results[:, outer].mean(axis=0)
        errors = results[:, outer].std(axis=0, ddof=1)/math.sqrt(args.replicates)
        rows.append({'reflected_large_count': outer,
                     **{name: {'mean': float(means[i]), 'replicate_standard_error': float(errors[i])}
                        for i, name in enumerate(names)}})
    payload = {'model_only': True, 'arithmetic_certificate': False,
               'normalization': '(-(-1)^6 R_(1-lambda))/lambda against prod(dx_i/x_i), divided by 6!',
               'prime_count': 6, 'largest_share_ceiling': '119/200',
               'least_share_floor': '1/100000000', 'cutoff': args.cutoff,
               'samples_per_replicate': 1 << args.power, 'replicates': args.replicates,
               'importance_alpha': args.alpha, 'rows': rows,
               'limitations': ['Floating-point quadrature is not a rigorous enclosure.',
                   'No actual prime count or source-normalized transfer is asserted.',
                   'The unassigned factor is bounded above by one, not replaced in a signed carrier theorem.',
                   'Radial and phase factors are excluded; these are angular diagnostic costs only.',
                   'Second-reflection charges are coefficient-side diagnostics; no population payment is inferred.',
                   'Other counts, the omitted small-share boundary and other periods are not paid.'],
               'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    args.output.write_text(json.dumps(payload, indent=2)+'\n')
    print(json.dumps(rows, indent=2))


if __name__ == '__main__':
    main()

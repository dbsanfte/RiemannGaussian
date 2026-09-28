#!/usr/bin/env python3
"""Optional sign-preserving five-prime diagnostic; no arithmetic certificate.

The reflected Riesz coefficient is evaluated with every subset sign. The
partitions explain which already-supported angular regions merit a sharper
literal inequality. They do not count primes or pay a source-scale term.
"""

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.special import gammaln
from scipy.stats import qmc


def sample(lam, power, seed):
    x = -np.log(qmc.Sobol(5, scramble=True, seed=seed).random_base2(power))
    x = np.sort(x/x.sum(axis=1, keepdims=True), axis=1)
    subset_sums = [np.zeros(len(x))]
    for i in range(5):
        subset_sums += [s+x[:, i] for s in subset_sums]
    response = sum((-1)**bits.bit_count()*np.maximum(1-lam-s, 0)
                   for bits, s in enumerate(subset_sums))
    # For five primes reflection gives +H_5(1-lambda)/lambda.
    coeff = response/lam*np.exp(-np.log(x).sum(axis=1)-gammaln(6)-gammaln(5))
    mass = np.maximum(-coeff, 0)
    base = (x[:, 0] >= .001) & (x[:, 4] <= .601)
    old = ((x[:, 0] >= .01) & (x[:, 4] <= .5)
           & (x[:, 0]+x[:, 1]+x[:, 4] <= lam)
           & (x[:, 2]+x[:, 3]+x[:, 4] >= lam))
    above = ((x[:, 0] >= .01) & (x[:, 4] > .5) & (x[:, 4] <= 9/16)
             & (x[:, 0]+x[:, 1]+x[:, 4] <= lam)
             & (x[:, 2]+x[:, 3]+x[:, 4] >= lam))
    linear = (x[:, 0] >= (1-lam)/2) & (x[:, 4] <= 1-lam)
    regions = {'all_negative': base, 'old_credited_region': base & old,
               'owner_above_half': base & above,
               'reflected_linear': base & linear,
               'three_largest_below_cutoff': base & (x[:, 2:].sum(axis=1) < lam)}
    return {key: float(mass[mask].sum()/len(x)) for key, mask in regions.items()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--power', type=int, default=19)
    parser.add_argument('--replicates', type=int, default=4)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    rows = []
    for lam in [.682, .693, .704]:
        samples = [sample(lam, args.power, 19870+i) for i in range(args.replicates)]
        row = {'ratio': lam, 'replicates': samples}
        for key in samples[0]:
            values = [s[key] for s in samples]
            row[key] = {'mean': float(np.mean(values)), 'replicate_range': [min(values), max(values)]}
        rows.append(row)
        print(json.dumps({k:v for k,v in row.items() if k != 'replicates'}), flush=True)
    payload = {'scope': 'uncertified continuum diagnostic, not an arithmetic bound',
               'power': args.power, 'replicates': args.replicates, 'rows': rows,
               'limitations': [
                   'No prime counting, allocation, phase or radial transport is inferred.',
                   'Replicate ranges are not rigorous error bounds.',
                   'The existing literal interior family already includes owners above one half.',
                   'Additional credits must be proved disjoint in the credited integral, not added as another population.'],
               'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if args.output:
        args.output.write_text(json.dumps(payload, indent=2)+'\n')


if __name__ == '__main__':
    main()

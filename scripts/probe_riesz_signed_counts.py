#!/usr/bin/env python3
"""Optional continuum signed-count diagnostic, not an arithmetic theorem.

Sample the symmetric log-share simplex with a deterministic scrambled
Sobol rule. Every subset sign of the Riesz coefficient is retained before
splitting the resulting real coefficient into positive and negative parts.
The k! symmetry divisor and (k-1)! simplex sampling density are explicit.
No prime counts, allocation, phase transport, source limit or rounding
certificate is inferred. In particular this cannot be used to pay a Lean
carrier term. It is intended to choose the next literal inequality.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path

import numpy as np
from scipy.special import gammaln
from scipy.stats import qmc


def count_sample(k, power, seed, lam, least, largest):
    points = qmc.Sobol(k, scramble=True, seed=seed).random_base2(power)
    # Normalized independent exponential variables are uniform Dirichlet(1).
    logs = -np.log(points)
    shares = logs / logs.sum(axis=1, keepdims=True)
    retained = ((shares.min(axis=1) >= least) &
                (shares.max(axis=1) <= largest))
    x = shares[retained]
    # Reflect to the shorter cutoff, keeping the exact (-1)^k sign.
    d = 1-lam
    response = np.full(len(x), d)
    subset_sums = [np.zeros(len(x))]
    for i in range(k):
        subset_sums += [s + x[:, i] for s in subset_sums]
    for bits, value in enumerate(subset_sums[1:], 1):
        response += (-1 if bits.bit_count() % 2 else 1)*np.maximum(d-value, 0)
    coefficient = -((-1)**k)*response/lam
    weight = np.exp(-np.log(x).sum(axis=1)-gammaln(k+1)-gammaln(k))
    terms = coefficient*weight
    scale = len(points)
    # These split the final coefficient, not its constituent subset terms.
    return dict(positive=float(np.maximum(terms, 0).sum()/scale),
                negative=float(np.maximum(-terms, 0).sum()/scale),
                signed=float(terms.sum()/scale), samples=scale,
                retained=int(retained.sum()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--power', type=int, default=16)
    parser.add_argument('--replicates', type=int, default=4)
    parser.add_argument('--max-count', type=int, default=8)
    parser.add_argument('--ratio', type=float, default=.693)
    parser.add_argument('--least', type=float, default=.001)
    parser.add_argument('--largest', type=float, default=.601)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    assert 0 < args.least < args.largest < 1
    assert .5 < args.ratio < 1 and args.max_count >= 3
    rows = []
    for k in range(3, args.max_count+1):
        samples = [count_sample(k, args.power, 12000+k*100+i,
                               args.ratio, args.least, args.largest)
                   for i in range(args.replicates)]
        row = {'prime_count': k, 'replicates': samples}
        for key in ('positive', 'negative', 'signed'):
            values = [s[key] for s in samples]
            row[key] = float(np.mean(values))
            row[key+'_replicate_range'] = [min(values), max(values)]
        rows.append(row)
        print(json.dumps({k:v for k,v in row.items() if k!='replicates'}), flush=True)
    payload = dict(scope='uncertified continuum diagnostic, not a literal prime-sum bound',
                   ratio=args.ratio, least=args.least, largest=args.largest,
                   power=args.power, replicates=args.replicates, rows=rows,
                   limitations=[
                       'Replicate ranges are diagnostics, not certified error intervals.',
                       'No original factorial allocation or complex phase is transported.',
                       'The omitted prime-count tail and deleted share regions are unpaid.',
                       'These masses are not independent additive supplies for existing ledgers.'],
                   source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    if args.output:
        args.output.write_text(json.dumps(payload, indent=2)+'\n')


if __name__ == '__main__':
    main()

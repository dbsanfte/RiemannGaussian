#!/usr/bin/env python3
"""Optional exact-integer squarefree sharp-cutoff diagnostic.

Keeps the full signed divisor prefix and its exact reflected endpoint.
Integer second moments and reflection checks are exact; reported ratios
use floating arithmetic. This is not a source-scale carrier certificate
and is not run by ordinary CI.
"""
import argparse
import json
import numpy as np
from probe_riesz_sieve_mean import arithmetic


def probe(population, cutoffs):
    mu, _ = arithmetic(population)
    n = np.arange(population + 1, dtype=np.int64)
    selected = (mu != 0) & (n > 1)
    response = np.zeros(population + 1, dtype=np.int64)
    previous = 0
    rows = []
    for cutoff in sorted(cutoffs):
        for d in range(previous + 1, min(cutoff, population) + 1):
            response[d::d] += int(mu[d])
        previous = min(cutoff, population)
        dual = np.zeros(population + 1, dtype=np.int64)
        qmax = population // cutoff
        for q in range(qmax + 1):
            lo, hi = q * cutoff + 1, min(population, (q + 1) * cutoff)
            for d in range(1, q + 1):
                start = ((lo + d - 1) // d) * d
                dual[start:hi + 1:d] += int(mu[d])
        reflected = -mu.astype(np.int64) * dual
        assert np.array_equal(response[selected], reflected[selected])
        square = int(np.dot(response[selected], response[selected]))
        rows.append({
            'population': population, 'cutoff': cutoff,
            'squarefreeNonunitSecondMoment': square,
            'secondMomentOverPopulation': square / population,
            'originalFloorErrorOverPopulation': cutoff**2 / population,
            'dualBlockFloorErrorOverPopulation':
                sum(q*q for q in range(qmax+1)) / population,
            'dualCubicErrorOverPopulation': qmax**3 / population,
            'dualPairErrorOverPopulation': qmax**2 / population,
            'minimumSquareErrorOverPopulation': min(cutoff**2, qmax**2) / population,
            'dualUniformRange': population**2 <= cutoff**3,
            'exactReflectionVerified': True,
        })
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--population', type=int, default=200000)
    parser.add_argument('--cutoffs', type=int, nargs='+', default=[200, 500, 2000, 5000, 10000, 100000])
    args = parser.parse_args()
    if args.population < 2 or min(args.cutoffs) < 1:
        parser.error('Population must be at least two and cutoffs positive')
    print(json.dumps({'scope': __doc__.strip(),
                     'rows': probe(args.population, args.cutoffs)}, indent=2))


if __name__ == '__main__':
    main()

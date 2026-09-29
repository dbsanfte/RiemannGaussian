#!/usr/bin/env python3
"""Optional finite squarefree cutoff-family Gram diagnostic.

Möbius prefixes are literal integer sums on squarefree nonunit labels.
Gram eigenvalues and normalized costs use floating arithmetic. No zeta
phase, source floor, or whole prime-period bound is certified here.
This probe is not part of ordinary CI.
"""
import json
import numpy as np
from probe_riesz_sieve_mean import arithmetic


def probe(population):
    mu, _ = arithmetic(population)
    labels = np.arange(population + 1, dtype=np.int64)
    selected = (mu != 0) & (labels > 1)
    cutoffs = [2**i for i in range(population.bit_length())]
    response = np.zeros(population + 1, dtype=np.int64)
    columns = []
    previous = 0
    for cutoff in cutoffs:
        for d in range(previous + 1, cutoff + 1):
            if mu[d]:
                response[d::d] += int(mu[d])
        previous = cutoff
        columns.append(response[selected].astype(np.float64))
    matrix = np.stack(columns, axis=1)
    gram = matrix.T @ matrix / population
    rows = []
    for count in sorted(set([4, 8, 12, len(cutoffs)])):
        count = min(count, len(cutoffs))
        q = gram[:count, :count]
        a = (-1.0)**np.arange(count)
        rows.append({'cutoffCount': count,
                     'largestGramEigenvalueOverPopulation': float(np.linalg.eigvalsh(q)[-1]),
                     'largestIndividualMeanOverPopulation': float(np.max(np.diag(q))),
                     'alternatingMeanOverPopulationAndCoefficientEnergy': float(a @ q @ a / count)})
    return {'population': population, 'cutoffs': cutoffs, 'rows': rows}


if __name__ == '__main__':
    print(json.dumps({'scope': __doc__.strip(),
                      'populations': [probe(x) for x in (32768, 131072, 524288)]}, indent=2))

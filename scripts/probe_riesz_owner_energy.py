#!/usr/bin/env python3
"""Optional finite diagnostic of the all-count cofactor energy.

Prime incidences, squarefree masks and largest primes are computed on
literal integers. Normalized energies use floating arithmetic. This is
not a carrier/source-scale certificate and is not run by ordinary CI.
"""
import json
import numpy as np


def probe(x):
    counts = np.zeros(x + 1, dtype=np.int32)
    largest = np.zeros(x + 1, dtype=np.int32)
    squarefree = np.ones(x + 1, dtype=bool)
    primes = []
    for p in range(2, x + 1):
        if counts[p] == 0:
            primes.append(p)
            counts[p::p] += 1
            largest[p::p] = p
            if p * p <= x:
                squarefree[p*p::p*p] = False
    labels = np.arange(x // 2 + 1, x + 1)
    selected = labels[squarefree[labels]]
    logs = np.log(selected)
    harmonic = float(sum(1 / p for p in primes))
    count_energy = float(np.sum((counts[selected] / (selected * logs))**2))
    largest_energy = float(np.sum(1 / (selected * np.log(largest[selected]))**2))
    return {
        "population": x,
        "reciprocalPrimeMass": harmonic,
        "meanDistinctPrimeCountSquared": float(np.sum(counts[1:].astype(float)**2) / x),
        "provedCountMomentUpper": harmonic**2 + harmonic,
        "countBasedSquarefreeEnergy": count_energy,
        "largestPrimeSquarefreeEnergy": largest_energy,
        "energyTimesPopulationLogHalfSquared": count_energy * x * np.log(x / 2)**2,
        "provedShellUpperInSameNormalization": 4 * (harmonic**2 + harmonic),
    }


if __name__ == "__main__":
    print(json.dumps({"scope": __doc__.strip(),
                      "rows": [probe(x) for x in (32768, 262144, 1048576)]}, indent=2))

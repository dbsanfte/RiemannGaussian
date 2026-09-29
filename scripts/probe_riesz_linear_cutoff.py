#!/usr/bin/env python3
"""Optional finite arithmetic diagnostic for the linear Riesz cutoff cost.

Keeps the exact integer Mobius coefficients and every signed divisor term,
with floating logarithms. The unit is excluded. This is not a source-scale
carrier certificate or a numerical bound on the Lean existential constant.
It is not run by ordinary CI.
"""
import argparse
import json
import math

import numpy as np

from probe_riesz_sieve_mean import arithmetic


def probe(population):
    mu, phi = arithmetic(population)
    labels = np.arange(population + 1)
    selected = (mu != 0) & (labels > 1)
    composite = selected & ~((labels >= 2) & (phi == labels - 1))
    log_population = math.log(population)
    cutoffs = sorted(set(
        [q * log_population for q in (.15, .3, .5, .7, .95, 1.1)]
        + [.5 * log_population + .01, .5 * log_population + .1]
    ))
    values = np.zeros((len(cutoffs), population + 1))
    cutoff_array = np.array(cutoffs)
    for divisor in np.flatnonzero(mu[1:]) + 1:
        coefficient = int(mu[divisor]) * np.maximum(0, cutoff_array - math.log(divisor))
        values[:, divisor::divisor] += coefficient[:, None]
    rows = []
    for i, lower in enumerate(cutoffs):
        for j in range(i + 1, len(cutoffs)):
            upper = cutoffs[j]
            displacement = upper - lower
            difference = values[j] - values[i]
            denominator = population * min(displacement**2, displacement)
            rows.append({
                "population": population,
                "lowerOverLogPopulation": lower / log_population,
                "upperOverLogPopulation": upper / log_population,
                "displacement": displacement,
                "meanOverMinCost": float(difference[selected] @ difference[selected] / denominator),
                "compositeMeanOverMinCost": float(
                    difference[composite] @ difference[composite] / denominator),
            })
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--populations", nargs="+", type=int,
                        default=[16384, 65536, 262144])
    args = parser.parse_args()
    if min(args.populations) < 2:
        parser.error("Populations must be at least two")
    rows = [row for population in args.populations for row in probe(population)]
    print(json.dumps({
        "scope": __doc__.strip(),
        "rows": rows,
        "maxRatio": max(row["meanOverMinCost"] for row in rows),
        "maxCompositeRatio": max(row["compositeMeanOverMinCost"] for row in rows),
    }, indent=2))


if __name__ == "__main__":
    main()

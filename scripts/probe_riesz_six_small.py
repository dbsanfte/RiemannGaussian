#!/usr/bin/env python3
"""Optional numerical guide to the six-small-prime signed inequality.

This samples normalized logarithms, not primes.  The separate Lean theorem
proves the inequality for all real logarithms in the stated chamber.
Nothing in this script is imported by a proof or run by ordinary CI.
Run with a Python environment containing numpy and scipy.
"""

import argparse
import json
from itertools import combinations

import numpy as np
from scipy.stats import qmc


def response(logs, cutoff):
    result = np.zeros(len(logs))
    for count in range(7):
        for subset in combinations(range(6), count):
            result += (-1) ** count * np.maximum(
                cutoff - logs[:, subset].sum(axis=1), 0
            )
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--power", type=int, default=18)
    args = parser.parse_args()
    cuts = np.sort(qmc.Sobol(5, scramble=True, seed=63).random_base2(args.power), axis=1)
    shares = np.diff(
        np.column_stack((np.zeros(len(cuts)), cuts, np.ones(len(cuts)))), axis=1
    )
    rows = []
    for cutoff in (0.22, 0.25, 0.28, 0.3, 0.307, 0.32, 1 / 3):
        selected = shares[shares.max(axis=1) <= cutoff]
        ratio = response(selected, cutoff) / selected.min(axis=1)
        index = np.argmax(ratio)
        rows.append(
            {
                "cutoff_over_total_log": cutoff,
                "samples": len(selected),
                "minimum_response_over_least_log": float(ratio.min()),
                "maximum_response_over_least_log": float(ratio[index]),
                "maximizing_sample_shares": sorted(selected[index].tolist()),
            }
        )
    # The window integrand can reach three, so the integral bound one
    # cannot be proved by bounding each individual window by one.
    logs = np.array([0.12612928, 0.12791928, 0.13911228, 0.14391282, 0.15694231, 0.30598403])
    v = 0.307 - 0.003906335454942469
    window = 0
    for count in range(5):
        for subset in combinations(range(2, 6), count):
            value = sum(logs[i] for i in subset)
            window += (-1) ** count * int(v - logs[1] < value < v)
    print(json.dumps({"status": "uncertified exploration", "rows": rows,
                      "window_shortcut_counterexample_value": window}, indent=2))


if __name__ == "__main__":
    main()

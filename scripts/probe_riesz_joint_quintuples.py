#!/usr/bin/env python3
"""Optional exact rational-log probe, not a discrete prime-sum certificate."""

import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path


def kernel(shares, length):
    return sum(
        (-1) ** size * max(F(0), length - sum((shares[i] for i in subset), F(0)))
        for size in range(len(shares) + 1)
        for subset in combinations(range(len(shares)), size)
    )


def check(large, small, length):
    terms = [kernel(small, length - x - y) for x, y in combinations(large, 2)]
    full = kernel(large + small, length)
    assert full == sum(terms)
    assert 0 <= full <= 2 * min(small)
    assert sum(value != 0 for value in terms) <= 2
    return full, terms


def main():
    total, length, budget = F(2), F(137, 100), F(1, 2048)
    small = [budget / 4, 3 * budget / 4]
    large = [2 * length - total,
             total - length - budget / 2 + budget / 8,
             total - length - budget / 2 - budget / 8]
    full, terms = check(large, small, length)
    assert full == 2 * min(small)
    grids = []
    for size in (32, 64, 128):
        tested = 0
        for i in range(1, size):
            p = total * i / size
            for j in range(1, size - i):
                q = total * j / size
                r = total - budget - p - q
                if min(p, q, r) <= budget or max(p, q, r) > F(601, 1000) * total:
                    continue
                check([p, q, r], small, length)
                tested += 1
        grids.append({"grid": size, "exact_rational_cases": tested})
    result = {
        "scope": "Exact rational logarithmic model, not actual prime populations or a signed sum",
        "lean_source": "RiemannGaussian/ZetaRieszJointQuintupleFloor.lean",
        "extremal_example": {
            "large_logs_per_order": list(map(str, large)),
            "small_logs_per_order": list(map(str, small)),
            "length_per_order": str(length),
            "total_log_per_order": str(total),
            "pair_tents": list(map(str, terms)),
            "full_Riesz_response": str(full),
            "two_least_log_bound": str(2 * min(small)),
        },
        "grids": grids,
        "limitations": [
            "No assertion that the listed rational shares are prime logarithms.",
            "The formal core theorem derives the small-factor budget from literal masks.",
            "No distribution, phase correlation, source-scale floor, or zero exclusion is tested.",
        ],
    }
    output = Path(__file__).resolve().parents[1] / "docs/riesz-joint-quintuple-probe.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Wrote {output.relative_to(output.parent.parent)}; {sum(r['exact_rational_cases'] for r in grids)} rational cases")


if __name__ == "__main__":
    main()

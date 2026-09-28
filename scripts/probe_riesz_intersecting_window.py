#!/usr/bin/env python3
"""Optional rational-weight exploration of odd-count Riesz inequalities.

Weights model logarithms, not actual prime labels. The data neither
certify extrema nor prove prime-density or source-normalized estimates.
"""
from __future__ import annotations

import argparse
import json
import math
import random
from fractions import Fraction
from pathlib import Path

from probe_riesz_complement_window import subset_profile

ROOT = Path(__file__).resolve().parents[1]


def quotas(k: int) -> list[Fraction]:
    """The two capacities proved in ZetaRieszIntersectingWindow."""
    capacities = [Fraction(max(math.comb(k, j) for j in range(k + 1)
                              if j % 2 == b)) for b in (0, 1)]
    j = (k + 1) // 2
    parity = j % 2
    central = math.comb(k, j)
    off_rank = max(math.comb(k, i) for i in range(k + 1)
                   if i % 2 == parity and i != j)
    quota = math.comb(k - 1, k - j - 1)
    capacities[parity] = min(capacities[parity],
                             off_rank + Fraction(central - off_rank, central) * quota)
    if k == 5:
        capacities[1] = Fraction(5)
    return capacities


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--samples', type=int, default=240)
    parser.add_argument('--output', type=Path,
                        default=ROOT / 'docs/riesz-intersecting-window-probe.json')
    args = parser.parse_args()
    if args.samples < 1:
        parser.error('--samples must be positive')
    rng = random.Random(20260929)
    rows = []
    for count in (7, 9, 11):
        examples = [[100] * count, [1] + [100] * (count - 1),
                    list(range(100, 100 + count))]
        examples += [sorted(rng.randint(1, 1000) for _ in range(count))
                     for _ in range(args.samples)]
        lo = hi = None
        lo_at = hi_at = None
        for weights in examples:
            terms = subset_profile(weights)
            for length in (Fraction(2, 3), Fraction(27, 40), Fraction(69, 100),
                           Fraction(7, 10), Fraction(71, 100)):
                cutoff = (1 - length) * sum(weights)
                num, den = cutoff.numerator, cutoff.denominator
                response = sum(sign * max(num - den * value, 0)
                               for value, sign in terms)
                # At odd counts reflection reverses the Riesz sign, so
                # the coefficient divided by (T/L)*leastShare is +R_D/leastShare.
                ratio = Fraction(response, den * min(weights))
                record = {'weights': weights, 'length_share': str(length)}
                if lo is None or ratio < lo:
                    lo, lo_at = ratio, record
                if hi is None or hi < ratio:
                    hi, hi_at = ratio, record
        even, odd = quotas(count - 2)
        old = math.comb(count - 2, (count - 2) // 2)
        if not -odd <= lo <= hi <= even:
            raise RuntimeError(f'quantitative regression at count {count}')
        rows.append({
            'prime_count_model': count,
            'old_coefficient_capacities': [-old, old],
            'proved_new_coefficient_capacities': [str(-odd), str(even)],
            'model_observed_min': str(lo), 'model_observed_max': str(hi),
            'model_min_at': lo_at, 'model_max_at': hi_at,
            'coefficient_units': '(log(n)/L)*log(minFac(n))',
        })
    result = {
        'schema': 1, 'seed': 20260929, 'random_weight_samples_per_count': args.samples,
        'model_only': True, 'prime_sum_certificate': False,
        'description': 'Exact rational finite differences; no prime realization, extremality or density transport.',
        'rows': rows,
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    for row in rows:
        print(row['prime_count_model'], row['old_coefficient_capacities'], '->',
              row['proved_new_coefficient_capacities'], 'observed',
              row['model_observed_min'], row['model_observed_max'])


if __name__ == '__main__':
    main()

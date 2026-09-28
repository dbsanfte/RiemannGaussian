#!/usr/bin/env python3
"""Optional exact-rational probe of reflected Riesz subset geometry.

These positive integer weights model prime logarithms; they are NOT prime
labels or a signed prime-sum certificate. No model result enters Lean.
"""
from __future__ import annotations

import argparse
import json
import math
import random
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def capacity(k: int, parity: int) -> Fraction:
    layers = [math.comb(k, j) for j in range(k + 1) if j % 2 == parity]
    old = max(layers, default=0)
    if k >= 4 and k % 2 == 0 and (k // 2) % 2 == parity:
        off = max((math.comb(k, j) for j in range(k + 1)
                   if j % 2 == parity and j != k // 2), default=0)
        return Fraction(math.comb(k, k // 2) + off, 2)
    return Fraction(old)


def subset_profile(weights: list[int]) -> list[tuple[int, int]]:
    terms = [(0, 1)]
    for weight in weights:
        terms += [(value + weight, -sign) for value, sign in terms]
    return terms


def normalized_coefficient(weights: list[int], length: Fraction,
                           terms: list[tuple[int, int]]) -> Fraction:
    # Reflection has positive sign at the even counts tested here.
    cutoff = (1 - length) * sum(weights)
    num, den = cutoff.numerator, cutoff.denominator
    response = sum(sign * max(num - den * value, 0) for value, sign in terms)
    return Fraction(-response, den * min(weights))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--samples', type=int, default=240)
    parser.add_argument('--output', type=Path,
                        default=ROOT / 'docs/riesz-complement-window-probe.json')
    args = parser.parse_args()
    if args.samples < 1:
        parser.error('--samples must be positive')
    rng = random.Random(20260928)
    rows = []
    for count in (8, 10, 12):
        examples = [[100] * count, [100] * (count - 1) + [300],
                    list(range(100, 100 + count))]
        for _ in range(args.samples):
            examples.append(sorted(rng.randint(1, 1000) for _ in range(count)))
        lo, hi = None, None
        lo_at, hi_at = None, None
        for weights in examples:
            terms = subset_profile(weights)
            for cutoff in (Fraction(2, 3), Fraction(27, 40), Fraction(69, 100),
                           Fraction(7, 10), Fraction(71, 100)):
                value = normalized_coefficient(weights, cutoff, terms)
                record = {'weights': weights, 'length_share': str(cutoff)}
                if lo is None or value < lo:
                    lo, lo_at = value, record
                if hi is None or hi < value:
                    hi, hi_at = value, record
        k = count - 2
        rows.append({
            'prime_count_model': count,
            'old_signed_capacities': [
                -max(math.comb(k, j) for j in range(0, k + 1, 2)),
                max(math.comb(k, j) for j in range(1, k + 1, 2))],
            'proved_new_signed_capacities': [str(-capacity(k, 0)), str(capacity(k, 1))],
            'model_observed_min': str(lo), 'model_observed_max': str(hi),
            'model_min_at': lo_at, 'model_max_at': hi_at,
            'coefficient_units': '(log(n)/L)*log(minFac(n))',
        })
    result = {
        'schema': 1, 'seed': 20260928, 'random_weight_samples_per_count': args.samples,
        'model_only': True, 'prime_sum_certificate': False,
        'description': 'Exact subset arithmetic on positive integer logarithmic weights; no prime realization or density transport.',
        'rows': rows,
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    for row in rows:
        print(row['prime_count_model'], row['old_signed_capacities'], '->',
              row['proved_new_signed_capacities'], 'observed',
              row['model_observed_min'], row['model_observed_max'])


if __name__ == '__main__':
    main()

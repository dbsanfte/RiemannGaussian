#!/usr/bin/env python3
"""Optional exact rational check of the reflected-prime coefficient costs.

The weights model logarithms, not actual prime labels. Lean proves the
arithmetic inequalities independently. This probe does not estimate a
source-normalized prime sum, an allocation error, or a population density.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import random

from probe_riesz_complement_window import subset_profile

ROOT = Path(__file__).resolve().parents[1]
PREVIOUS = {6: (3, 4), 7: (5, 10), 8: (15, 13), 9: (35, 27), 10: (49, 56)}


def capacity(k: int, outer: int, side: int) -> int:
    if outer >= 3:
        return 0
    remaining = k - outer - 2
    parity = k % 2 if side == 0 else 1 - k % 2
    return max((math.comb(remaining, j) for j in range(remaining + 1)
                if j % 2 == parity), default=0)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--samples', type=int, default=240)
    parser.add_argument('--output', type=Path,
                        default=ROOT / 'docs/riesz-reflected-primes-probe.json')
    args = parser.parse_args()
    if args.samples < 1:
        parser.error('--samples must be positive')
    rng = random.Random(20260928)
    rows = []
    for k, old in PREVIOUS.items():
        examples = [[1] + [10] * (k - 2) + [40],
                    [1] + [10] * (k - 3) + [50, 51],
                    [1] * (k - 3) + [40, 41, 42],
                    [1] + [100] * (k - 1)]
        examples += [sorted(rng.randint(1, 1000) for _ in range(k))
                     for _ in range(args.samples)]
        groups = {}
        for weights in examples:
            terms = subset_profile(weights)
            for cutoff_share in (Fraction(29, 100), Fraction(307, 1000), Fraction(8, 25)):
                cutoff = cutoff_share * sum(weights)
                outer = sum(w >= cutoff for w in weights)
                active = [w for w in weights if w < cutoff]
                num, den = cutoff.numerator, cutoff.denominator
                response = sum(sign * max(num - den * w, 0) for w, sign in terms)
                active_response = sum(sign * max(num - den * w, 0)
                                      for w, sign in subset_profile(active))
                assert response == active_response
                ratio = Fraction(-((-1) ** k) * response, den * min(weights))
                bounds = tuple(min(old[b], capacity(k, outer, b)) for b in (0, 1))
                if k in (6, 7) and outer == 2:
                    # This is the proved second-reflection improvement, not
                    # a fitted capacity or an inferred population estimate.
                    bounds = (min(bounds[0], 1), min(bounds[1], 1) if k == 6 else bounds[1])
                    reflected = sum(active) - cutoff
                    reflected_response = sum(sign * max(reflected - w, 0)
                                             for w, sign in subset_profile(active))
                    assert Fraction(response, den) == (-1) ** k * reflected_response
                    assert 3 * reflected <= sum(active)
                    if k == 6:
                        assert reflected_response >= -min(weights)
                    else:
                        assert reflected_response <= min(weights)
                assert -bounds[0] <= ratio <= bounds[1], (k, weights, cutoff, ratio)
                if outer >= 3:
                    assert ratio == 0
                group = groups.setdefault(outer, dict(samples=0, lower=ratio, upper=ratio,
                                                       lower_at=None, upper_at=None,
                                                       proved_capacities=[-bounds[0], bounds[1]]))
                record = dict(weights=weights, reflected_cutoff_share=str(cutoff_share))
                if ratio <= group['lower']:
                    group['lower'], group['lower_at'] = ratio, record
                if ratio >= group['upper']:
                    group['upper'], group['upper_at'] = ratio, record
                group['samples'] += 1
        for outer, group in sorted(groups.items()):
            group['lower'], group['upper'] = str(group['lower']), str(group['upper'])
            rows.append(dict(prime_count_model=k, reflected_large_count=outer,
                             previous_capacities=[-old[0], old[1]], **group))
    second_reflection_endpoints = []
    for k, weights, cutoff, expected in (
        (6, [1, 4, 5, 6, 16, 17], 15, -1),
        (6, [1, 1, 1, 7, 8, 8], 8, 1),
        (7, [1, 1, 1, 1, 10, 11, 11], 11, -1),
        (7, [1, 10, 10, 10, 10, 31, 31], 30, 3),
    ):
        total = sum(weights)
        outer = sum(w >= cutoff for w in weights)
        active = [w for w in weights if w < cutoff]
        response = sum(sign * max(cutoff-w, 0) for w, sign in subset_profile(weights))
        ratio = Fraction(-(-1) ** k * response, min(weights))
        assert outer == 2 and 7*cutoff >= 2*total and ratio == expected
        second_reflection_endpoints.append(dict(
            prime_count_model=k, weights=weights, total=total, reflected_cutoff=cutoff,
            reflected_cutoff_share=str(Fraction(cutoff, total)),
            active_weights=active, second_cutoff=sum(active)-cutoff,
            coefficient_ratio=str(ratio), model_only=True))
    result = dict(schema=1, seed=20260928, random_weight_samples_per_count=args.samples,
                  model_only=True, prime_sum_certificate=False,
                  coefficient_units='(log(n)/L)*log(minFac(n))',
                  limitations=[
                      'Exact rational model weights are not actual prime logarithms.',
                      'Sampled extrema are not certified extrema.',
                      'No density, phase, or source-normalized mass is transported.',
                      'The complete signed rest is not bounded by this probe.'],
                  rows=rows, second_reflection_endpoints=second_reflection_endpoints,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    for row in rows:
        print(row['prime_count_model'], row['reflected_large_count'],
              row['previous_capacities'], '->', row['proved_capacities'],
              'observed', row['lower'], row['upper'])


if __name__ == '__main__':
    main()

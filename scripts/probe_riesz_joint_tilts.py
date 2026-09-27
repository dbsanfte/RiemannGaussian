#!/usr/bin/env python3
"""Optional scalar diagnostic for the two existing allocation tails.

This optimizes an exponential envelope, not the arithmetic signed sum.
Floating results are not certificates. The concrete 293/500 and 601/1000
endpoints and the 59% / 60% all-tilt obstructions are proved separately in
the JointAllocationFloor / JointDominantFloor Lean modules.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path


U = 10001 / 20000
B = 13 / 32
GROWTH = math.log(U * 262144 / 131071)


def gain(share, tilt=None):
    x = 1 - share
    if tilt is None:
        tilt = B * (1 - x) / (x * (1 - B))
    return B * math.log(tilt) - math.log1p((tilt - 1) * x) - GROWTH


def root(lo, hi):
    """Bisection for the diagnostic boundary, without interval certification."""
    assert gain(lo) * gain(hi) < 0
    for _ in range(60):
        mid = (lo + hi) / 2
        if gain(lo) * gain(mid) <= 0:
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    shares = [9 / 16, 293 / 500, 59 / 100, 19 / 32,
              3 / 5, 601 / 1000, 121 / 200]
    payload = {
        'scope': 'uncertified scalar tilt optimization; no prime-sum bound',
        'radius': U,
        'order_endpoint': B,
        'source_envelope_log_growth': GROWTH,
        'rows': [
            {'largest_prime_share': p,
             'optimal_tilt': B * p / ((1 - p) * (1 - B)),
             'normalized_saving': gain(p)} for p in shares
        ],
        'concrete_tilts': [
            {'largest_prime_share': 293 / 500, 'tilt': 97 / 100,
             'normalized_saving': gain(293 / 500, 97 / 100),
             'lean_saving_at_least': 1 / 100000},
            {'largest_prime_share': 601 / 1000, 'tilt': 103 / 100,
             'normalized_saving': gain(601 / 1000, 103 / 100),
             'lean_saving_at_least': 1 / 1000000},
        ],
        'diagnostic_optimal_share_boundaries': [root(.58, .59), root(.60, .61)],
        'limitations': [
            'No directed roundoff or rigorous root enclosure',
            'Optimizes only this exponential-tilt / summable-envelope bound',
            'No lower bound on the actual allocation tails is asserted',
            'The raw signed sum and transition remain unbounded',
        ],
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.output.write_text(json.dumps(payload, indent=2) + '\n')


if __name__ == '__main__':
    main()

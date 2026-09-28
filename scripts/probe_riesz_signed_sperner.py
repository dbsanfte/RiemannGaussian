#!/usr/bin/env python3
"""Optional signed divisor-capacity diagnostic; not a prime-sum certificate.

Compare the exact parity-specific binomial capacities with a continuous
log-share probe. The rational six-share witness is evaluated exactly by
Python fractions, while sampled extrema are only floating diagnostics.
Neither asserts a density, source-scale saving, or a literal prime label.
The general arithmetic inequalities are proved separately in Lean.
"""

import argparse
from fractions import Fraction
import hashlib
from itertools import product
import json
import math
from pathlib import Path

import numpy as np
from scipy.stats import qmc


def capacities(k):
    dimension = k - 2
    even = max(math.comb(dimension, j) for j in range(0, dimension + 1, 2))
    odd = max((math.comb(dimension, j) for j in range(1, dimension + 1, 2)), default=0)
    return dict(prime_count=k, coefficient_lower_capacity=even,
                coefficient_upper_capacity=odd,
                previous_symmetric_capacity=math.comb(dimension, dimension // 2))


def sample(k, power):
    points = qmc.Sobol(k + 1, scramble=True, seed=67000 + k).random_base2(power)
    exps = -np.log(points[:, :k])
    shares = exps / exps.sum(axis=1, keepdims=True)
    lam = 2/3 + points[:, k] / 12
    keep = (shares.max(axis=1) <= .601) & (shares.min(axis=1) > 1e-10)
    x, d = shares[keep], 1-lam[keep]
    response = np.zeros(len(x))
    for bits in product((0, 1), repeat=k):
        response += (-1)**sum(bits) * np.maximum(d-x @ bits, 0)
    ratio = -((-1)**k) * response / x.min(axis=1)
    return dict(prime_count=k, samples=len(points), retained=len(x),
                sampled_lower=float(ratio.min()), sampled_upper=float(ratio.max()))


def rational_witness():
    numerators = [2, 149200, 189530, 192440, 226300, 242528]
    x = [Fraction(v, 1000000) for v in numerators]
    lam = Fraction(739383, 1000000)
    response = sum((-1)**sum(bits) *
                   max(Fraction(0), 1-lam-sum(a*b for a, b in zip(x, bits)))
                   for bits in product((0, 1), repeat=6))
    return dict(share_numerators=numerators, denominator=1000000,
                cutoff_ratio=str(lam), share_sum=str(sum(x)),
                reflected_response=str(response),
                coefficient_ratio_without_T_over_L=str(-response/min(x)))


def core_rational_witness(numerators, reflected_cutoff):
    denominator = sum(numerators)
    x = [Fraction(v, denominator) for v in numerators]
    d = Fraction(reflected_cutoff, denominator)
    response = sum((-1)**sum(bits) *
                   max(Fraction(0), d-sum(a*b for a, b in zip(x, bits)))
                   for bits in product((0, 1), repeat=6))
    return dict(share_numerators=numerators, denominator=denominator,
                cutoff_ratio=str(1-d), reflected_response=str(response),
                coefficient_ratio_without_T_over_L=str(-response/min(x)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--power', type=int, default=15)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    rows = [sample(k, args.power) for k in range(3, 9)]
    payload = dict(
        scope='Optional log-share diagnostic; no prime density or source-scale conclusion',
        coefficient_convention='c/(T/L) = -(-1)^k H_k(1-lambda); divide by least share',
        cutoff_interval=['2/3', '3/4'], largest_share_ceiling=.601,
        power=args.power, capacities=[capacities(k) for k in range(2, 17)],
        sampled_extrema=rows, rational_six_share_witness=rational_witness(),
        core_rational_witnesses=[
            core_rational_witness([1, 80, 81, 82, 83, 330], 197),
            core_rational_witness([1, 80, 81, 82, 83, 84], 127)],
        limitations=[
            'Sampled extrema are not proved extrema or error intervals.',
            'The rational shares are not asserted to be logarithms of actual primes.',
            'No phase, factorial allocation, radial transport or prime-count tail is paid.',
            'Lean separately proves [-6,4] at all cutoffs and [-3,4] when 2T<=3L.',
            'A smaller local allowance does not establish either whole-carrier endgame bound.'],
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    for row in rows:
        print(json.dumps(row), flush=True)
    print(json.dumps(payload['rational_six_share_witness']), flush=True)
    if args.output:
        args.output.write_text(json.dumps(payload, indent=2) + '\n')


if __name__ == '__main__':
    main()

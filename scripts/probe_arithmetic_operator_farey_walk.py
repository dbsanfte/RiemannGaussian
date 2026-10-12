#!/usr/bin/env python3
"""Exact finite regression for native Farey walks; never an asymptotic proof.

Constructs adjacency from sorted reduced rational numbers, independently of
the quotient recurrence. All comparisons use integer or Fraction arithmetic.
The free inverse arrays in the collapse test are controls, not Farey measures.
"""

import argparse
import json
from fractions import Fraction
from math import gcd
from pathlib import Path


def mobius(n):
    sign = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign


def successor(cutoff, q, r):
    return cutoff - (cutoff + q) % r


def word(cutoff, q, r, length):
    values = [(q, r)]
    for _ in range(length):
        q, r = r, successor(cutoff, q, r)
        values.append((q, r))
    return values


def signed_mask(values, kind):
    if kind == 0:
        return 1
    if kind == 1:
        return sum((-1) ** i * (q - r) for i, (q, r) in enumerate(values))
    if kind == 2:
        return int(values[0][0] < values[-1][1]) - int(values[0][0] > values[-1][1])
    return sum((q + r) % 3 - 1 for q, r in values)


def run(max_cutoff):
    pair_cases = 0
    triple_cases = 0
    joined_cases = 0
    for cutoff in range(1, max_cutoff + 1):
        fractions = sorted({Fraction(a, q) for q in range(1, cutoff + 1)
                            for a in range(q + 1)})
        actual_pairs = [(a.denominator, b.denominator)
                        for a, b in zip(fractions, fractions[1:])]
        primitive_pairs = [(q, r) for q in range(1, cutoff + 1)
                           for r in range(1, cutoff + 1)
                           if cutoff < q + r and gcd(q, r) == 1]
        assert set(actual_pairs) == set(primitive_pairs)
        actual_triples = {(a.denominator, b.denominator, c.denominator)
                          for a, b, c in zip(fractions, fractions[1:], fractions[2:])}
        recurrence_triples = {(q, r, successor(cutoff, q, r))
                              for q, r in primitive_pairs if r != 1}
        assert actual_triples == recurrence_triples
        assert len(actual_triples) == len(actual_pairs) - 1
        all_pairs = [(q, r) for q in range(1, cutoff + 1)
                     for r in range(1, cutoff + 1) if cutoff < q + r]
        images = []
        for q, r in primitive_pairs:
            t = successor(cutoff, q, r)
            assert q + t == ((cutoff + q) // r) * r
            assert successor(cutoff, t, r) == q
            assert (r, t) in set(primitive_pairs)
            images.append((r, t))
        assert len(set(images)) == len(primitive_pairs)
        for length in (0, 1, 3, 9):
            words = {pair: word(cutoff, *pair, length) for pair in all_pairs}
            for kind in range(4):
                literal = sum(signed_mask(words[pair], kind) for pair in primitive_pairs)
                joined = sum(mobius(d) * sum(signed_mask(words[(q, r)], kind)
                                            for q, r in all_pairs
                                            if q % d == 0 and r % d == 0)
                             for d in range(1, cutoff + 1))
                assert literal == joined
                joined_cases += 1
        pair_cases += len(actual_pairs)
        triple_cases += len(actual_triples)
    return {
        "scope": "finite native recurrence and signed whole-word Mobius regression",
        "arithmetic": "exact integers and fractions; no floating point",
        "maxCutoff": max_cutoff,
        "nativeAdjacentPairCases": pair_cases,
        "nativeThreeFractionCases": triple_cases,
        "signedJoinedWordCases": joined_cases,
        "wordLengths": [0, 1, 3, 9],
        "signedMasks": 4,
        "checksPassed": True,
        "asymptoticArithmeticEstimate": False,
        "proofInput": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-cutoff", type=int, default=40)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.max_cutoff < 1:
        parser.error("--max-cutoff must be positive")
    result = json.dumps(run(args.max_cutoff), indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result)
    print(result, end="")


if __name__ == "__main__":
    main()

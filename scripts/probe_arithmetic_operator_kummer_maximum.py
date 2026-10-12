#!/usr/bin/env python3
"""Exact all-split Kummer regression; no asymptotic estimate or proof input.

Checks the maximum independently by enumerating every split. Actual integer
binomial valuations and symbolic log-prime coefficients keep all prime powers.
Signed arbitrary weights are pairs of integers, so no floats enter the audit.
"""

import argparse
import json
from collections import Counter
from math import comb, isqrt
from pathlib import Path


def primes_upto(cutoff):
    return [p for p in range(2, cutoff + 1)
            if all(p % q for q in range(2, isqrt(p) + 1))]


def carry(n, k, d):
    return n // d - k // d - (n - k) // d if d else 0


def valuation(n, p):
    count = 0
    while n % p == 0:
        n //= p
        count += 1
    return count


def signed_weight(d, kind):
    if kind == 0:
        return 1, 0
    if kind == 1:
        return (-1) ** d * d, d * d - 2 * d
    return (d % 7) - 3, (d % 11) - 5


def add_pairs(values):
    values = list(values)
    return sum(v[0] for v in values), sum(v[1] for v in values)


def run(max_row):
    maxima_cases = 0
    common_witness_cases = 0
    valuation_cases = 0
    weighted_cases = 0
    symbolic_prime_power_cases = 0
    for n in range(max_row + 1):
        x = n + 1
        maxima = {}
        for d in range(x + 9):
            literal = max(carry(n, k, d) for k in range(n + 1))
            expected = int(0 < d <= x and x % d != 0)
            assert literal == expected, (n, d, literal, expected)
            maxima[d] = literal
            maxima_cases += 1
        for kind in range(3):
            lhs = add_pairs((maxima[d] * signed_weight(d, kind)[0],
                             maxima[d] * signed_weight(d, kind)[1])
                            for d in range(1, x + 1))
            prefix = add_pairs(signed_weight(d, kind) for d in range(1, x + 1))
            endpoint = add_pairs(signed_weight(d, kind)
                                 for d in range(1, x + 1) if x % d == 0)
            assert lhs == (prefix[0] - endpoint[0], prefix[1] - endpoint[1])
            weighted_cases += 1
        prefix = Counter()
        endpoint = Counter()
        packet = Counter()
        for p in primes_upto(x):
            j, power = 0, 1
            while power * p <= x:
                power *= p
                j += 1
            witness = power - 1
            assert 0 <= witness <= n
            for i in range(j + 4):
                d = p ** i
                whole_max = max(carry(n, k, d) for k in range(n + 1))
                assert carry(n, witness, d) == whole_max
                common_witness_cases += 1
            row_vals = [valuation(comb(n, n - k), p) for k in range(n + 1)]
            assert max(row_vals) == row_vals[witness]
            assert max(row_vals) == j - valuation(x, p)
            valuation_cases += len(row_vals)
            power = p
            while power <= x:
                prefix[p] += 1
                endpoint[p] += int(x % power == 0)
                packet[p] += maxima[power]
                symbolic_prime_power_cases += 1
                power *= p
        assert packet == prefix - endpoint
        assert endpoint == Counter({p: valuation(x, p) for p in primes_upto(x)
                                    if x % p == 0})
    return {
        "scope": "exact finite all-split maxima, common prime-power witness and joined endpoints",
        "arithmetic": "integers and symbolic prime logarithms; no floating point",
        "maxRow": max_row,
        "rowMaximumCases": maxima_cases,
        "commonPrimePowerWitnessCases": common_witness_cases,
        "actualBinomialValuationCases": valuation_cases,
        "signedArbitraryWeightJoins": weighted_cases,
        "symbolicActualPrimePowerCases": symbolic_prime_power_cases,
        "checksPassed": True,
        "asymptoticArithmeticEstimate": False,
        "proofInput": False,
        "fullRowLCMFormalClaim": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-row", type=int, default=128)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.max_row < 0:
        parser.error("--max-row must be nonnegative")
    result = json.dumps(run(args.max_row), indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result)
    print(result, end="")


if __name__ == "__main__":
    main()

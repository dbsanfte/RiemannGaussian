#!/usr/bin/env python3
"""Optional symmetry and joined-price regression; not a floor certificate."""
from fractions import Fraction as F
from itertools import combinations
from math import exp, factorial, log, prod
import json


def main():
    primes = [2, 3, 5, 11, 101, 1009, 10007]
    mass = sum((F(1, p) for p in primes), F())
    counts = []
    for k in range(len(primes) + 1):
        exact = sum((F(1, prod(s)) for s in combinations(primes, k)), F())
        assert factorial(k) * exact <= mass**k
        counts.append({"count": k, "squarefree_mass": str(exact),
                       "factorial_symmetry_ratio": float(factorial(k) * exact / mass**k)})
    assert log(primes[-1]) / log(primes[0]) > 4
    rows = []
    for a, h in [(5000, 10000), (5000, 100000), (10000, 1000000)]:
        m = log(4 * h / a) + 1 / a
        actual = 2017 * exp(2 * m) / h
        bound = 64544 * h / a**2
        assert actual <= bound
        rows.append({"lower_prime_log": a, "owner_log_scale": h,
                     "joined_count_price": actual, "quadratic_upper_bound": bound})
    print(json.dumps({"noncomparable_finite_symmetry": counts,
                      "count_exponential_regression": rows,
                      "global_relative_price": [
                          {"log_N_plus_one": x, "price": 129088 / x**2}
                          for x in [5000, 10000, 50000, 100000]],
                      "scope": "Finite symmetry and constants only. Tiny primes do not meet the Lean Chebyshev threshold. No whole-floor margin, effective start or disjoint literal cover is certified."}, indent=2))


if __name__ == "__main__":
    main()

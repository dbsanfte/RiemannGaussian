#!/usr/bin/env python3
"""Reproduce the sparse Seifert determinant checks using only Python stdlib."""
from fractions import Fraction
from random import Random


def determinant(matrix):
    a = [[Fraction(x) for x in row] for row in matrix]
    result = Fraction(1)
    for i in range(len(a)):
        pivot = next((j for j in range(i, len(a)) if a[j][i]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            result = -result
        value = a[i][i]
        result *= value
        for j in range(i + 1, len(a)):
            multiplier = a[j][i] / value
            for k in range(i + 1, len(a)):
                a[j][k] -= multiplier * a[i][k]
    return result


def seifert_matrix(coefficients):
    n = len(coefficients) - 1
    v = [[0] * (2 * n) for _ in range(2 * n)]
    for j in range(n):
        v[j][j] = (-1) ** j * coefficients[j + 1]
        v[n + j][j] = -1
        if j + 1 < n:
            v[j][n + j + 1] = 1
            v[n + j + 1][j] = 1
    v[n][n] = 1
    return v


def main():
    rng = Random(25)
    checks = 0
    for n in range(1, 8):
        for trial in range(10):
            coefficients = [1] + [rng.randrange(-10, 11) for _ in range(n)]
            v = seifert_matrix(coefficients)
            assert sum(value != 0 for row in v for value in row) <= 4 * n - 1
            for i in range(2 * n):
                for j in range(2 * n):
                    expected_skew = int(i < n and j == i + n) - int(
                        j < n and i == j + n
                    )
                    assert v[i][j] - v[j][i] == expected_skew
            for t in (2, 3, -1, -2):
                matrix = [
                    [v[i][j] - t * v[j][i] for j in range(2 * n)]
                    for i in range(2 * n)
                ]
                w = Fraction((1 - t) ** 2, t)
                expected = t**n * sum(
                    coefficients[j] * w**j for j in range(n + 1)
                )
                actual = determinant(matrix)
                assert actual == expected, (n, trial, t, actual, expected)
                checks += 1
    print("Deterministic seed: 25")
    print("Sizes: n=1,...,7; 10 coefficient lists per size")
    print("Evaluation points: 2, 3, -1, -2")
    print("Sparse-entry bound and standard skew-part checks passed.")
    print(f"Exact integer/rational determinant checks passed: {checks}")


if __name__ == "__main__":
    main()

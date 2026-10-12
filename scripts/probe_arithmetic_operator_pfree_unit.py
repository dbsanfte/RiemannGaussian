#!/usr/bin/env python3
"""Exact finite p-free binomial regressions; never zero-source evidence.

Integer extraction retains valuation and native crossings. Fourier codes
are Gaussian integers (the four roots of unity), so the defect identity
is checked exactly rather than with floating complex arithmetic.
"""
from json import dump
from math import comb
from pathlib import Path


def primes_to(limit):
    return [p for p in range(2, limit + 1)
            if all(p % d for d in range(2, int(p**0.5) + 1))]


def extract(p, value):
    assert value > 0
    valuation = 0
    while value % p == 0:
        value //= p
        valuation += 1
    return valuation, value


def character(p, unit):
    assert unit % p
    if p == 2:
        return 1
    result = pow(unit % p, (p - 1) // 2, p)
    assert result in (1, p - 1)
    return 1 if result == 1 else -1


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def mul(x, y):
    return x[0]*y[0] - x[1]*y[1], x[0]*y[1] + x[1]*y[0]


def scale(n, x):
    return n*x[0], n*x[1]


def power(x, n):
    result = (1, 0)
    for _ in range(n):
        result = mul(result, x)
    return result


def main():
    stats = dict(integer_unit_recurrences=0, valuation_balances=0,
                 native_crossings=0, noncrossing_residue_recurrences=0,
                 zero_raw_residue_nonzero_unit=0,
                 exact_gaussian_fourier_defects=0, pair_rows=0)
    primes = primes_to(53)
    for p in primes:
        for D in range(p, 351, p):
            for k in range(D - 1):
                va, a = extract(p, comb(D - 1, k))
                vb, b = extract(p, comb(D - 1, k + 1))
                vx, x = extract(p, k + 1)
                vy, y = extract(p, D - 1 - k)
                assert b*x == a*y
                assert vb + vx == va + vy
                stats['integer_unit_recurrences'] += 1
                stats['valuation_balances'] += 1
                if va:
                    assert a % p
                    stats['zero_raw_residue_nonzero_unit'] += 1
                if (k + 1) % p:
                    assert (b + a) % p == 0
                    assert va == vb
                    stats['noncrossing_residue_recurrences'] += 1
                else:
                    stats['native_crossings'] += 1
    codes = ((1, 0), (-1, 0), (0, 1), (0, -1))
    for p in primes:
        for q in primes:
            if p*q > 900:
                continue
            for rp, rq in ((1, 1), (2, 1), (1, 2)):
                D = p**rp*q**rq
                if D > 900:
                    continue
                row = []
                for k in range(D):
                    _, a = extract(p, comb(D - 1, k))
                    _, b = extract(q, comb(D - 1, k))
                    row.append(character(p, a)*character(q, b))
                sigma = character(p, p - 1)*character(q, q - 1)
                assert row[0] == row[-1] == 1
                for k in range(D - 1):
                    if (k + 1) % p and (k + 1) % q:
                        assert row[k + 1] == sigma*row[k]
                for code in codes:
                    total = (0, 0)
                    jumps = (0, 0)
                    for k, atom in enumerate(row):
                        total = add(total, scale(atom, power(code, k)))
                        if k < D - 1 and ((k + 1) % p == 0 or (k + 1) % q == 0):
                            jumps = add(jumps, scale(row[k + 1] - sigma*atom,
                                                     power(code, k + 1)))
                    left = mul(add((1, 0), scale(-sigma, code)), total)
                    right = add(add((1, 0), scale(-sigma, power(code, D))), jumps)
                    assert left == right
                    stats['exact_gaussian_fourier_defects'] += 1
                stats['pair_rows'] += 1
    out = Path('.lake/arithmetic-operator-pfree-unit')
    out.mkdir(parents=True, exist_ok=True)
    report = {'evidenceKind': 'exact finite integer/Gaussian-integer diagnostic',
              'proofInput': False, 'actualZeroSourceInferred': False,
              'valuationOrdersAndCrossingsRetained': True,
              'counts': stats}
    with (out/'probe.json').open('w') as stream:
        dump(report, stream, indent=2)
    print(report)


if __name__ == '__main__':
    main()

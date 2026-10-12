#!/usr/bin/env python3
"""Native binomial/GCD checks and a separately labelled Mellin diagnostic."""
import argparse
import cmath
import json
import math
from pathlib import Path


def primes_to(n):
    flags = bytearray(b'\x01') * (n + 1)
    flags[:2] = b'\x00\x00'
    for p in range(2, math.isqrt(n) + 1):
        if flags[p]:
            flags[p * p:n + 1:p] = b'\x00' * ((n - p * p) // p + 1)
    return [p for p in range(2, n + 1) if flags[p]]


def valuation(n, p):
    result = 0
    while n % p == 0:
        n //= p
        result += 1
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    limit = 512
    primes = primes_to(limit)
    cells = 0
    large_checks = 0
    carry_checks = 0
    proper_checks = 0
    for n in range(2, limit + 1):
        values = [math.comb(n, k) for k in range(n + 1)]
        g = 0
        gcds = {}
        for a in range(n // 2 - 1, -1, -1):
            g = math.gcd(g, values[a + 1])
            gcds[a] = g
        carry_minima = {}
        for d in range(1, min(n + 2, 42)):
            current = n
            for a in range(n // 2 - 1, -1, -1):
                k = a + 1
                current = min(current, n // d - k // d - (n - k) // d)
                carry_minima[a, d] = current
        valuation_minima = {}
        for p in primes:
            if p > n:
                break
            current = n
            for a in range(n // 2 - 1, -1, -1):
                current = min(current, valuation(values[a + 1], p))
                valuation_minima[a, p] = current
        for a in range((n - 1) // 3 + 1):
            S = list(range(a + 1, n - a))
            assert S and all(0 < k < n for k in S)
            g = gcds[a]
            cells += 1
            for d in range(1, min(n + 2, 42)):
                minimum = carry_minima[a, d]
                assert minimum == int(d <= n <= d + a)
                carry_checks += 1
            for p in primes:
                if p > n:
                    break
                v = valuation(g, p)
                assert v == valuation_minima[a, p]
                proper_checks += 1
                if n < p * p:
                    assert v == int(p <= n <= p + a)
                    large_checks += 1
                else:
                    orders = 0
                    power = p
                    while power <= n:
                        orders += 1
                        power *= p
                    assert v <= orders
    log_width = math.log(1.5)
    diagnostic = []
    for beta in [0.5001, 0.625, 0.875, 0.99995]:
        for y in [54, -54, 65, 100]:
            rho = complex(beta, y)
            factor = (1 - cmath.exp(-beta * log_width)) / beta
            assert factor.real > 0 and factor.imag == 0
            diagnostic.append({'beta': beta, 'height': y,
                               'matchedRealMultiplier': factor.real,
                               'multiplicityOneResidue': -factor.real})
    report = {
        'checksPassed': True,
        'proofInput': False,
        'scope': 'all symmetric corridors 3*a<n in the finite sample; full integer GCD and all actual valuations',
        'exactNativeCorridorCells': cells,
        'exactArbitraryDenominatorFirstCarryChecks': carry_checks,
        'exactLargePrimeValuationChecks': large_checks,
        'exactWholeGcdValuationChecks': proper_checks,
        'controlsGrantedActualBinomialGammaData': False,
        'floatingDiagnosticOnly': {'matchedWindowResidues': diagnostic},
        'nativeCofinalZeroSourceInferred': False,
        'newRHClaimed': False,
    }
    Path(args.output).write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'floatingDiagnosticOnly'}))


if __name__ == '__main__':
    main()

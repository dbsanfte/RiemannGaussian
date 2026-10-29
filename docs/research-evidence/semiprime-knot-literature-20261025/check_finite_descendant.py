#!/usr/bin/env python3
"""Reproduce validation.txt using exact composite-ring arithmetic (Python 3)."""
from math import gcd
from pathlib import Path

count = zero = 0
for modulus in (15, 21, 35, 77):
    for q in range(1, modulus):
        if gcd(q, modulus) != 1:
            continue
        qi = pow(q, -1, modulus)
        for t in range(modulus):
            C = [1]
            for j in range(1, 9):
                C.append(C[-1] * (t - pow(q, j, modulus) - pow(qi, j, modulus)) % modulus)
            if 0 in C:
                zero += 1
            for L in range(8):
                def D(m):
                    return sum(C[j] * pow(q, m*j, modulus) for j in range(L+1)) % modulus
                for m in range(-3, 4):
                    lhs = (pow(q, m+1, modulus)*D(m+1)
                           + (1-t*pow(q, m, modulus))*D(m)
                           + pow(q, m-1, modulus)*D(m-1)) % modulus
                    rhs = (1-pow(q, m*(L+1), modulus)*C[L+1]) % modulus
                    assert lhs == rhs, (modulus, q, t, L, m, lhs, rhs)
                    count += 1
result = (f'PASS exact finite descendant boundary identity; cases={count}; '
          f'zero-factor configurations={zero}\n')
Path(__file__).with_name('validation.txt').write_text(result)
print(result, end='')

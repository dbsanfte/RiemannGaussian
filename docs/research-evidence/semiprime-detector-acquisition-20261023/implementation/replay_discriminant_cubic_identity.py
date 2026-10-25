#!/usr/bin/env python3
"""One exact polynomial/carry replay; no search or coverage experiment."""


def add(*terms):
    return [sum(p[i] if i < len(p) else 0 for p in terms)
            for i in range(max(map(len, terms)))]


def mul(p, q):
    result = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            result[i + j] += x * y
    return result


# By homogeneity, set X=U/a and remove a^6. All coefficient tests exact.
lift = [-16, -8, 2, -1]
norm = [20, -4, 1]
residual = add(mul(lift, lift), [0, 0, 0, 0] + [-x for x in norm],
               [-256, -256])
assert all(x == 0 for x in residual)
print("homogeneous lift identity coefficients:", residual)

# Same fixed row as check_integer_character_filter.py; no search.
r, a, C, N, B = 43, 1, 331, 3551779909, 1082824
M = r**4
U = C*N-a
L = -16*a**3-8*a*a*U+2*a*U*U-U**3
assert U % r == 0 and (L-8*a*a*B) % M == 0
t = (L-8*a*a*B)//M
assert (B*B-4*a*C*N) % M == 0
D0 = (B*B-4*a*C*N)//M
F = (C*N-3*a)**2+16*a*a
residual = 64*a**4*D0+16*a*a*B*t+M*t*t-(U//r)**4*F
assert residual == 0
root = L*pow(U*U, -1, N) % N
assert root == (-5*a) % N
print("fixed-row centered-carry residual:", residual)
print("fixed-row induced root modulo N:", root, "expected:", (-5*a) % N)

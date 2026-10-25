#!/usr/bin/env python3
"""One inherited true witness refutes automatic principal-square-form transfer."""
from math import gcd, isqrt

r, P, Q = 43, 59447, 59747
N, H, M = P*Q, r*r, r**4
a, C, s, c, B = 1, 331, 345, 41, 1082824
b, d, sigma = 586, 343984, 48
h = (c*P-s)//H
assert H*h+s == c*P
assert a*h*h+b*h+d == P*sigma and 0 < sigma < 4*r
assert B == H*b-2*a*s and C*N == M*d-H*b*s+a*s*s
assert 0 < a < r and 0 < C <= H//2 and abs(B) <= M//2
assert C*N % r == a and s % r == 1
assert 16*H < P < Q and N <= r**6


def prime(n):
    return n >= 2 and all(n % j for j in range(2, isqrt(n)+1))


dp, dq = (P-1)//2, (Q-1)//2
assert all(prime(n) for n in (P, Q, dp, dq))
assert min(dp, dq) > 16*H and gcd(dp, dq) == 1
assert dp*dq > 256*M and pow(4, dp, P) == pow(4, dq, Q) == 1
assert 4 % P != 1 and 4 % Q != 1
D = b*b-4*a*d
Delta = 16*a*C*N
assert B*B-M*D == 4*a*C*N and gcd(H, 2*B) == 1
assert gcd(D, N) == 1 and isqrt(Delta)**2 < Delta
sqrt_floor = isqrt(Delta)


def rho(form):
    """Gower-Wagstaff standard reduction, exact integer comparisons only."""
    A, middle, end = form
    width = 2*abs(end)
    if end*end > Delta:
        new_middle = (-middle) % width
        if new_middle > abs(end):
            new_middle -= width
    else:
        new_middle = sqrt_floor-(sqrt_floor+middle) % width
    assert (new_middle+middle) % (2*end) == 0
    assert (new_middle*new_middle-Delta) % (4*end) == 0
    return end, new_middle, (new_middle*new_middle-Delta)//(4*end)


def reduced(form):
    A, middle, _ = form
    # |sqrt(Delta)-2|A|| < middle < sqrt(Delta).
    lower = 2*abs(A)-middle
    return (middle > 0 and middle*middle < Delta
            and (middle+2*abs(A))**2 > Delta
            and (lower <= 0 or lower*lower < Delta))


def cycle(form):
    while not reduced(form):
        form = rho(form)
    start = form
    length = principal = ambiguous = 0
    while True:
        A, middle, end = form
        assert reduced(form) and middle*middle-4*A*end == Delta
        assert gcd(gcd(abs(A), abs(middle)), abs(end)) == 1
        principal += A == 1
        ambiguous += middle % A == 0 or A == end
        form = rho(form)
        length += 1
        if form == start:
            break
        assert length <= 20000000, "fixed-instance guard exceeded"
    return dict(reduced=start, length=length,
                principal_forms=principal, ambiguous_forms=ambiguous)


G_cycle = cycle((H, 2*B, D*H))
F_cycle = cycle((D, 2*B, H*H))
assert G_cycle == dict(reduced=(1849, 4336374, -823003), length=152120,
                      principal_forms=0, ambiguous_forms=0)
assert F_cycle == dict(reduced=(-1032540, 4230728, 220613), length=151318,
                      principal_forms=0, ambiguous_forms=0)
print(dict(r=r, N=N, h=h, sigma=sigma, D=D, Delta=Delta,
           G_cycle=G_cycle, F_cycle=F_cycle))

#!/usr/bin/env python3
"""One exact algebraic replay; no performance or coverage experiment."""
import json
from fractions import Fraction
from math import gcd, isqrt


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def centered(x, modulus):
    x %= modulus
    return x - modulus if 2*x > modulus else x


r, P, Q = 43, 59447, 59747
H, M, N = r*r, r**4, P*Q
P0 = 32*H
A, T = isqrt(N)//P0, H//2
assert prime(r) and prime(P) and prime(Q)
assert N == 3551779909 and N <= r**6
assert 16*H < P < Q and P0 <= P < Q < 2*P0
assert P > P0-1 and P >= 2*(16*H) and A == 1 and T == 924
beta = 4
dp, dq = (P-1)//2, (Q-1)//2
assert prime(dp) and prime(dq) and dp % 2 == dq % 2 == 1
assert dp == 29723 and dq == 29873 and min(dp,dq) > 16*H
assert gcd(dp,dq) == gcd(r,dp*dq) == gcd(beta,N) == 1
assert beta % P != 1 and beta % Q != 1
assert pow(beta,dp,P) == pow(beta,dq,Q) == 1
# Each order divides a certified prime and is nontrivial, hence is exact.
D = dp*dq
assert D > 256*M and pow(beta,D,N) == 1
assert pow(beta,D//dp,N) != 1 and pow(beta,D//dq,N) != 1
assert pow(beta,H,P) != 1 and pow(beta,H,Q) != 1
assert pow(beta,M,P) != 1 and pow(beta,M,Q) != 1
expected = [(41, 345, 331, 1082824, 48, 41),
            (28, 1420, 116, -453996, 12, 7)]
rows = []
for (factor, other), expect in zip([(P,Q),(Q,P)], expected):
    c = pow(factor, -1, r)
    s = (c*factor) % H
    a = 1
    C = centered(a*s*s*pow(N,-1,H), H)
    B = centered(-a*s-C*N*pow(s,-1,M), M)
    h, rem = divmod(c*factor-s, H)
    assert rem == 0 and h >= 0 and s % r == 1
    root_residual = (a*s*s+B*s+C*N) % M
    derivative_residual = (2*a*s+B) % H
    assert root_residual == derivative_residual == 0
    numerator = a*c*c*factor+B*c+C*other
    sigma, source_residual = divmod(numerator, M)
    assert source_residual == 0
    assert abs(C) <= T and C != 0 and abs(sigma)*2 < 7*r
    denominator = Fraction(sigma,c).denominator
    assert gcd(c,sigma) == gcd(c,C)
    assert denominator == c//gcd(c,C) and denominator > 1
    assert (c,s,C,B,sigma,denominator) == expect
    rows.append(dict(factor=factor,c=c,s=s,C=C,B=B,h=h,sigma=sigma,
                     ratio=str(Fraction(sigma,c)),denominator=denominator,
                     root_residual=root_residual,
                     derivative_residual=derivative_residual,
                     source_residual=source_residual))
print(json.dumps(dict(status='PASS',r=r,H=H,M=M,P0=P0,P=P,Q=Q,N=N,
                      A=A,T=T,primality='complete trial division',
                      preparation=dict(base=beta,local_orders=[dp,dq],
                                       global_order=D,local_lower_bound=16*H,
                                       global_lower_bound=256*M,
                                       coprime_local_orders=True,
                                       odd_local_orders=True,
                                       H_and_M_preserve_local_orders=True),rows=rows),
                 indent=2))

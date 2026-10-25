#!/usr/bin/env python3
"""One exact counterexample to the specified quadratic cover; no search."""
from math import gcd, isqrt


def prime_by_trial(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def main():
    r, s = 450071, 454931
    P, Q = 900143, 909863
    N, m, beta = 819006810409, 97, 4
    assert P == 2*r + 1 and Q == 2*s + 1 and N == P*Q
    assert all(prime_by_trial(z) for z in (r, s, P, Q, m))
    assert max(isqrt(z) for z in (r, s, P, Q, m)) < 1000
    assert (m-1)**6 < N <= m**6
    # Thus m is already prime and is the first prime >= ceil(N^(1/6)).
    H = m*m
    assert gcd(beta, N) == 1
    assert pow(beta, r, P) == pow(beta, s, Q) == 1
    assert beta % P != 1 and beta % Q != 1
    # r,s prime: these are exact orders, not merely annihilators.
    assert gcd(r, s) == 1 and r % 2 == s % 2 == 1
    assert min(r, s) > 16*H
    assert r*s > 256*H*H
    assert gcd(H, r*s) == 1  # q=beta^H has the same exact local orders.
    assert gcd(N-1, r*s) == 1  # compatible with N-1 projection too.

    M = 1
    for ell in range(2, m+1):
        if not prime_by_trial(ell):
            continue
        pp = ell
        while pp*ell <= N:
            pp *= ell
        M *= pp
    assert gcd(M, r*s) == 1
    projected = pow(beta, M, N)
    assert gcd(projected-1, N) == 1
    assert pow(projected, r, P) == pow(projected, s, Q) == 1
    assert projected % P != 1 and projected % Q != 1

    lo, hi = m, m*m+m-1
    residues = (N % r, N % s)
    assert residues == (9721, 445212)
    assert 0 < lo <= hi < min(r, s)
    assert all(hi < z < order for z, order in zip(residues, (r, s)))
    assert N > 2*m*m
    # For every b=1..m and a=0..m-1:
    # u=mb-a lies in [1,m^2], v=mb+a lies in [lo,hi].
    # The orders r,s are prime and exceed m^2, so neither divides u.
    # Neither divides N-v, because its residue is outside [lo,hi].
    # Hence neither divides Delta=u*(N-v): EVERY cross-difference is a unit.
    print({"N": N, "P": P, "Q": Q, "m": m,
           "exact_local_orders": [r, s], "beta": beta,
           "M_bits": M.bit_length(), "projected_base": projected,
           "local_order_margin": 16*H,
           "global_order": r*s, "global_margin": 256*H*H,
           "v_interval": [lo, hi], "N_residues": list(residues),
           "verdict": "all quadratic cross-differences are units"})


if __name__ == "__main__":
    main()

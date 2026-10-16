"""Exact small diagnostic; no theorem or asymptotic complexity claim."""
import json


def order(p, a, b):
    assert (4 * a**3 + 27 * b**2) % p
    squares = {i * i % p for i in range(p)}
    total = 1
    for x in range(p):
        rhs = (x**3 + a * x + b) % p
        total += 1 if rhs == 0 else 2 if rhs in squares else 0
    return total


p, ell, a, b, d = 421, 5, 1, 3, 2
assert all(p % q for q in range(2, 21))
assert p > 16 * ell**2
assert pow(d, (p - 1) // 2, p) == p - 1
n = order(p, a, b)
nt = order(p, a * d * d % p, b * d**3 % p)
trace = p + 1 - n
assert (n, nt, trace) == (412, 432, 10)
assert n + nt == 2 * (p + 1)
assert n % ell and nt % ell
assert trace % ell == 0 and p % ell == 1
assert [u for u in range(ell) if (u * u - trace * u + p) % ell == 0] == [2, 3]
print(json.dumps({
    "p": p, "ell": ell, "curve": [a, b], "order": n,
    "nonsquare_twist": d, "twist_curve": [a*d*d % p, b*d**3 % p],
    "twist_order": nt, "trace": trace,
    "frobenius_eigenvalues_mod_ell": [2, 3],
    "interpretation": "Two F_p-rational cyclic 5-isogeny kernels, no rational 5-torsion on either twist."
}, indent=2))

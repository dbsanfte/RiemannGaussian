#!/usr/bin/env python3
"""Exact reference checks for the native half-center reduction, not a fast oracle."""
from math import gcd, prod


def mul(values, modulus):
    return prod(values) % modulus


def polynomial_at(roots, value, modulus):
    return mul((value - root for root in roots), modulus)


def delta_row(x, t, modulus):
    return (x - t) * (x - pow(t, -1, modulus)) * pow((x - 1) ** 2, -1, modulus) % modulus


def crt(a, b, p, r):
    # Test fixture creation only; the proposed algorithm does not know p,r.
    return (a + p * ((b - a) * pow(p, -1, r) % r)) % (p * r)


def main():
    p, r = 23, 47
    modulus, eta, horizon = p * r, 2, 3
    q = eta * eta
    mixed = crt(pow(q, 2, p), pow(q, 3, r), p, r)
    separate1 = crt(pow(q, 2, p), pow(q, 5, r), p, r)
    separate2 = crt(pow(q, 5, p), pow(q, 3, r), p, r)
    cases = [
        [pow(q, 2, modulus)],
        [mixed],
        [separate1, separate2],
        [pow(q, 5, modulus)],
        [pow(q, 2, modulus), pow(q, 2, modulus)],
    ]
    identities = recoveries = 0
    for representatives in cases:
        rows = [z for x in representatives for z in (x, q * pow(x, -1, modulus) % modulus)]
        assert all(gcd(x * (x - 1) * (x - q) * (x - eta), modulus) == 1 for x in representatives)
        weights = [(x + q * pow(x, -1, modulus)) % modulus for x in representatives]
        norm_h = pow(polynomial_at(weights, 1 + q, modulus), -1, modulus)

        def d(t):
            return polynomial_at(weights, (t + q * pow(t, -1, modulus)) % modulus, modulus) * norm_h % modulus

        centered = [x * pow(eta, -1, modulus) % modulus for x in representatives]
        traces = [(v + pow(v, -1, modulus)) % modulus for v in centered]
        norm_r = pow(polynomial_at(traces, 2, modulus), -1, modulus)

        def knot(t):
            return polynomial_at(traces, (t + pow(t, -1, modulus)) % modulus, modulus) * norm_r % modulus

        c = knot(eta)
        assert gcd(c, modulus) == 1 and d(1) == d(q) == 1
        b_previous = 1
        zero_bits = []
        for m in range(horizon + 1):
            original = mul((delta_row(x, pow(q, i, modulus), modulus)
                            for x in rows for i in range(1, m + 1)), modulus)
            b = mul((d(pow(q, i, modulus)) for i in range(2, m + 2)), modulus)
            if m:
                assert original == b * b_previous % modulus
                identities += 1
            negative = mul((polynomial_at(rows, pow(q, -i, modulus), modulus)
                            for i in range(1, m + 1)), modulus)
            normalization = (pow(q, len(representatives) * m * (m + 1) // 2, modulus)
                             * pow(polynomial_at(rows, 1, modulus), -m, modulus)) % modulus
            assert b == normalization * negative % modulus
            odd = mul((knot(pow(eta, 2 * i + 1, modulus)) for i in range(1, m + 1)), modulus)
            assert odd == pow(c, m, modulus) * b % modulus
            assert (original == 0) == (b == 0) == (negative == 0) == (odd == 0)
            assert (gcd(original, modulus) > 1) == (gcd(b, modulus) > 1)
            identities += 4
            zero_bits.append(negative == 0)
            b_previous = b
        assert zero_bits == sorted(zero_bits)
        if zero_bits[-1]:
            lo, hi = 0, horizon
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if zero_bits[mid]:
                    hi = mid
                else:
                    lo = mid
            # Only the negative original seed is scanned.
            target = pow(q, -hi, modulus)
            assert any(gcd(x - target, modulus) > 1 for x in rows)
            recoveries += 1

    # Public half-center rows are harmless under the needed local order bound.
    assert all(gcd(eta - pow(q, i, modulus), modulus) == 1
               for i in range(-horizon, horizon + 1))
    print(f"PASS: {len(cases)} exact half-center fixtures; {identities} identity/predicate checks")
    print(f"PASS: {recoveries} negative-only recovery cases, including mixed CRT and repeated roots")
    print("PASS: harmless public half-center row check")
    print("Reference arithmetic only; no fast prefix oracle or native coverage claim.")


if __name__ == '__main__':
    main()

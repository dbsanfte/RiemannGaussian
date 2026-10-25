#!/usr/bin/env python3
"""Construct a proved universal *small-multiple* residue cover.

For an odd prime r, acquire a catalog S modulo r^2 of soft O(r) size
such that every unit x has c*x in S for some 1 <= c < r. This does NOT
acquire a factor residue or the semiprime collision query. Its witness
table is indexed by q_r(x), which is unknown when x is an unknown factor.

The greedy cover uses exact cyclic convolution via packed GMP integer
multiplication. No floating point, empirical density premise, or factors
of the semiprime enter this constructor. --self-test checks algebra and
packing, not a semiprime coverage experiment or an asymptotic benchmark.
"""
from __future__ import annotations

import argparse
import json
import math

import gmpy2


def primes_up_to(limit):
    """Deterministic sieve; its O(limit) output allocation is charged."""
    flags = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        flags[0] = 0
    if limit >= 1:
        flags[1] = 0
    for prime in range(2, math.isqrt(limit) + 1):
        if flags[prime]:
            count = (limit - prime * prime) // prime + 1
            flags[prime * prime:limit + 1:prime] = b"\x00" * count
    return [i for i, flag in enumerate(flags) if flag]


def fermat_quotient(value, prime):
    """Only call with prime prime and a unit value modulo prime."""
    if value % prime == 0:
        raise ValueError("Fermat quotient requires a unit")
    remainder = pow(int(value), prime - 1, prime * prime)
    if remainder % prime != 1:
        raise ValueError("prime parameter or Fermat remainder is invalid")
    return (remainder - 1) // prime


def cyclic_binary_convolution(left, right):
    """Exact convolution modulo X^r-1 for two binary coefficient arrays.

    Radix 256^width exceeds r, so no coefficient carries occur. Byte
    packing/unpacking avoids quadratic repeated shifts of growing words.
    The one packed integer multiplication has O(r log r) input bits.
    """
    size = len(left)
    if not size or len(right) != size:
        raise ValueError("equal nonempty arrays required")
    if any(v not in (0, 1) for v in left + right):
        raise ValueError("binary coefficients required")
    width = (size.bit_length() + 7) // 8
    first = gmpy2.mpz.from_bytes(
        b"".join(int(v).to_bytes(width, "little") for v in left), "little")
    second = gmpy2.mpz.from_bytes(
        b"".join(int(v).to_bytes(width, "little") for v in right), "little")
    packed = (first * second).to_bytes((2 * size - 1) * width, "little")
    ordinary = [int.from_bytes(packed[i * width:(i + 1) * width], "little")
                for i in range(2 * size - 1)]
    return [ordinary[i] + (ordinary[i + size] if i < size - 1 else 0)
            for i in range(size)]


def build_cover(prime):
    """Public constructor. The primality check costs soft O(r), not free."""
    r = int(prime)
    if r < 3 or r % 2 == 0:
        raise ValueError("an odd prime is required")
    primes = primes_up_to(r)
    if primes[-1] != r:
        raise ValueError("an odd prime is required")
    quotient_witness = [0] * r
    for multiplier in range(1, r):
        q = fermat_quotient(multiplier, r)
        if quotient_witness[q] == 0:
            quotient_witness[q] = multiplier
    image = [q for q, c in enumerate(quotient_witness) if c]
    indicator = [int(c != 0) for c in quotient_witness]
    d = len(image)
    pi = len(primes) - 1
    # Finite form of Ostafe--Shparlinski's image-size proof, not a test
    # replacing that theorem. The actual measured d controls the loop.
    if d * (pi + r - 2) < pi * pi:
        raise ArithmeticError("finite image theorem check failed")
    round_bound = ((r + d - 1) // d) * (r.bit_length() + 1)
    uncovered = [1] * r
    remaining = r
    shifts, witnesses, rounds = [], [None] * r, []
    while remaining:
        scores = cyclic_binary_convolution(uncovered, indicator)
        tau = max(range(r), key=lambda i: scores[i])
        if r * scores[tau] < remaining * d:
            raise ArithmeticError("averaging inequality failed")
        shift_index = len(shifts)
        shifts.append(tau)
        removed = 0
        for q in image:
            t = (tau - q) % r
            if uncovered[t]:
                uncovered[t] = 0
                witnesses[t] = [shift_index, quotient_witness[q]]
                removed += 1
        if removed != scores[tau] or removed == 0:
            raise ArithmeticError("cyclic convolution orientation failed")
        remaining -= removed
        rounds.append({"shift": tau, "removed": removed,
                       "remaining": remaining})
        if len(shifts) > round_bound:
            raise ArithmeticError("greedy cover bound failed")
    modulus = r * r
    teich = [pow(j, r, modulus) for j in range(1, r)]
    catalog = [v * (1 - r * tau) % modulus
               for tau in shifts for v in teich]
    return {"prime": r, "modulus": modulus, "image": image,
            "image_size": d, "prime_count_below": pi,
            "round_bound": round_bound, "shifts": shifts,
            "witnesses": witnesses, "catalog": catalog, "rounds": rounds}


def locate_multiple(cover, value):
    """Use only when value itself is known; NOT a hidden-factor oracle."""
    r, modulus = cover["prime"], cover["modulus"]
    t = fermat_quotient(value, r)
    shift_index, multiplier = cover["witnesses"][t]
    residue = multiplier * value % modulus
    tag = residue % r
    index = shift_index * (r - 1) + tag - 1
    if cover["catalog"][index] != residue:
        raise ArithmeticError("Teichmuller catalog lookup failed")
    return {"multiplier": multiplier, "residue": residue,
            "catalog_index": index}


def self_test():
    packing_cases = 0
    # Include the byte boundary: coefficient 256 must not carry.
    for size in [1, 2, 3, 7, 31, 255, 256, 257]:
        for left, right in [([1] * size, [1] * size),
                            ([int(i % 3 == 0) for i in range(size)],
                             [int(i % 5 != 0) for i in range(size)])]:
            direct = [sum(left[j] * right[(i - j) % size]
                          for j in range(size)) for i in range(size)]
            assert cyclic_binary_convolution(left, right) == direct
            packing_cases += 1
    unit_cases = row_cases = selected_pair_cases = 0
    tested_primes = [r for r in primes_up_to(101) if r > 2]
    for r in tested_primes:
        cover = build_cover(r)
        h = r * r
        assert len(set(cover["catalog"])) == len(cover["catalog"])
        # The selected (residue,multiplier) graph represents each unit
        # exactly once, even though the row catalog itself is smaller.
        represented = []
        for t, (index, c) in enumerate(cover["witnesses"]):
            tau = cover["shifts"][index]
            assert (tau - fermat_quotient(c, r)) % r == t
            for j in range(1, r):
                s = cover["catalog"][index * (r - 1) + j - 1]
                represented.append(s * pow(c, -1, h) % h)
        units = [x for x in range(h) if x % r]
        assert sorted(represented) == units
        selected_pair_cases += len(represented)
        for x in units:
            located = locate_multiple(cover, x)
            assert 1 <= located["multiplier"] < r
            assert located["residue"] == x * located["multiplier"] % h
            unit_cases += 1
        # Literal linear-row identities for arbitrary unit integers P,Q.
        # These are algebra checks; neither P,Q primality nor coverage of
        # test semiprimes is used as a claim about the factoring goal.
        for offset in range(1, 8):
            p = r**3 + offset
            q = r**3 + 2 * offset + 1
            if p % r == 0 or q % r == 0:
                continue
            n = p * q
            located = locate_multiple(cover, p)
            c, s = located["multiplier"], located["residue"]
            b = (-n * pow(s, -1, h)) % h
            if 2 * b > h:
                b -= h
            d = (n + s * b) // h
            assert h * d - s * b == n
            row_h = (c * p - s) // h
            quotient, rem = divmod(b * row_h + d, p)
            assert rem == 0 and h * quotient == b * c + q
            assert n + b * c - h * quotient == (p - 1) * q
            row_cases += 1
    for bad in [0, 2, 9, 15]:
        try:
            build_cover(bad)
        except ValueError:
            pass
        else:
            raise AssertionError("composite or out-of-scope modulus accepted")
    return {"status": "pass", "packing_cases": packing_cases,
            "auxiliary_primes": len(tested_primes),
            "unit_identity_cases": unit_cases,
            "selected_pair_cases": selected_pair_cases,
            "linear_row_identity_cases": row_cases,
            "scope": "algebra and constructor checks; no factoring-rate claim"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        print(json.dumps(self_test(), indent=2))
    elif args.prime is not None:
        cover = build_cover(args.prime)
        print(json.dumps({k: v for k, v in cover.items()
                          if k not in ("image", "witnesses", "catalog")}, indent=2))
    else:
        parser.error("supply --prime or --self-test")


if __name__ == "__main__":
    main()

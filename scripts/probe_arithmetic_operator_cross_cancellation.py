#!/usr/bin/env python3
"""Exact shared-row cancellation diagnostics; no asymptotic proof input.

Keep both Lucas upper residues, the quotient crossings and final endpoint.
Prime-power row lengths are tested as well as ordinary prime pairs. Floating
height phases below are diagnostics only, not hypothetical-zero samples.
"""

from collections import Counter
from fractions import Fraction as F
from math import comb, isqrt, log
from pathlib import Path
import cmath
import json


def primes(limit):
    return [n for n in range(3, limit + 1, 2)
            if all(n % d for d in range(2, isqrt(n) + 1))]


def quadratic(p, x):
    v = pow(x % p, (p - 1) // 2, p)
    return -1 if v == p - 1 else v


def choose_mod(n, k, p):
    """Exact Lucas product, including every upper digit."""
    value = 1
    while n or k:
        nd, kd = n % p, k % p
        if kd > nd:
            return 0
        value = value * comb(nd, kd) % p
        n, k = n // p, k // p
    return value


def row_data(p, q, D):
    assert D > 0 and D % 2 == 1 and D % p == D % q == 0
    ep, eq = quadratic(p, -1), quadratic(q, -1)
    upper_p = [quadratic(p, choose_mod(D // p - 1, h, p))
               for h in range(D // p)]
    upper_q = [quadratic(q, choose_mod(D // q - 1, h, q))
               for h in range(D // q)]

    def atom(k):
        return ep ** (k % p) * eq ** (k % q) * upper_p[k // p] * upper_q[k // q]

    # On a quotient-stable segment only the literal (-1)^k parity varies.
    # This is an exact integer sweep, not period completion.
    total, k = 0, 0
    while k < D:
        hp, hq = k // p, k // q
        end = min(p * (hp + 1), q * (hq + 1))
        length = end - k
        segment_mass = length if ep * eq == 1 else ((-1) ** k if length % 2 else 0)
        total += ep ** hp * eq ** hq * upper_p[hp] * upper_q[hq] * segment_mass
        k = end
    return F(total, D), atom


def direct_row(p, q, D):
    coefficient, total = 1, 0
    for k in range(D):
        total += quadratic(p, coefficient) * quadratic(q, coefficient)
        if k + 1 < D:
            coefficient = coefficient * (D - 1 - k) // (k + 1)
    return F(total, D)


def crossings(p, q, D):
    return sorted({(multiple * r - 1) // 2
                   for r in (p, q) for multiple in range(1, D // r + 1)
                   if multiple * r % 2 == 1 and multiple * r < D})


def cancellation_check(p, q, D, trace, atom):
    assert p % 4 != q % 4
    jumps = crossings(p, q, D)
    assert len(jumps) <= D // p + D // q
    joined = 1 + sum(atom(2 * i) + atom(2 * i + 1) for i in jumps)
    assert trace == F(joined, D)
    assert abs(trace) <= F(1, D) + F(2, p) + F(2, q)
    if D <= 1024:
        for i in range(D // 2):
            if i not in jumps:
                assert atom(2 * i) + atom(2 * i + 1) == 0


def main():
    ps = primes(251)
    traces, counts, signs = {}, Counter(), Counter()
    for ip, p in enumerate(ps):
        for q in ps[:ip]:
            D = p * q
            trace, atom = row_data(p, q, D)
            traces[p, q] = trace
            counts["ordinaryPairs"] += 1
            if p % 4 != q % 4:
                cancellation_check(p, q, D, trace, atom)
                counts["oppositeParityChecks"] += 1
            else:
                signs["negative" if trace < 0 else "positive" if trace > 0 else "zero"] += 1
            if p <= 31:
                assert trace == direct_row(p, q, D)
                counts["directIntegerRows"] += 1
    assert traces[19, 7] == F(-13, 133)

    # Do not silently drop proper prime-power common row lengths.
    for p in primes(19):
        for q in primes(19):
            if p % 4 != 3 or q % 4 != 1:
                continue
            for r in range(1, 4):
                for s in range(1, 4):
                    D = p ** r * q ** s
                    if D > 100000:
                        continue
                    trace, atom = row_data(p, q, D)
                    cancellation_check(p, q, D, trace, atom)
                    counts["properPowerRows"] += int(r > 1 or s > 1)
                    if D <= 1024:
                        assert trace == direct_row(p, q, D)
                        counts["properPowerDirectRows"] += int(r > 1 or s > 1)

    # A bounded INTERNAL mask can undo the cancellation. Its exclusion
    # from the Lean terminal theorem is material, not cosmetic.
    masked_p, masked_q = 59, 41
    trace, atom = row_data(masked_p, masked_q, masked_p * masked_q)
    masked = F(sum(atom(k) ** 2 for k in range(masked_p * masked_q)), masked_p * masked_q)
    bound = F(1, masked_p * masked_q) + F(2, masked_p) + F(2, masked_q)
    assert masked > bound

    # Complete small dyadic bands. These are fixed finite heights, not
    # zeros, and do not settle the still-open same-parity source gate.
    samples = []
    for J in range(2, 8):
        band = [p for p in ps if 2 ** J <= p < 2 ** (J + 1)]
        for y in (54, 65, 100):
            sums = {"opposite": 0j, "same": 0j}
            for ip, p in enumerate(band):
                for q in band[:ip]:
                    key = "opposite" if p % 4 != q % 4 else "same"
                    sums[key] += log(p) * log(q) * cmath.exp(-1j * y * log(p * q)) * float(traces[p, q])
            samples.append({"J": J, "height": y, "ordinaryPrimes": len(band),
                            "oppositeNorm": abs(sums["opposite"]),
                            "sameParityNorm": abs(sums["same"]),
                            "oppositeCertifiedEnvelope": 20 * (J + 1) ** 2 * 2 ** J})

    report = {
        "checksPassed": True, "proofInput": False,
        "arithmetic": "integer Lucas upper digits, native quotient sweeps, exact rational traces",
        "maxPrime": 251, "ordinaryPrimeCount": len(ps), "checks": dict(counts),
        "sameParityTraceSigns": dict(signs),
        "negativeSameParityExample": {"p": 19, "q": 7, "trace": "-13/133"},
        "internalMaskCounterexample": {"p": masked_p, "q": masked_q,
            "unmasked": str(trace), "boundedInternalMaskTrace": str(masked),
            "outsideMaskEnvelope": str(bound)},
        "floatingHeightSamplesAreNotZeroSourceProofs": True,
        "finiteHeightSamples": samples,
        "finiteMatrixPSDOrAsymptoticClaim": False,
        "sameParitySourceGateOpen": True,
        "leanScope": "complete opposite-parity rows, all common prime-power lengths; balanced terminal packet over ordinary prime pairs and bounded OUTSIDE masks only",
    }
    target = Path(".lake/arithmetic-operator-cross-cancellation/probe.json")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "finiteHeightSamples"}, indent=2))


if __name__ == "__main__":
    main()

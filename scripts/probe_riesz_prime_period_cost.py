#!/usr/bin/env python3
"""Optional finite-prime diagnostic; never an analytic certificate.

These accessible primes are BELOW the rigorous log-prime cutoff 5000.
The experiment checks signed moments and endpoint effects, not the
large-range theorem, source normalization, or the full Riesz carrier.
"""

from array import array
from bisect import bisect_right
import json
import math


def prime_table(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p::p] = b"\x00" * ((limit - p * p) // p + 1)
    return array("I", (p for p, flag in enumerate(sieve) if flag))


def period(primes, base, y, n):
    half = math.pi / abs(y)
    cofactor = math.log(n)
    index = math.ceil(((base + half + cofactor) / half - 1) / 2)
    centre = (2 * index + 1) * half
    lower = centre - half - cofactor
    upper = lower + 2 * half
    lo = bisect_right(primes, math.exp(lower))
    hi = bisect_right(primes, math.exp(upper))
    moment0 = math.fsum(math.cos(y * (math.log(p) + cofactor)) / p for p in primes[lo:hi])
    moment1 = math.fsum((math.log(p) + cofactor - centre)
                       * math.cos(y * (math.log(p) + cofactor)) / p for p in primes[lo:hi])
    clipped_upper = lower + 0.37 * (upper - lower)
    clipped_hi = bisect_right(primes, math.exp(clipped_upper))
    clipped = math.fsum(math.cos(y * (math.log(p) + cofactor)) / p
                       for p in primes[lo:clipped_hi])
    boundary = (math.sin(y * (clipped_upper + cofactor))
                - math.sin(y * (lower + cofactor))) / (y * lower)
    return {"basePrimeLog": lower, "height": y, "cofactor": n, "primeCount": hi - lo,
            "scaledZerothMoment": moment0 * lower**2,
            "scaledFirstMoment": moment1 * lower**2,
            "clippedSignedSum": clipped, "clippedBoundaryMain": boundary,
            "scaledClippedDiscrepancy": (clipped - boundary) * lower**2}


def moebius(n):
    parity = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            parity = -parity
            if n % p == 0:
                return 0
        p += 1
    return -parity if n > 1 else parity


def cofactor_shell(primes, M, y):
    half = math.pi / abs(y)
    centre = (2 * math.ceil(((13 + math.log(2 * M)) / half - 1) / 2) + 1) * half
    signed = []
    local_bounds = []
    count = 0
    for n in range(M + 1, 2 * M + 1):
        sign = moebius(n)
        if not sign:
            continue
        count += 1
        lower = centre - half - math.log(n)
        upper = lower + 2 * half
        lo = bisect_right(primes, math.exp(lower))
        hi = bisect_right(primes, math.exp(upper))
        moment = math.fsum(math.cos(y * (math.log(p) + math.log(n))) / p for p in primes[lo:hi])
        signed.append(sign * moment / n)
        local_bounds.append(4 / (n * lower**2))
    H = math.fsum(1 / p for p in primes[:bisect_right(primes, 2 * M)])
    return {"M": M, "height": y, "squarefreeCofactors": count,
            "signedJointSum": math.fsum(signed),
            "sumAbsoluteAfterPrimeCancellation": math.fsum(abs(v) for v in signed),
            "inverseSquareBudgetDiagnostic": math.fsum(local_bounds),
            "allCountFormulaDiagnostic": 8 * (H * H + H) / math.log(M)**2}


def main():
    primes = prime_table(12_000_000)
    rows = [period(primes, base, y, n)
            for base in (10, 12, 14, 16)
            for y in (-128, 54, 128, 512)
            for n in (6, 30, 210)]
    shells = [cofactor_shell(primes, M, y) for M in (64, 256, 1024) for y in (54, 128)]
    print(json.dumps({"scope": __doc__.strip(), "rows": rows, "shells": shells,
                      "summary": {
                          "maxAbsScaledZeroth": max(abs(r["scaledZerothMoment"]) for r in rows),
                          "maxAbsScaledFirst": max(abs(r["scaledFirstMoment"]) for r in rows),
                          "maxAbsScaledClippedDiscrepancy": max(abs(r["scaledClippedDiscrepancy"]) for r in rows),
                      }}, indent=2))


if __name__ == "__main__":
    main()

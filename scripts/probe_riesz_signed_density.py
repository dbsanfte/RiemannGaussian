#!/usr/bin/env python3
"""Optional actual-integer regression for the signed rough-density bound.

The normalized coefficient is mu(n) prod_{p|n} 1/(p+1), with forbidden
prime intersections zero. These are complete reference prefixes, not the
remaining masked core carrier. No numerical floor or source saving is
certified. This script is deliberately outside ordinary CI.
"""

import argparse
import cmath
from fractions import Fraction
import json
import math
from pathlib import Path


def prime_table(limit):
    spf = list(range(limit + 1))
    for p in range(2, math.isqrt(limit) + 1):
        if spf[p] == p:
            for n in range(p * p, limit + 1, p):
                if spf[n] == n:
                    spf[n] = p
    return spf


def coefficients(limit, forbidden, spf, exact=False):
    zero, one = (Fraction(0), Fraction(1)) if exact else (0.0, 1.0)
    result = [zero] * (limit + 1)
    result[1] = one
    for n in range(2, limit + 1):
        p = spf[n]
        m = n // p
        if p not in forbidden and m % p:
            result[n] = -result[m] / (p + 1)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=20000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.limit < 128:
        parser.error("limit must be at least 128")
    spf = prime_table(args.limit)
    cases = []
    for forbidden in (set(), {2}, {3}, {23}, {2, 3, 5, 7}, {2, 7, 31}):
        exact = coefficients(128, forbidden, spf, exact=True)
        prefix = Fraction(0)
        for a in exact[1:]:
            prefix += a
            assert abs(prefix) <= 1
        a = coefficients(args.limit, forbidden, spf)
        prefix, log_prefix = 0.0, 0.0
        prefix_abs_max, prefix_min = 0.0, math.inf
        profile_samples = []
        twisted = {54.0: 0j, 19 * math.pi / math.log(2): 0j}
        twist_max = {y: 0.0 for y in twisted}
        sample_cuts = {128, 1024, 8192, args.limit}
        for n in range(1, args.limit + 1):
            prefix += a[n]
            log_prefix += a[n] * math.log(n)
            prefix_abs_max = max(prefix_abs_max, abs(prefix))
            prefix_min = min(prefix_min, prefix)
            for y in twisted:
                twisted[y] += a[n] * cmath.exp(-1j * y * math.log(n))
                twist_max[y] = max(twist_max[y], abs(twisted[y]))
            if n in sample_cuts:
                c = math.log(n)
                response = c * prefix - log_prefix
                assert abs(response) <= c + 1e-11
                profile_samples.append({"cutoff": n, "hingeHeight": c,
                                        "normalizedSignedHinge": response,
                                        "provedAllowance": c})
        assert prefix_abs_max <= 1 + 1e-11
        cases.append({"forbiddenPrimes": sorted(forbidden),
                      "normalizedPrefixAbsMaximum": prefix_abs_max,
                      "normalizedPrefixMinimum": prefix_min,
                      "finalNormalizedPrefix": prefix,
                      "exactRationalChecksThrough": 128,
                      "profiles": profile_samples,
                      "phaseTwistedPrefixAbsMaximum": {
                          str(y): twist_max[y] for y in twisted}})
    height = 19 * math.pi / math.log(2)
    exact_twist = 1 - cmath.exp(-1j * height * math.log(2)) / 3
    assert height > 54 and abs(exact_twist - 4 / 3) < 1e-12
    report = {"scope": "Complete actual-integer reference density prefixes only.",
              "limit": args.limit, "cases": cases,
              "phaseCounterexample": {"height": height, "cutoff": 2,
                                      "realPart": exact_twist.real,
                                      "provedExactValue": "4/3"},
              "maskedCarrierBoundCertified": False,
              "sourceScaleDecayCertified": False, "floorCertified": False}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": len(cases), "exactPrefixCutoff": 128,
                      "floatingPrefixCutoff": args.limit,
                      "phaseCounterexampleHeight": height,
                      "phaseCounterexampleRealPart": exact_twist.real,
                      "floorCertified": False}, indent=2))


if __name__ == "__main__":
    main()

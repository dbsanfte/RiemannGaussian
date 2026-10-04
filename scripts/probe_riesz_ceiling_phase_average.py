#!/usr/bin/env python3
"""Optional common-height regression with literal signed squarefree atoms.

This finite sample does NOT replace the native core or complete prime coverage.
It verifies the exact diagonal/cross-pair calculation on actual integer labels,
with signed Riesz coefficients and the original allocation orders collected
before squaring. There are no actual-zero samples or pointwise ceiling credits.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import time
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx


def prime64(n: int) -> bool:
    """Deterministic Miller--Rabin on the explicitly enforced n < 2^64 domain."""
    assert 1 < n < 2**64
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        value = pow(a, d, n)
        if value in (1, n - 1):
            continue
        for _ in range(s - 1):
            value = value * value % n
            if value == n - 1:
                break
        else:
            return False
    return True


def next_prime(n: int) -> int:
    n = max(3, n + (n % 2 == 0))
    while not prime64(n):
        n += 2
    return n


def record(x: arb) -> dict:
    """Save exact dyadic centre and radius as well as a readable enclosure."""
    mid, rad = x.mid().man_exp(), x.rad().man_exp()
    return {"ball": x.str(85), "mid": [str(mid[0]), int(mid[1])],
            "rad": [str(rad[0]), int(rad[1])]}


def orders(n: int) -> list[int]:
    # Literal lowerWing \ reserveOrders \ highOrders; no asymptotic endpoints.
    return [k for k in range(n + 2)
            if n + 1 < 8 * k < 7 * (n + 1)
            and 32 * k <= 15 * n + 64
            and not (13 * n // 32 + 1 <= k <= (15 * n + 64) // 32)
            and not (4 * n <= 5 * (n + 1 - k))]


def amplitude(n: int, factors: tuple[int, ...]) -> tuple[arb, arb, arb, arb]:
    u = Fraction(10001, 20000)
    ur = arb(u.numerator) / u.denominator
    cutoff = u.denominator**n // (u.numerator**n * (n + 1))
    length = 2 * arb(cutoff + 2).log()
    log_parts = [arb(p).log() for p in factors]
    total = sum(log_parts, arb(0))
    riesz = arb(0)
    for mask in range(1 << len(factors)):
        removed = sum((v for i, v in enumerate(log_parts) if mask >> i & 1), arb(0))
        hinge = length - removed
        assert hinge > 0 or hinge < 0  # No uncertain hinge is classified by its midpoint.
        if hinge > 0:
            riesz += (-1) ** mask.bit_count() * hinge
    assigned = arb(0)
    for p, part in zip(factors, log_parts):
        # All sampled prime factors lie in the ACTUAL physical interval.
        assert n**2 < p < (cutoff + 2) ** 2
        for k in orders(n):
            assigned += (total - part) ** k / math.factorial(k) * part ** (n + 1 - k) / math.factorial(n + 1 - k)
    share = assigned / (total ** (n + 1) / math.factorial(n + 1))
    assert share >= 0 and share <= 1
    coeff = -(1 - share) * total * riesz / length
    value = ur ** (n + 1) * coeff * total ** n / math.factorial(n) * (-(arb(3) / 2) * total).exp()
    return value, total, riesz, share


def window_mean(values: list[arb], logs: list[arb], h: int, t: int) -> arb:
    # Both incidences and the diagonal are kept. No per-prime random phases.
    value = sum((x * x for x in values), arb(0))
    for i, j in itertools.combinations(range(len(values)), 2):
        diff = logs[i] - logs[j]
        # Stable exact integral of cos(diff*y) over [h,h+t].
        mean_cos = (diff * (arb(h) + arb(t) / 2)).cos() * (diff * arb(t) / 2).sin() / (diff * arb(t) / 2)
        value += 2 * values[i] * values[j] * mean_cos
    return value


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(".lake/riesz-ceiling-phase-average/probe.json"))
    args = parser.parse_args()
    ctx.prec = 360
    started = time.monotonic()
    rows, all_primes = [], set()
    for n in (48, 64):
        samples = []
        for count in range(3, 11):
            factors = tuple(next_prime(int(math.exp(2 * n / count + 0.04 * (2 * i - count + 1) / (count - 1)))) for i in range(count))
            assert len(set(factors)) == count
            last = factors[-1]
            for repeat in range(3):
                if repeat:
                    last = next_prime(last + 2)
                selected = factors[:-1] + (last,)
                value, total, riesz, share = amplitude(n, selected)
                assert arb(39) * n / 20 < total <= arb(203) * n / 100
                samples.append({"factors": list(selected), "label": str(math.prod(selected)),
                                "coefficient": record(value), "log": record(total),
                                "riesz": record(riesz), "boundedShare": record(share)})
                all_primes.update(selected)
        assert len({sample["label"] for sample in samples}) == len(samples)
        # Deduplicated integer labels are the Fourier frequencies, not incidences.
        values = [arb(item["coefficient"]["ball"]) for item in samples]
        logs = [arb(item["log"]["ball"]) for item in samples]
        energy = sum((value * value for value in values), arb(0))
        normalized = [value / energy.sqrt() for value in values]
        cross = sum((4 * abs(normalized[i]) * abs(normalized[j]) / abs(logs[i] - logs[j])
                     for i, j in itertools.combinations(range(len(samples)), 2)), arb(0))
        minimum = min(abs(logs[i] - logs[j]) for i, j in itertools.combinations(range(len(samples)), 2))
        windows = []
        for h in (54, 1000):
            for t in (1, 100, 10**12, 10**22):
                mean = window_mean(normalized, logs, h, t)
                error = cross / t
                assert abs(mean - 1) <= error
                windows.append({"baseHeight": h, "windowLength": str(t),
                                "meanOverEnergy": record(mean), "finiteWindowErrorOverEnergy": record(error),
                                "rawMean": record(energy * mean)})
        rows.append({"N": n, "exactUnpaidOrders": orders(n), "samples": samples,
                     "energy": record(energy), "minimumLogSpacing": record(minimum),
                     "crossingCostOverEnergy": record(cross), "windows": windows})
    result = {"schemaVersion": 1, "precisionBits": 360,
              "classification": "finite literal-atom / common-height regression; not complete native-core enumeration",
              "radius": "10001/20000", "rows": rows, "distinctActualPrimeFactors": len(all_primes),
              "squarefreeLabels": sum(len(row["samples"]) for row in rows),
              "coreMembershipCertified": False, "joinedMultiplierApplied": False,
              "completeCoverageReplaced": False, "allCountsRetainedInLean": True,
              "actualZeroSamples": 0, "nativeEntryOrderCertified": False,
              "newPointwiseCeilingCredit": 0, "fullCeilingProved": False,
              "seconds": round(time.monotonic() - started, 3)}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("squarefreeLabels", "distinctActualPrimeFactors", "seconds")}))


if __name__ == "__main__":
    main()

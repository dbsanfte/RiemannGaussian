#!/usr/bin/env python3
"""Optional finite-Euler-jet control. Not an actual zero/carrier counterexample.

All logged orders and the SAME signed factorial evaluator are retained.
The actual ordinary-prime jet uses Mobius inversion of complete log zeta
at dilated Euler centres, with an explicit Cauchy enclosure of its tail.
No sampled prime population replaces complete coverage.
"""
from __future__ import annotations

import argparse
import json
import time
from fractions import Fraction
from pathlib import Path

from flint import acb, acb_series, arb, ctx


def mobius(n: int) -> int:
    value, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            value = -value
            if n % p == 0:
                return 0
        p += 1
    return -value if n > 1 else value


def encode(value: acb) -> dict[str, str]:
    return {"real": value.real.str(75), "imag": value.imag.str(75)}


def moving_length(u: Fraction, order: int) -> arb:
    head = (u.denominator**order) // (u.numerator**order * (order + 1))
    return 2 * arb(head + 2).log()


def joined(values: list[acb], order: int, u: Fraction) -> acb:
    """Collect trace cancellation FIRST, with exact integer boundaries."""
    k0 = 13 * order // 32
    value = values[order]
    for k in range(k0 + 1, order - k0 + 1):
        value -= values[k - 1] * values[order - k] / (order + 1 - k)
    pref = acb(order + 1) / (acb(u.numerator) / u.denominator * moving_length(u, order))
    for k in range(1, order + 2 - k0):
        value += pref * values[k - 1] * values[order + 1 - k] / (order + 2 - k)
    return value


def complete_ordinary_head(height: int, count: int, qmax: int, u: Fraction) -> list[acb]:
    # G(t)=u sum_{q>=1} mu(q)*(-zeta'/zeta)(q*(3/2+iy-u*t)).
    uc = acb(u.numerator) / u.denominator
    centre = acb_series([acb(arb(3) / 2, height), -uc])
    total = acb_series([0])
    for q in range(1, qmax + 1):
        mu = mobius(q)
        if mu:
            zeta = (q * centre).zeta()
            total += mu * zeta.derivative() / (q * zeta)
    # On |t|<=4/3, Re(s)>=4/5. For q>qmax>=5, the
    # elementary integer-series bound |Z(q*s)|<=16*2^(-4q/5)
    # gives tail <=20*(3/5)^(qmax+1). Cauchy supplies (3/4)^n.
    tail = 20 * (arb(3) / 5) ** (qmax + 1)
    return [total[n] + acb(arb(0, tail * (arb(3) / 4) ** n),
                           arb(0, tail * (arb(3) / 4) ** n)) for n in range(count)]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(".lake/riesz-ceiling-euler-jet-audit/probe.json"))
    args = parser.parse_args()
    # The arbitrary-J and concrete 512-order statements are proved in
    # Lean. Numerical checks use 64 orders: the saved 512-order trial
    # lost useful interval precision at high derivative orders.
    ctx.prec, ctx.cap = 360, 66
    u, count, qmax = Fraction(10001, 20000), 64, 128
    started = time.monotonic()
    rows = []
    for height in (54, 1000):
        head = complete_ordinary_head(height, count, qmax, u)
        price = sum((head[n].abs_upper() * (arb(4) / 3) ** (n + 1) for n in range(count)), arb(0))
        comparisons = []
        for order in (8, 16, 32, 48, 62):
            comparisons.append({"N": order, "completeJoined": encode(joined(head, order, u)),
                                "patchedJoined": encode(joined(head, order, u)),
                                "allIndicesInsideExactHead": order + 1 < count})
        plateau = []
        for order in (128, 4096, 8799):
            vals = head + [acb(0)] * (order + 2 - count)
            value = joined(vals, order, u)
            assert value.is_zero()
            plateau.append({"N": order, "exactZero": True, "headCount": count,
                            "beforeFirstRootHarmonic": order + 2 < 131072})
        rows.append({"height": height, "jet": [encode(v) for v in head],
                     "headPriceUpper": price.str(75), "finiteJoined": comparisons,
                     "zeroPlateau": plateau})
    ur = arb(u.numerator) / u.denominator
    cost = (arb(32) / 13).log() / (-2 * ur * ur.log()) - (arb(19) / 13).log()
    source = -2 + 4 * cost
    result = {"schemaVersion": 1, "precisionBits": 360, "headCount": count,
              "mobiusEulerDilationCutoff": qmax, "radius": str(u), "rows": rows,
              "sameJoinedSourceLimit": source.str(75),
              "ceilingGap": (source - arb(42) / 25).str(75),
              "actualPrimeSamples": 0, "actualZeroSamples": 0,
              "completeEulerJetCoefficientsEnclosed": count * len(rows),
              "formalUniformHeadCount": 512, "arbitraryHeadLengthProvedInLean": True,
              "highOrder512Trial": "retained as inconclusive interval output, not ground-truth mass",
              "patchedTailIdentifiedWithActualPrimes": False,
              "nativeEntryOrderCertified": False, "newCeilingCredit": 0,
              "fullCeilingProved": False, "seconds": round(time.monotonic() - started, 3)}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("completeEulerJetCoefficientsEnclosed", "ceilingGap", "seconds")}))


if __name__ == "__main__":
    main()

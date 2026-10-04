#!/usr/bin/env python3
"""Independent optional replay: log-series extraction and uncollapsed evaluator.

Does not import the probe. Scalar intervals do not certify an actual zero,
the infinite patched prime tail, or a native carrier entry order.
"""
from __future__ import annotations

import argparse
import json
import time
from fractions import Fraction
from pathlib import Path

from flint import acb, acb_series, arb, ctx


def mu(n: int) -> int:
    sign = 1
    for p in range(2, n + 1):
        if p * p > n:
            break
        if n % p:
            continue
        n //= p
        if n % p == 0:
            return 0
        sign *= -1
    return -sign if n > 1 else sign


def decode(value: dict[str, str]) -> acb:
    return acb(arb(value["real"]), arb(value["imag"]))


def exact_length(order: int) -> arb:
    power = Fraction(20000, 10001) ** order / (order + 1)
    length_head = power.numerator // power.denominator
    return arb((length_head + 2) ** 2).log()


def original_evaluation(values: list[acb], order: int) -> acb:
    # Compute BOTH exact trace slots independently. No index or diagonal
    # is removed from the original evaluator in this replay.
    conv = sum((values[k] * values[order - 1 - k] for k in range(order)), acb(0)) / order
    trace = -values[order] - conv
    lower = 13 * order // 32
    balanced = sum((values[k - 1] * values[order - k] / (order + 1 - k)
                    for k in range(order + 2)
                    if lower < k and lower < order + 1 - k), acb(0))
    prefix = sum((values[k - 1] * values[order + 1 - k] / (order + 2 - k)
                  for k in range(1, order + 2 - lower)), acb(0))
    lam = acb(order + 1) / (acb(10001) / 20000 * exact_length(order))
    harmonic = conv + balanced - lam * prefix
    return -trace - harmonic


def ordinary_coefficients(height: int, count: int, qmax: int) -> list[acb]:
    centre = acb_series([acb(arb(3) / 2, height), -acb(10001) / 20000])
    logarithm = acb_series([0])
    for q in range(1, qmax + 1):
        sign = mu(q)
        if sign:
            logarithm += sign * (q * centre).zeta().log() / q
    # d/dt log zeta at this centre has precisely the full prime
    # factorial normalization. Extract via log coefficients, rather
    # than the probe's zeta-derivative quotient.
    cutoff_bound = 20 * (arb(3) / 5) ** (qmax + 1)
    return [(n + 1) * logarithm[n + 1] +
            acb(arb(0, cutoff_bound * (arb(3) / 4) ** n),
                arb(0, cutoff_bound * (arb(3) / 4) ** n)) for n in range(count)]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=Path(".lake/riesz-ceiling-euler-jet-audit/probe.json"))
    parser.add_argument("--output", type=Path, default=Path(".lake/riesz-ceiling-euler-jet-audit/numeric-replay.json"))
    args = parser.parse_args()
    ctx.prec, ctx.cap = 420, 66
    started = time.monotonic()
    data = json.loads(args.input.read_text())
    count, qmax = data["headCount"], data["mobiusEulerDilationCutoff"]
    assert count == 64 and qmax == 128
    assert data["formalUniformHeadCount"] == 512 and data["arbitraryHeadLengthProvedInLean"]
    assert data["actualPrimeSamples"] == data["actualZeroSamples"] == 0
    assert not data["patchedTailIdentifiedWithActualPrimes"]
    assert not data["nativeEntryOrderCertified"] and data["newCeilingCredit"] == 0
    # Exact rational blocks used in the Lean proof, independently replayed.
    assert Fraction(10001, 10000) ** 512 <= 2
    assert Fraction(4, 3) ** 128 <= 10**17
    assert Fraction(512 * 200000) * 10**68 <= 10**77
    assert 4 * 131072 + 10**77 <= 10**78
    # Quantitative complex-Euler tail checks. The first integer term
    # plus its decreasing integral bound the entire log mass at four.
    mass_at_four = arb(2).log() / 16 + arb(3).log() / 81 + (arb(3).log() / 3 + arb(1) / 9) / 27
    assert mass_at_four < 1
    sigma_min = arb(3) / 2 - arb(10001) / 20000 * arb(4) / 3
    assert sigma_min > arb(4) / 5
    assert (-(arb(4) / 5) * arb(2).log()).exp() < arb(3) / 5
    assert 16 * (arb(10001) / 20000) / (1 - arb(3) / 5) < 21
    # The tail prefactor is actually <20.002; use the sharper ratio
    # 2^-sigma_min here to validate the probe's deliberately round 20.
    ratio = (-sigma_min * arb(2).log()).exp()
    assert 16 * (arb(10001) / 20000) / (1 - ratio) < 20
    coefficient_rows = evaluator_rows = plateaux = 0
    prices = []
    for item in data["rows"]:
        values = ordinary_coefficients(item["height"], count, qmax)
        for n, previous in enumerate(item["jet"]):
            assert values[n].overlaps(decode(previous)), (item["height"], n)
            coefficient_rows += 1
        price = sum((values[n].abs_upper() * (arb(4) / 3) ** (n + 1) for n in range(count)), arb(0))
        # Both methods enclose the same true price; this numerical
        # reported price is not substituted for the formal 10^77 bound.
        assert price < 10**77
        prices.append({"height": item["height"], "headPriceUpper": price.str(50)})
        for row in item["finiteJoined"]:
            value = original_evaluation(values, row["N"])
            assert value.overlaps(decode(row["completeJoined"]))
            assert value.overlaps(decode(row["patchedJoined"]))
            assert row["N"] + 1 < count
            evaluator_rows += 1
        for row in item["zeroPlateau"]:
            n = row["N"]
            assert row["exactZero"] and n >= 2 * count and n + 2 < 131072
            value = original_evaluation(values + [acb(0)] * (n + 2 - count), n)
            assert value.is_zero()
            plateaux += 1
    u = arb(10001) / 20000
    cost = (arb(32) / 13).log() / (-2 * u * u.log()) - (arb(19) / 13).log()
    limit = -2 + 4 * cost
    assert limit.overlaps(arb(data["sameJoinedSourceLimit"]))
    assert limit - arb(42) / 25 > arb(1) / 2000
    result = {"precisionBits": 420, "completeEulerJetRows": coefficient_rows,
              "unchangedEvaluatorRows": evaluator_rows, "exactZeroPlateaux": plateaux,
              "exactRationalBlocksPassed": True, "cauchyEulerTailChecked": True,
              "prices": prices, "newCeilingCredit": 0, "fullCeilingProved": False,
              "actualPrimeSamples": 0, "actualZeroSamples": 0,
              "nativeEntryOrderCertified": False,
              "seconds": round(time.monotonic() - started, 3)}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()

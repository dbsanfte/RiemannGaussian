#!/usr/bin/env python3
"""Independent optional replay of literal atoms and common-height integration.

420-bit complex integration is compared with the probe's real sinc formula;
selected short windows also get an independent direct quadrature. No completed
native carrier, actual zero or pointwise endgame bound is inferred from these
finite regressions.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import time
from fractions import Fraction
from pathlib import Path

import mpmath as mp
from flint import acb, arb, ctx, fmpz


def decode(entry: dict) -> arb:
    centre = arb(int(entry["mid"][0])) * arb(2) ** entry["mid"][1]
    radius = arb(int(entry["rad"][0])) * arb(2) ** entry["rad"][1]
    return arb(centre, radius)


def verify(value: arb, stored: dict) -> None:
    ball = decode(stored)
    assert value.overlaps(ball), (value, ball)
    # Track widths; no interval inflation is mistaken for actual mass.
    assert ball.rad() <= (1 + ball.abs_upper()) * arb(10) ** -45


def literal_atom(n: int, factors: list[int]) -> tuple[arb, arb, arb, arb]:
    q = Fraction(20000, 10001) ** n / (n + 1)
    cutoff = q.numerator // q.denominator
    length = arb((cutoff + 2) ** 2).log()
    label = math.prod(factors)
    total = arb(label).log()
    riesz = arb(0)
    # Enumerate ACTUAL divisors as integers, rather than adding prime logs.
    for size in range(len(factors) + 1):
        for subset in itertools.combinations(factors, size):
            hinge = length - arb(math.prod(subset)).log()
            assert hinge > 0 or hinge < 0
            if hinge > 0:
                riesz += (-1) ** size * hinge
    middle = {k for k in range(n + 2) if n + 1 < 8 * k < 7 * (n + 1)}
    lower = {k for k in middle if 32 * k <= 15 * n + 64}
    reserve = set(range(13 * n // 32 + 1, (15 * n + 64) // 32 + 1))
    high = {k for k in lower if 4 * n <= 5 * (n + 1 - k)}
    allocation = arb(0)
    for p in factors:
        assert fmpz(p).is_prime()
        assert n * n < p < (cutoff + 2) ** 2
        x = arb(p).log() / total
        # Binomial marginals give a second exact route to the allocated fraction.
        for k in sorted(lower - reserve - high):
            allocation += math.comb(n + 1, k) * (1 - x) ** k * x ** (n + 1 - k)
    ur = arb(10001) / 20000
    coefficient = -(1 - allocation) * total * riesz / length
    value = ur ** (n + 1) * coefficient * total ** n / math.factorial(n) / arb(label).sqrt() ** 3
    return value, total, riesz, allocation


def complex_mean(values: list[arb], logs: list[arb], h: int, t: int) -> arb:
    total = acb(0)
    imaginary = acb(0, 1)
    for i in range(len(values)):
        for j in range(len(values)):
            if i == j:
                pair = acb(1)
            else:
                delta = logs[i] - logs[j]
                pair = ((-imaginary * delta * (h + t)).exp() - (-imaginary * delta * h).exp()) / (-imaginary * delta * t)
            total += values[i] * values[j] * pair
    assert total.imag.contains(0)
    return total.real


def quadrature(values: list[arb], logs: list[arb], h: int, t: int) -> arb:
    # Remove only the unit-modulus common character, preserving every relative phase.
    coefs = [mp.mpf(str(v.mid().str(130, radius=False))) for v in values]
    frequencies = [mp.mpf(str(v.mid().str(130, radius=False))) for v in logs]
    frequencies = [x - frequencies[0] for x in frequencies]

    def integrand(y: mp.mpf) -> mp.mpf:
        whole = sum(c * mp.exp(-1j * f * y) for c, f in zip(coefs, frequencies))
        return abs(whole) ** 2

    answer = mp.quad(integrand, [mp.mpf(h), mp.mpf(h + t)]) / t
    return arb(mp.nstr(answer, 125))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=Path(".lake/riesz-ceiling-phase-average/probe.json"))
    parser.add_argument("--output", type=Path, default=Path(".lake/riesz-ceiling-phase-average/numeric-replay.json"))
    args = parser.parse_args()
    ctx.prec, mp.mp.prec = 420, 440
    started = time.monotonic()
    data = json.loads(args.input.read_text())
    assert data["actualZeroSamples"] == data["newPointwiseCeilingCredit"] == 0
    assert not data["completeCoverageReplaced"] and not data["coreMembershipCertified"]
    assert not data["joinedMultiplierApplied"] and not data["fullCeilingProved"]
    assert Fraction(10001, 15000) ** 2 < 1
    atom_count = pair_windows = direct_windows = 0
    diagnostics = []
    for row in data["rows"]:
        values, logs = [], []
        for sample in row["samples"]:
            factors = sample["factors"]
            assert len(set(factors)) == len(factors) and 3 <= len(factors) <= 10
            assert str(math.prod(factors)) == sample["label"]
            value, log, riesz, share = literal_atom(row["N"], factors)
            for computed, key in ((value, "coefficient"), (log, "log"), (riesz, "riesz"), (share, "boundedShare")):
                verify(computed, sample[key])
            values.append(value)
            logs.append(log)
            atom_count += 1
        energy = sum((v * v for v in values), arb(0))
        verify(energy, row["energy"])
        normalized = [v / energy.sqrt() for v in values]
        crossing = sum((4 * abs(normalized[i]) * abs(normalized[j]) / abs(logs[i] - logs[j])
                        for i, j in itertools.combinations(range(len(values)), 2)), arb(0))
        verify(crossing, row["crossingCostOverEnergy"])
        for item in row["windows"]:
            h, t = item["baseHeight"], int(item["windowLength"])
            mean = complex_mean(normalized, logs, h, t)
            verify(mean, item["meanOverEnergy"])
            verify(mean * energy, item["rawMean"])
            assert abs(mean - 1) <= crossing / t
            pair_windows += 1
            if t <= 100:
                direct = quadrature(normalized, logs, h, t)
                verify(direct, item["meanOverEnergy"])
                direct_windows += 1
        diagnostics.append({"N": row["N"], "minimumLogSpacing": row["minimumLogSpacing"]["ball"],
                            "crossingCostOverEnergy": crossing.str(55),
                            "shortWindowRatio": row["windows"][0]["meanOverEnergy"]["ball"],
                            "longWindowRatio": row["windows"][3]["meanOverEnergy"]["ball"]})
    result = {"precisionBits": 420, "directQuadratureBits": 440, "literalAtomsReplayed": atom_count,
              "complexPairWindows": pair_windows, "directQuadratureWindows": direct_windows,
              "diagonalAndBothIncidencesRetained": True, "intervalWidthsChecked": True,
              "classification": "finite regression only; full native theorem is proved separately in Lean",
              "newPointwiseCeilingCredit": 0, "fullCeilingProved": False,
              "diagnostics": diagnostics, "seconds": round(time.monotonic() - started, 3)}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("literalAtomsReplayed", "complexPairWindows", "directQuadratureWindows", "seconds")}))


if __name__ == "__main__":
    main()

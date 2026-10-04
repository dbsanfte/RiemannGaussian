#!/usr/bin/env python3
"""Independent 420-bit replay; never imports the numerical producer.

This validates finite scalar balls only. It does not certify an actual
prime-array entry order, an arithmetic floor, or any zeta zero exclusion.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import arb, ctx, fmpz


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, nargs="?", default=Path("data/riesz-factorial-cutoff-probe.json"))
    parser.add_argument("--output", type=Path, default=Path("data/riesz-factorial-cutoff-replay.json"))
    args = parser.parse_args()
    document = json.loads(args.input.read_text())
    assert document["schema"] == "riesz-factorial-cutoff-scalar-v1"
    assert document["proof_dependency"] is False
    assert document["ordinary_ci"] is False
    ctx.prec = 420
    checked = 0

    def compare(row: dict, key: str, value: arb) -> None:
        nonlocal checked
        assert arb(row[key]).contains(value), (key, row, value)
        checked += 1

    for row in document["source_rows"]:
        numerator, denominator = row["u"]
        u = arb(numerator) / denominator
        c = -2 * u * u.log()
        s0 = 1 + (arb(19) / 13).log() - (arb(32) / 13).log() / c
        s1 = 1 + (arb(2431) / 1665).log() - (arb(4096) / 1665).log() / c
        # Narrow ratios independently evaluate the transition directly.
        delta = (arb(31635) / 31603).log() - (arb(1665) / 1664).log() / c
        assert (s0 - s1).overlaps(delta)
        compare(row, "S0", s0)
        compare(row, "S1", s1)
        compare(row, "transition_source", delta)
        compare(row, "centered_source_per_m", 1 / c - arb(4096) / 2431)
        compare(row, "original_gap", s0 - arb(399) / 5000)
        compare(row, "candidate_headroom", arb(399) / 5000 - s1)
        compare(row, "maximum_transition_fraction_using_candidate_limit", (arb(399) / 5000 - s1) / delta)
        assert delta > arb(1) / 7000
        assert s1 < arb(399) / 5000

    for row in document["finite_rows"]:
        numerator, denominator = row["u"]
        u = arb(numerator) / denominator
        n, m = row["N"], row["multiplicity"]
        k0, k1 = row["K0"], row["K1"]
        assert k0 == 1664 * n // 4096 == 13 * n // 32
        assert k1 == 1665 * n // 4096
        assert row["steps"] == k1 - k0 == n // 4096
        length = arb((fmpz(denominator) ** n // (fmpz(numerator) ** n * (n + 1)) + 2) ** 2).log()
        compare(row, "length", length)
        h = []
        for k in [k0, k1]:
            h.append(m ** 2 * (1 + arb(n - k + 1).digamma() - arb(k + 1).digamma()
                - arb(n + 1) / (u * length) * (arb(n + 2).digamma() - arb(k + 1).digamma())))
        compare(row, "H0", h[0])
        compare(row, "H1", h[1])
        # Replay through the factored centered increment, not H0-H1.
        increments = []
        for k in range(k0, k1):
            defect = -m / arb(n - k) + m / (u * length)
            increments.append(arb(n + 1) / (k + 1) * (-m) * defect)
        value = sum(increments)
        assert value > 0
        assert (h[0] - h[1]).overlaps(value)
        compare(row, "transition", value)
        compare(row, "step_sum", value)
        compare(row, "scaled_centered", -m * (arb(n + 1) / (n - k1) - arb(n + 1) / (u * length)))

    report = {"schema": "riesz-factorial-cutoff-replay-v1", "precision_bits": 420,
        "independent_producer_import": False, "comparisons": checked,
        "all_finite_balls_enclosed": True,
        "scope": "scalar/source-model controls only; no actual prime sum or zero certificate",
        "independent_floor_credit": 0, "rh_proved": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed {checked} independent finite-ball comparisons")


if __name__ == "__main__":
    main()

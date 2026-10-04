#!/usr/bin/env python3
"""Optional scalar ball audit of the fixed-N factorial-cutoff experiment.

These are exact constant/source-array controls, NOT actual prime sums or
zeros. Finite controls retain the repository's integer-floor moving length.
The Lean source and obstruction proofs do not depend on this numerical file.
This script is intentionally outside the ordinary CI/build path.
"""
from __future__ import annotations

import argparse
import importlib.metadata
import json
import subprocess
from pathlib import Path

from flint import arb, ctx, fmpz


def ball(value: arb) -> str:
    return value.str(100, radius=True)


def run() -> dict:
    ctx.prec = 360
    source_rows = []
    finite_rows = []
    for numerator, denominator in [(1, 2), (20001, 40000), (10001, 20000)]:
        u = arb(numerator) / denominator
        damping = -2 * u * u.log()
        theta0, theta1 = arb(13) / 32, arb(1665) / 4096
        s0 = 1 + ((1 - theta0) / theta0).log() - (1 / theta0).log() / damping
        s1 = 1 + ((1 - theta1) / theta1).log() - (1 / theta1).log() / damping
        difference = s0 - s1
        centered = -1 * (1 / (1 - theta1) - 1 / damping)
        assert difference > arb(1) / 7000
        assert s1 < arb(399) / 5000
        assert centered < 0
        source_rows.append({
            "u": [numerator, denominator],
            "S0": ball(s0), "S1": ball(s1),
            "transition_source": ball(difference),
            "centered_source_per_m": ball(centered),
            "original_gap": ball(s0 - arb(399) / 5000),
            "candidate_headroom": ball(arb(399) / 5000 - s1),
            "maximum_transition_fraction_using_candidate_limit": ball((arb(399) / 5000 - s1) / difference),
        })
        for n in [4096, 16384, 65536, 262144]:
            # Compute the literal floor with exact integers, not floating exp.
            cutoff = fmpz(denominator) ** n // (fmpz(numerator) ** n * (n + 1))
            length = 2 * arb(cutoff + 2).log()
            factor = arb(n + 1) / (u * length)
            k0, k1 = 13 * n // 32, 1665 * n // 4096
            assert k1 - k0 == n // 4096

            def harmonic_value(k: int) -> arb:
                # Euler's constant cancels between genuine harmonic endpoints.
                return 1 + arb(n - k + 1).digamma() - arb(k + 1).digamma() - factor * (
                    arb(n + 2).digamma() - arb(k + 1).digamma())

            h0, h1 = harmonic_value(k0), harmonic_value(k1)
            step_sum = sum((arb(n + 1) / (k + 1) * (
                1 / arb(n - k) - 1 / (u * length))) for k in range(k0, k1))
            assert (h0 - h1).overlaps(step_sum)
            assert step_sum > 0
            for multiplicity in [1, 2]:
                scaled_centered = -multiplicity * (arb(n + 1) / (n - k1) - factor)
                assert scaled_centered < 0
                finite_rows.append({
                    "u": [numerator, denominator], "N": n,
                    "multiplicity": multiplicity, "K0": k0, "K1": k1,
                    "steps": k1 - k0, "length": ball(length),
                    "H0": ball(multiplicity ** 2 * h0),
                    "H1": ball(multiplicity ** 2 * h1),
                    "transition": ball(multiplicity ** 2 * (h0 - h1)),
                    "step_sum": ball(multiplicity ** 2 * step_sum),
                    "scaled_centered": ball(scaled_centered),
                })
    return {
        "schema": "riesz-factorial-cutoff-scalar-v1",
        "source_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "precision_bits": 360,
        "python_flint": importlib.metadata.version("python-flint"),
        "scope": "finite scalar/source-model ball controls; no actual primes or zeros",
        "proof_dependency": False, "ordinary_ci": False,
        "source_rows": source_rows, "finite_rows": finite_rows,
        "verdict": "positive coherent transition; no independent floor credit",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("data/riesz-factorial-cutoff-probe.json"))
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Saved {len(result['source_rows'])} source and {len(result['finite_rows'])} finite controls to {args.output}")


if __name__ == "__main__":
    main()

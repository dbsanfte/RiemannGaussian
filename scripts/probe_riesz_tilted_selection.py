#!/usr/bin/env python3
"""Optional exact-geometry/ball-value audit of tilted zero selection.

The points below are synthetic, not asserted to be zeta zeros. The only
integral evaluated is the exact two-chamber minimum moment already proved
in Lean. It is not the joined Riesz/count sum or a prime-sum estimate.
Requires the optional requirements-riesz-balls.txt environment; not CI.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import importlib.metadata
import json
from pathlib import Path

from flint import arb, ctx


def ball(x):
    return arb(x.numerator) / x.denominator


def run():
    ctx.prec = 192
    beta, gamma = Q(999951, 1000000), Q(100)
    slope, gain, remote = Q(1, 10**9), Q(1, 10**6), Q(10**6)
    u = Q(3, 2) - beta
    y = gamma - slope * u
    d, eta = u - gain, remote + y
    selected_score = beta - slope * gamma
    assert selected_score > Q(19999, 20000)
    assert 0 < d < u < Q(10001, 20000)
    assert beta + gain < 1
    points = [(beta, gamma), (beta + gain, remote), (beta + gain, remote + 2*y)]
    # Include conjugation and functional-equation symmetries as geometry
    # checks, with no claim that these numbers belong to the zeta divisor.
    symmetric = {(b, g) for b0, g0 in points for b in (b0, 1-b0) for g in (g0, -g0)}
    upper = sorted((b, g) for b, g in symmetric if g >= 0)
    gaps = []
    for b, g in upper:
        gap = selected_score - (b - slope*g)
        if (b, g) != (beta, gamma):
            assert gap > 0
        gaps.append(dict(beta=str(b), gamma=str(g), score_gap=str(gap)))
    # The negative-height member and a different positive-height member
    # have cancelling offsets at the tilted evaluation height.
    assert y - (-remote) == eta
    assert y - (remote + 2*y) == -eta
    source_norm = (ball(u)**2 + ball(slope*u)**2).sqrt()
    remote_norm = (ball(d)**2 + ball(eta)**2).sqrt()
    assert ball(u) < source_norm < ball(Q(10001, 20000))
    assert remote_norm > 10**6
    log_rate = (ball(u)/ball(d)).log()
    rows = []
    for order in (10**6, 10**7, 2*10**7, 4*10**7):
        log_value = order*log_rate - (ball(d)**2 + ball(eta)**2).log()
        rows.append(dict(order=order, log_normalized_minimum=str(log_value),
                         normalized_minimum=str(log_value.exp())))
    return dict(
        scope="Synthetic symmetric points and the exact two-chamber minimum moment only. "
              "No joined Riesz/count cancellation, arithmetic transport, or actual zero claim.",
        beta=str(beta), gamma=str(gamma), slope=str(slope), horizontal_gain=str(gain),
        remote_height=str(remote), evaluation_height=str(y), u=str(u),
        upper_scores=gaps, source_norm=str(source_norm), remote_norm=str(remote_norm),
        minimum_growth_exponent=str(log_rate), moments=rows,
        exact_formula="(u/d)^h / (d^2 + eta^2)",
        lean_theorems=[
            "ZetaTiltedZeroSelection.exists_unique_upper_max",
            "ZetaTiltedZeroSelection.remote_pair_denominators",
            "ZetaTiltedZeroSelection.remote_minimum_tendsto"],
        versions={name: importlib.metadata.version(name) for name in ("python-flint",)},
        probe_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))

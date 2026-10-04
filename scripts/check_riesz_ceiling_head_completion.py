#!/usr/bin/env python3
"""Independent 420-bit replay: divisor enumeration, phases and source scalars.

Does not import the producer or identify fixed finite completion heads with
the native core. Ball overlap AND relative enclosure widths are checked.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

from flint import acb, arb, ctx


def load_ball(row: dict) -> arb:
    m, r = row["mid"], row["rad"]
    return arb(int(m[0]))*arb(2)**int(m[1])+arb(0, int(r[0]))*arb(2)**int(r[1])


def compare(row: dict, expected: arb) -> None:
    stored = load_ball(row)
    assert stored.overlaps(expected)
    if expected == 0:
        assert stored == 0
        return
    scale = abs(expected)
    # Relative precision at tiny nonzero factorial amplitudes is required;
    # absolute smallness alone cannot certify the row.
    assert stored.rad() < scale*arb(2)**(-290)
    assert expected.rad() < scale*arb(2)**(-350)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/riesz-ceiling-head-completion-audit/numeric-replay.json"))
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    ctx.prec = 420
    assert data["precisionBits"] == 360 and len(data["primeRows"]) == 144
    comparisons = 0
    for row in data["primeRows"]:
        p, q, N, y = (row[k] for k in ("p", "q", "N", "height"))
        n = p*q
        x, z, T = arb(p).log(), arb(q).log(), arb(n).log()
        L = x+z/2
        assert n % p == n % q == 0 and n//p == q and n//q == p
        assert all(v == 0 for v in row["assignedShareByPhysicalSelection"].values())
        assert row["markedRectangleMass"] == 0 and row["fullComplementMass"] == 1
        assert row["nativeCoreMember"] is False
        # Enumerate the complete squarefree divisor response independently.
        response = arb(0)
        for d, mu in ((1, 1), (p, -1), (q, -1), (n, 1)):
            t = L-arb(d).log()
            response += mu*(t if t > 0 else arb(0))
        coefficient = -T*response/L
        atom = acb(coefficient*T**N/arb(math.factorial(N)))*(
            -acb(arb(3)/2, arb(y))*T).exp()
        compare(row["testLength"], L)
        compare(row["firstHinge"], -response)
        compare(row["secondHinge"], -response)
        compare(row["atomRe"], atom.real)
        compare(row["atomIm"], atom.imag)
        compare(row["exactNorm"], abs(atom))
        comparisons += 6
        assert coefficient < 0 and abs(atom) > 0
    u = arb(10001)/20000
    c = (arb(32).log()-arb(13).log())/(-2*u*u.log())-(arb(19).log()-arb(13).log())
    for row in data["sourceScalarRows"]:
        m = row["multiplicity"]
        head = m*m*(1-c)
        main = -m+m*m*c
        compare(row["retainedPairSource"], head)
        compare(row["joinedSource"], main)
        compare(row["completedTrace"], arb(m*m-m))
        assert (main+head).overlaps(arb(m*m-m))
        comparisons += 3
    assert data["newGlobalCeilingCredit"] == 0
    result = {"passed": True, "precisionBits": 420,
              "finiteActualPairRows": len(data["primeRows"]),
              "sourceScalarRows": len(data["sourceScalarRows"]),
              "ballComparisons": comparisons, "relativeWidthsChecked": True,
              "producerImported": False, "nativeCoreEnumerated": False,
              "actualZeroSamples": 0, "fullConstantCeilingProved": False,
              "newGlobalCeilingCredit": 0, "headCompletionShortcutPassed": False}
    args.output.write_text(json.dumps(result, indent=2)+"\n")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact coefficient/content checks of the known-residue bivariate proposal.

Private factors occur only in labelled reference diagnostics. This
probe is not an N-only factoring algorithm or a runtime certificate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import random

import gmpy2

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-q-aggregate-audit.json"
REPLAY_ID = 202610032701


def inspect_case(p, q, width=None):
    """Verify the literal known-residue polynomial against reference factors."""
    n = p*q
    b = int(gmpy2.iroot(n, 6)[0]) if width is None else width
    if b <= 1 or math.gcd(p, b) != 1:
        return None
    a = b**3+p % b
    c = b**3+(n*pow(a, -1, b)) % b
    assert (a*c-n) % b == 0 and (p-a) % b == 0 and (q-c) % b == 0
    d, x, y = (a*c-n)//b, (p-a)//b, (q-c)//b
    original = [a*c-n, b*c, b*a, b*b]
    divided = [d, c, a, b]
    assert all(u == b*v for u, v in zip(original, divided))
    assert original[0]+original[1]*x+original[2]*y+original[3]*x*y == 0
    assert divided[0]+divided[1]*x+divided[2]*y+divided[3]*x*y == 0
    content = math.gcd(*original)
    assert content % b == 0 and math.gcd(*divided) == 1
    box = int(gmpy2.iroot(n, 3)[0])+1
    assert abs(x) <= box and abs(y) <= box
    original_height = max(abs(original[0]), abs(original[1])*box,
        abs(original[2])*box, abs(original[3])*box*box)
    divided_height = max(abs(divided[0]), abs(divided[1])*box,
        abs(divided[2])*box, abs(divided[3])*box*box)
    assert original_height == b*divided_height
    wrong_value = (a*c-n)+c*x+a*y+b*b*x*y
    return dict(N=n, reference_p=p, reference_q=q, B=b, A=a, C=c, D=d,
        reference_x=x, reference_y=y, original_coefficients=original,
        divided_coefficients=divided, integer_content=content,
        primitive_content=1, root_box=box, original_scaled_height=original_height,
        divided_scaled_height=divided_height,
        divided_height_criterion=(box*box)**3 < divided_height**2,
        idealised_cleared_criterion=n**3 < n*n*b**4,
        fourth_power_criterion=n < b**4, dropped_linear_factor_value=wrong_value)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeKnownBitsBudget.lean",
        "scripts/CheckSemiprimeKnownBitsBudget.lean", "scripts/probe_semiprime_known_bits_budget.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import primerange
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources = source_inventory()
    rnd, primes, cases = random.Random(REPLAY_ID), list(primerange(101, 2000)), []
    while len(cases) < 192:
        p, q = sorted(rnd.sample(primes, 2))
        if q >= 2*p:
            continue
        case = inspect_case(p, q)
        if case is not None:
            cases.append(case)
    controls = [inspect_case(101, 103, 4), inspect_case(1000000007, 1400000543)]
    assert controls[0]["original_coefficients"] == [-6048, 268, 260, 16]
    assert controls[0]["integer_content"] == 4
    assert controls[0]["dropped_linear_factor_value"] == -3564
    for c in cases+controls:
        assert c["idealised_cleared_criterion"] == c["fourth_power_criterion"]
    scale_checks = []
    for b in range(2, 258):
        n = b**6
        assert not n**3 < n*n*b**4
        scale_checks.append(dict(B=b, N=n, idealised_cleared_criterion=False))
    assert source_inventory() == sources, "source changed during replay"
    report = dict(replay_id=REPLAY_ID, source_sha256=sources,
        scope="Known-residue polynomial content and correctly cleared height-budget audit",
        one_sixth_guarantee="OPEN", is_complete_semiprime_factorizer=False,
        is_bit_complexity_certificate=False, is_formal_machine_refinement=False,
        universal_content_and_budget_identities_lean=True,
        validation=dict(balanced_reference_cases=len(cases), exact_controls=len(controls),
            sixth_scale_checks=len(scale_checks), original_integer_content_retained=True,
            coefficient_expansion_matches=True, private_factors_used_only_as_references=True),
        controls=controls, cases=cases, sixth_scale_checks=scale_checks,
        primary_lead="https://arxiv.org/pdf/1308.2891v3",
        limitations="This checks the proposed encoding, not a factoring algorithm or an LLL implementation. Lean proves its content-B factorisation, nonirreducibility over the integer polynomial ring for B>1, and the idealised cleared height criterion N<B^4. It does not prove a general obstruction to other lattice methods or all known-bit algorithms. The complete every-run N-only one-sixth bit theorem remains open.")
    if args.output:
        args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources), validation=report["validation"],
        first_control=controls[0], large_control=controls[1], one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()

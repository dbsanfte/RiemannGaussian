#!/usr/bin/env python3
"""Target-preserving public row centering with charged N-only source replay.

The frozen controller is reused with new row/length constructors, without
changing its globals or calling an earlier factorizer inside the new timer.
Original rows and signed indices remain in the packet. Centering improves
the explicit interval constant; the one-sixth bit guarantee remains open.
"""
from __future__ import annotations

from collections import Counter
import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import types

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-quotient-rows-audit.json"
REPLAY_ID = 202610032901
PARENT = runpy.run_path(str(ROOT/"scripts/probe_semiprime_quotient_rows.py"))
IntegerLedger = PARENT["IntegerLedger"]


def public_box(n, integers):
    """All endpoints are computed from N, with literal integer floors."""
    half = integers.divmod(n, 2)[0]
    return integers.sqrt(half), integers.sqrt(n), integers.sqrt(integers.mul(2, n))


def centered_length(n, m, integers):
    low, _, high = public_box(n, integers)
    s, square = integers.sqrt(m), integers.mul(m, m)
    width = integers.add(high, -low)
    numerator = integers.add(integers.mul(s, width), square)
    denominator = integers.mul(2, square)
    return integers.add(integers.divmod(numerator, denominator)[0], 1)


def centered_row(n, m, j, integers, threshold=None):
    """Retain the public original row and its exact signed center phase."""
    source = PARENT["public_row"](n, m, j, integers, threshold)
    low_p, middle, high_q = public_box(n, integers)
    a, b, c, t = (source[k] for k in ("a", "b", "c", "t"))
    square = integers.mul(m, m)
    offset = integers.add(integers.mul(b, m),
        -integers.mul(integers.mul(2, a), j))
    low = integers.add(integers.add(integers.mul(a, low_p if a >= 0 else middle),
        integers.mul(t, middle)), offset)
    high = integers.add(integers.add(integers.mul(a, middle if a >= 0 else low_p),
        integers.mul(t, high_q)), offset)
    midpoint = integers.add(integers.add(low, high), square)
    shift = integers.divmod(midpoint, integers.mul(2, square))[0]
    return dict(source, source_row=source, shift=shift, sum_interval=[low, high],
        b=integers.add(b, -integers.mul(shift, m)),
        c=integers.add(c, -integers.mul(shift, j)),
        exponent=integers.add(source["exponent"], -integers.mul(shift, square)))


# Reuse the exact pinned N-only controller, including period setup, signed
# orientations, global-match recovery, product evaluation and saturation
# handling. Independent globals leave the frozen parent's behavior intact.
_parent_controller = PARENT["public_source"]
_centered_controller = types.FunctionType(_parent_controller.__code__,
    dict(_parent_controller.__globals__, public_row=centered_row,
        index_length=centered_length), "centered_controller",
    _parent_controller.__defaults__)


def centered_source(n, scaling=6, alpha=2):
    """N-only balanced prototype; all new arithmetic is inside its timer."""
    result = _centered_controller(n, scaling, alpha)
    result.update(variant="public-target-preserving-centering",
        retained_original_rows=result["constructed_rows"],
        frozen_controller_reused=True)
    return result


def reference_case(p, q, m):
    """Private factors select the correct row only in this reference check."""
    n, j, integers = p*q, p % m, IntegerLedger()
    if math.gcd(n, m) != 1:
        return None
    row = centered_row(n, m, j, integers)
    original = row["source_row"]
    a, b, c, t = (row[k] for k in ("a", "b", "c", "t"))
    x, square = p//m, m*m
    original_value = original["a"]*x*x+original["b"]*x+original["c"]
    assert original_value % p == 0
    original_index = original_value//p
    index = original_index-row["shift"]
    length = centered_length(n, m, integers)
    assert a*x*x+b*x+c == p*index
    assert square*c-j*m*b+j*j*a == n*t
    assert square*index == a*p+t*q+b*m-2*a*j
    assert abs(index) < length
    assert row["sum_interval"][0] <= square*original_index <= row["sum_interval"][1]
    assert p in PARENT["integer_roots"](n, m, row, index, integers)
    assert PARENT["integer_roots"](n, m, row, index, integers) == \
        PARENT["integer_roots"](n, m, original, original_index, integers)
    assert row["exponent"] == original["exponent"]-row["shift"]*square
    assert pow(2, row["exponent"] % (p-1), p) == pow(2, (square*index) % (p-1), p)
    gcd_controls = []
    for arbitrary in (0, original_index, original_index+1):
        old = (pow(2, original["exponent"], n)-pow(2, square*arbitrary, n)) % n
        new = (pow(2, row["exponent"], n)-pow(2, square*(arbitrary-row["shift"]), n)) % n
        phase = pow(2, -row["shift"]*square, n)
        assert new == phase*old % n and math.gcd(n, old) == math.gcd(n, new)
        gcd_controls.append(dict(original_index=arbitrary, gcd=math.gcd(n, old)))
    return dict(N=n, reference_p=p, reference_q=q, m=m, row=row,
        reference_original_index=original_index, reference_centered_index=index,
        centered_length=length, original_length=PARENT["index_length"](n, m, integers),
        recovered_candidates=PARENT["integer_roots"](n, m, row, index, integers),
        gcd_controls=gcd_controls, reference_constructor_metrics=integers.stats())


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeQuotientCentering.lean",
        "scripts/CheckSemiprimeQuotientCentering.lean", "scripts/probe_semiprime_quotient_centering.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import primerange
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources = source_inventory()
    assert _parent_controller.__globals__["public_row"] is PARENT["public_row"]
    assert _parent_controller.__globals__["index_length"] is PARENT["index_length"]
    rnd, primes = random.Random(REPLAY_ID), list(primerange(101, 5000))
    rounding_controls = 0
    for _ in range(4096):
        low, width, d = rnd.randint(-10**8, 10**8), rnd.randrange(10000), rnd.randint(1, 10000)
        high = low+width
        for value in (low, high, rnd.randint(low, high)):
            shift = (low+high+d)//(2*d)
            assert 2*abs(value-shift*d) <= width+d
            rounding_controls += 1
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    # Keep exactly the preceding 192 reference cases for coverage comparison.
    cases = [reference_case(c["reference_p"], c["reference_q"], c["m"]) for c in parent["cases"]]
    assert all(c is not None for c in cases)
    square_cases = []
    for p in primes[:32]:
        m = rnd.randint(2, 1000)
        if math.gcd(m, p) != 1:
            continue
        square_cases.append(reference_case(p, p, m))
    small_sources, outcomes = [], Counter()
    for case in cases[:128]:
        source = centered_source(case["N"])
        if source["factor"] is not None:
            assert source["factor"] in (case["reference_p"], case["reference_q"])
        outcomes[source["stage"]] += 1
        small_sources.append(source)
    controls = [reference_case(101, 103, 4),
        reference_case(1000000007, 1400000543, 1089),
        reference_case(1000000007, 1400000543, 4356)]
    n = 101*103
    old_signal = (pow(2, 10400, n)-1) % n
    new_signal = (pow(2, 10368, n)-pow(2, -32, n)) % n
    untransported = (pow(2, 10368, n)-1) % n
    assert math.gcd(n, old_signal) == math.gcd(n, new_signal) == 101
    assert math.gcd(n, untransported) == 1
    paired_sources = []
    for scaling in (6, 5):
        # Alternate order to avoid treating a shared import/cache as a result.
        if scaling == 6:
            baseline = PARENT["public_source"](1000000007*1400000543, scaling)
            new = centered_source(1000000007*1400000543, scaling)
        else:
            new = centered_source(1000000007*1400000543, scaling)
            baseline = PARENT["public_source"](1000000007*1400000543, scaling)
        assert baseline["factor"] in (1000000007, 1400000543)
        assert new["factor"] in (1000000007, 1400000543)
        paired_sources.append(dict(scaling=scaling, baseline=baseline, centered=new))
        print(json.dumps(dict(progress="paired-N-only-source", scaling=scaling,
            original_length=baseline["index_length"], centered_length=new["index_length"],
            baseline_ms=baseline["milliseconds"], centered_ms=new["milliseconds"],
            factor=new["factor"], stage=new["stage"])), flush=True)
    shapes = []
    for M in (2, 4, 8, 16, 32, 64):
        m = M*M
        fifth = centered_length(M**10, m, IntegerLedger())
        sixth = centered_length(M**12, m, IntegerLedger())
        assert fifth <= M*M+2 and sixth <= M**3+2
        shapes.append(dict(M=M, m=m, fifth_N=M**10, fifth_length=fifth,
            fifth_input_envelope=2*m+fifth, sixth_N=M**12, sixth_length=sixth,
            sixth_input_envelope=2*m+sixth))
    assert source_inventory() == sources, "source changed during replay"
    validation = dict(rounding_controls=rounding_controls, balanced_reference_rows=len(cases),
        prime_square_reference_rows=len(square_cases), small_public_sources=len(small_sources),
        small_public_outcomes=dict(outcomes), paired_public_sources=2*len(paired_sources),
        exact_controls=len(controls), shape_checks=len(shapes),
        residual_gcd_comparisons=3*(len(cases)+len(square_cases)+len(controls)),
        private_factors_used_only_as_references=True, frozen_parent_globals_unchanged=True)
    report = dict(replay_id=REPLAY_ID, source_sha256=sources,
        scope="Public target-preserving row centering and balanced collision coverage",
        one_sixth_guarantee="OPEN", is_complete_semiprime_factorizer=False,
        is_bit_complexity_certificate=False, is_formal_machine_refinement=False,
        exact_residual_gcd_preservation_lean=True, centered_balanced_coverage_lean=True,
        validation=validation, controls=controls, cases=cases, square_cases=square_cases,
        small_public_sources=small_sources, paired_public_sources=paired_sources, shape_checks=shapes,
        target_transport_control=dict(N=n, original_gcd=math.gcd(n, old_signal),
            centered_gcd=math.gcd(n, new_signal), untransported_gcd=math.gcd(n, untransported)),
        limitations="Lean proves the actual public shift, exact unit-phase residual GCD equality for every modulus, shifted recovery candidate equality, balanced index coverage and real hidden-field collision. Native source reuses the pinned public controller with independent globals and the new charged constructors. All centering arithmetic occurs inside each N-only source timer; no hidden factor, period or collision index enters that source. Original rows are retained in its packets. The complete arbitrary-ratio and saturated-local-period routes and full native/Boolean bit refinement remain open. Centering changes the explicit interval constant, not its sqrt(N)/m^(3/2) asymptotic size: fifth-root modulus has centeredLength <= M^2+2, while sixth-root modulus has an M^3+2 envelope for N <= M^12 and m=M^2. The perfect-power shape checks are parameter prices, not hard semiprime instances or general lower bounds. Paired timings are two runs on one common N, not a scaling exponent fit.")
    if args.output:
        args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources), validation=validation,
        controls=controls, paired_public_sources=paired_sources, shape_checks=shapes,
        one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()

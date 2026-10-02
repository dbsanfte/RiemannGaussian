#!/usr/bin/env python3
"""Exact Cartesian row batching and literal centre-curvature audit.

This is a detector/geometry replay, not a universal factoring algorithm.
Both timed implementations receive N and a public width, and rebuild all
input-specific powers. No hidden factor or local order enters the kernel.
The constant-centre grid is a model; literal sqrt centres are audited
separately and are never silently substituted by the model.
Optional research replay, outside ordinary builds and CI.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import statistics
import time

import gmpy2

ROOT = Path(__file__).resolve().parents[1]
LONG = runpy.run_path(str(ROOT / "scripts/probe_semiprime_long_period.py"))
MonicBatch = LONG["MonicBatch"]
SEED = 2026100487


def ceil_sqrt(n):
    s = math.isqrt(n)
    return s + (s*s < n)


def sixth_width(n):
    s = int(gmpy2.iroot(n, 6)[0])
    return s + (s**6 < n)


def root_lists(n, width):
    if n <= 1 or n % 2 == 0 or width < 1:
        raise ValueError("odd N>1 and positive public width required")
    # A common centre produces a genuinely Cartesian quotient grid.
    # It is deliberately labelled a model, not the literal sqrt centre.
    # One known primitive corner calibrates the centre. The rest of the
    # Cartesian completion still has different literal centres.
    owner = max(1, width-1)
    centre = ceil_sqrt(4*n*owner*width)
    axis = int(gmpy2.powmod(2, n, n))
    inverse = pow(2, -1, n)
    target = int(gmpy2.powmod(2, centre, n))
    roots, points = [], []
    value = 1
    for _ in range(width):
        value = value*axis % n
        target = target*inverse % n
        roots.append(value)
        points.append(target)
    return roots, points, {"centre": centre, "calibrating_weights": [owner, width],
        "setup_integer_square_roots": 1, "setup_powers": 2,
        "setup_exponent_bits": n.bit_length()+centre.bit_length(),
        "setup_inversions": 1, "axis_updates": 2*width,
        "input_residues": 2*width, "represented_pairs": width*width,
        "literal_centres": False}


def cartesian_product(n, width, method):
    roots, points, stats = root_lists(n, width)
    value = 1
    if method == "explicit":
        for x in roots:
            for y in points:
                value = value*(x-y) % n
        stats["pair_products"] = width*width
        stats["materialized_pair_list"] = 0
    elif method == "implicit":
        batch = MonicBatch(n)
        node = batch.tree(roots)
        values = batch.evaluate(node[0], points)
        for v in values:
            value = value*v % n
        # Evaluating P_x at y computes the resultant in the opposite order.
        # Retain the exact signed identity, not just its invariant GCD.
        if width % 2:
            value = (-value) % n
        stats.update(batch.stats())
        stats["pair_products"] = 0
        stats["point_products"] = width
        stats["materialized_pair_list"] = 0
        stats["resultant_sign_negations"] = width % 2
    else:
        raise ValueError("unknown method")
    stats["gcd_calls"] = 1
    return value, math.gcd(value, n), stats


def detector_regression():
    checked = 0
    normalized = 0
    for n in (35, 77, 143, 221, 323, 437, 899, 1009):
        for width in range(1, 17):
            explicit = cartesian_product(n, width, "explicit")
            implicit = cartesian_product(n, width, "implicit")
            assert explicit[:2] == implicit[:2]
            roots, points, _ = root_lists(n, width)
            # The unit normalisation retains every target-one row hit.
            original = 1
            for x in roots:
                for y in points:
                    original = original*(x*pow(y, -1, n)-1) % n
                    normalized += 1
            units = math.prod(points) % n
            assert original*pow(units, width, n) % n == explicit[0]
            assert math.gcd(original, n) == explicit[1]
            checked += 1
    return {"exact_composite_ring_batches": checked,
            "normalized_pair_checks": normalized}


def labelled_inputs():
    rnd = random.Random(SEED)
    cases = []
    for bits in (32, 40, 48, 64, 80):
        lo, hi = 1 << (bits//2-1), 1 << (bits//2)
        while True:
            p = int(gmpy2.next_prime(rnd.randrange(lo, hi)))
            q = int(gmpy2.next_prime(rnd.randrange(lo, hi)))
            if p != q and (p*q).bit_length() == bits:
                break
        cases.append({"kind": "fresh", "n": p*q,
                      "bits": bits, "reference_primes": sorted((p, q))})
    p, q = 661911275027, 720957498683
    cases.append({"kind": "saved-four-rough", "n": p*q,
                  "bits": (p*q).bit_length(), "reference_primes": [p, q]})
    return cases


def curvature_probe(n):
    B = sixth_width(n)
    for a in range(max(1, 3*B//4), min(B-1, 3*B//4+40)):
        for b in range(max(a+2, 7*B//8), min(B-1, 7*B//8+40)):
            corners = ((a, b), (a, b+2), (a+2, b), (a+2, b+2))
            if any(math.gcd(x, y) != 1 or not x <= y <= 2*x
                   or x*y > B*B for x, y in corners):
                continue
            centres = [ceil_sqrt(4*n*x*y) for x, y in corners]
            for (x, y), c in zip(corners, centres):
                assert (c-1)**2 < 4*n*x*y <= c*c
            defect = centres[0]+centres[3]-centres[1]-centres[2]
            # The proof gives defect > 2*sqrt(N)/B-2 for step two.
            lower = Fraction(2*math.isqrt(n), B)-2
            assert defect > lower
            width = (defect+1)//2
            return {"sixth_budget": B, "step": 2, "corners": corners,
                "centres": centres, "mixed_defect": defect,
                "integer_correction_width_at_least": width,
                "width_over_sixth_budget": width/B,
                "rational_defect_lower": [lower.numerator, lower.denominator],
                "primitive_balanced_support": True}
    raise AssertionError("no audited primitive four-corner block")


def flattening_regression():
    n = 77
    corners = ((8, 11), (8, 13), (10, 11), (10, 13))
    centres = [ceil_sqrt(4*n*x*y) for x, y in corners]
    assert centres == [165, 179, 185, 201]
    assert all(math.gcd(x, y) == 1 and x <= y <= 2*x for x, y in corners)
    predicted = centres[1]+centres[2]-centres[0]
    original = pow(2, 10*n+13-centres[3], n)
    flattened = pow(2, 10*n+13-predicted, n)
    assert (predicted, original, flattened) == (199, 15, 60)
    assert math.gcd(original-1, n) == 7 and math.gcd(flattened-1, n) == 1
    return {"n": n, "corners": corners, "centres": centres,
        "predicted_last_centre": predicted, "anchors": [original, flattened],
        "original_gcd": 7, "flattened_gcd": 1,
        "sixth_budget_recovery": False,
        "scope": "primitive-row identity counterexample, not a factoring benchmark"}


def coherent_batch_regression():
    # The public calibrated centre is 25. Both hidden prime components
    # hit, so the aggregate GCD is 77 and a proper leaf must be retained.
    n, width = 77, 2
    value, gcd, _ = cartesian_product(n, width, "implicit")
    assert value == 0 and gcd == 77
    roots, points, _ = root_lists(n, width)
    probes = 0
    for i, x in enumerate(roots):
        for j, y in enumerate(points):
            probes += 1
            signal = (x-y) % n
            g = math.gcd(signal, n)
            if 1 < g < n:
                return {"n": n, "width": width, "aggregate_gcd": gcd,
                    "proper_leaf_gcd": g, "signal": signal,
                    "weights": [i+1, j+1], "recovery_gcds": probes,
                    "scope": "small coherent-batch regression, not a universal recovery budget"}
    raise AssertionError("lost the original proper factor hit")


def replay(repeats=3):
    cases = labelled_inputs()
    rng = random.Random(SEED+1)
    regression = detector_regression()
    results = []
    # Warm imported polynomial paths only, not any input-specific cache.
    cartesian_product(323, 16, "implicit")
    for case in cases:
        n = case["n"]
        case["curvature"] = curvature_probe(n)
        widths = (32,) if case["bits"] < 48 else ((64, 128) if case["bits"] < 64
            else ((128, 256, 512) if case["bits"] < 79
                  else (256, 512, 1024, 2048, 4096)))
        for width in widths:
            assert width <= sixth_width(n)
            timings = {"explicit": [], "implicit": []}
            metrics = {}
            reference = None
            for _ in range(repeats):
                order = ["explicit", "implicit"]
                rng.shuffle(order)
                for method in order:
                    start = time.perf_counter()
                    value, gcd, stats = cartesian_product(n, width, method)
                    timings[method].append(1000*(time.perf_counter()-start))
                    metrics[method] = stats
                    if reference is None:
                        reference = value, gcd
                    assert reference == (value, gcd)
            results.append({"n": n, "bits": case["bits"], "width": width,
                "kind": case["kind"], "value": reference[0], "gcd": reference[1],
                "elapsed_ms": timings, "metrics": metrics,
                "median_speedup": statistics.median(timings["explicit"])/
                    statistics.median(timings["implicit"])})
    paths = ("scripts/probe_semiprime_cartesian_completion.py",
        "scripts/probe_semiprime_long_period.py", "scripts/probe_semiprime_weighted_batch.py",
        "RiemannGaussian/SemiprimeCartesianCompletion.lean")
    return {"status": "Cartesian detector checked; literal centre transport is unresolved",
        "universal_sixth_root_factorisation_proved": False,
        "seed": SEED, "repeats": repeats,
        "timing_scope": "complete constant-centre detector including root lists and GCD; not factoring",
        "reference_label_usage": "generation and descriptive labels only; no hidden input to detector",
        "inputs": cases, "benchmarks": results, "regression": regression,
        "flattening_regression": flattening_regression(),
        "coherent_batch_regression": coherent_batch_regression(),
        "source_sha256": {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths},
        "gmpy2_version": gmpy2.version()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("positive repeats required")
    result = replay(args.repeats)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": result["status"], "regression": result["regression"],
        "benchmarks": [{"bits": b["bits"], "width": b["width"],
            "speedup": b["median_speedup"]} for b in result["benchmarks"]],
        "curvature": [{"bits": c["bits"], **c["curvature"]} for c in result["inputs"]]}))


if __name__ == "__main__":
    main()

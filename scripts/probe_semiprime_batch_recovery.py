#!/usr/bin/env python3
"""Off-diagonal collision recovery with exact shared-root deflation.

Optional research replay, outside ordinary builds and CI. This completes
recovery for supplied residue lists, not universal one-sixth factorisation.
The literal-row replay retains every integer square-root centre and charges
its construction. Its anchor list still has a quadratic weight count.
"""
from __future__ import annotations

import argparse
import hashlib
from itertools import combinations
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
SEED = 202610020619


def distinct_residues(n, values):
    """Deterministic sorting, retaining the first original witness index."""
    ordered = sorted((int(value) % n, i) for i, value in enumerate(values))
    residues, indices = [], []
    for value, i in ordered:
        if not residues or residues[-1] != value:
            residues.append(value)
            indices.append(i)
    return residues, indices


def recovery(n, roots, points, method="implicit", include_signals=False):
    if n <= 1:
        raise ValueError("modulus greater than one required")
    xs, root_indices = distinct_residues(n, roots)
    ys, point_indices = distinct_residues(n, points)
    stats = {"input_roots": len(roots), "input_points": len(points),
             "distinct_roots": len(xs), "distinct_points": len(ys),
             "represented_input_pairs": len(roots)*len(points),
             "column_gcds": 0, "leaf_gcds": 0, "witness_remainders": 0,
             "pair_products": 0, "derivative_coefficients": 0,
             "recovery_pair_differences": 0, "whole_modulus_columns": 0}
    shared, ordinary = [], []
    i = 0
    for j, y in enumerate(ys):
        while i < len(xs) and xs[i] < y:
            i += 1
        (shared if i < len(xs) and xs[i] == y else ordinary).append(j)
    stats["shared_points"] = len(shared)
    stats["off_diagonal_pairs"] = len(xs)*len(ys)-len(shared)
    values = [1] * len(ys)
    if method == "explicit":
        for j, y in enumerate(ys):
            for x in xs:
                if x != y:
                    values[j] = values[j]*(y-x) % n
                    stats["pair_products"] += 1
    elif method == "implicit":
        batch = MonicBatch(n)
        polynomial = batch.tree(xs)[0]
        for j, value in zip(ordinary,
                            batch.evaluate(polynomial, [ys[j] for j in ordinary])):
            values[j] = value
        if shared:
            derivative = [(i*polynomial[i]) % n for i in range(1, len(polynomial))]
            stats["derivative_coefficients"] = len(derivative)
            for j, value in zip(shared,
                                batch.evaluate(derivative, [ys[j] for j in shared])):
                values[j] = value
        stats.update(batch.stats())
    else:
        raise ValueError("unknown evaluation method")

    result = {"status": "no-proper-collision", "factor": None}
    for j, (y, value) in enumerate(zip(ys, values)):
        stats["column_gcds"] += 1
        divisor = math.gcd(value, n)
        if divisor == 1:
            continue
        if divisor == n:
            stats["whole_modulus_columns"] += 1
            # Every exact shared root has already been removed. Each
            # remaining difference is nonzero modulo N, so a nonunit
            # product must have a proper-divisor leaf. This scan occurs
            # at most once, and never enumerates the full pair grid.
            for i, x in enumerate(xs):
                if x == y:
                    continue
                stats["recovery_pair_differences"] += 1
                stats["leaf_gcds"] += 1
                divisor = math.gcd((y-x) % n, n)
                if 1 < divisor < n:
                    break
            else:
                raise AssertionError("nonunit deflated product has no proper leaf")
        else:
            for i, x in enumerate(xs):
                if x == y:
                    continue
                stats["recovery_pair_differences"] += 1
                stats["witness_remainders"] += 1
                if (y-x) % divisor == 0:
                    break
            else:
                raise AssertionError("proper column GCD has no witness")
        assert 1 < divisor < n and n % divisor == 0
        result = {"status": "factor", "factor": divisor,
                  "root_index": root_indices[i], "point_index": point_indices[j],
                  "root": xs[i], "point": y, "column_value": value,
                  "stage": "leaf" if value == 0 else "column"}
        break
    stats["gcd_calls"] = stats["column_gcds"]+stats["leaf_gcds"]
    stats["gcd_bound"] = len(xs)+len(ys)
    assert stats["gcd_calls"] <= stats["gcd_bound"]
    assert stats["whole_modulus_columns"] <= 1
    result["metrics"] = stats
    if include_signals:
        result["signals"] = values
        result["ordered_roots"] = xs
        result["ordered_points"] = ys
    return result


def oracle(n, roots, points):
    """Independent exhaustive definition of a proper pair collision."""
    return any(1 < math.gcd(int(y)-int(x), n) < n for x in roots for y in points)


def validate():
    rnd = random.Random(SEED)
    checked = 0
    bounds = 0
    for n in (4, 6, 9):
        subsets = [list(s) for width in range(3)
                   for s in combinations(range(n), width)]
        for xs in subsets:
            for ys in subsets:
                explicit = recovery(n, xs, ys, "explicit", True)
                implicit = recovery(n, xs, ys, "implicit", True)
                assert explicit["signals"] == implicit["signals"]
                assert (implicit["factor"] is not None) == oracle(n, xs, ys)
                assert explicit["factor"] == implicit["factor"]
                checked += 1
                bounds += implicit["metrics"]["gcd_calls"]
    for _ in range(2048):
        n = rnd.choice((10, 15, 21, 25, 35, 49, 77, 143, 221, 323, 1009))
        xs = [rnd.randrange(-n, 2*n) for _ in range(rnd.randrange(25))]
        ys = [rnd.randrange(-n, 2*n) for _ in range(rnd.randrange(25))]
        explicit = recovery(n, xs, ys, "explicit", True)
        implicit = recovery(n, xs, ys, "implicit", True)
        assert explicit["signals"] == implicit["signals"]
        assert (implicit["factor"] is not None) == oracle(n, xs, ys)
        assert explicit["factor"] == implicit["factor"]
        checked += 1
        bounds += implicit["metrics"]["gcd_calls"]
    controls = [
        {"kind": "shared-root-before-later-hit", "n": 35,
         "roots": [1], "points": [1, 6], "expected_factor": 5},
        {"kind": "full-modulus-deflated-column", "n": 35,
         "roots": [1, 11, 15], "points": [1], "expected_factor": 5},
        {"kind": "repeated-global-root", "n": 35,
         "roots": [1, 1, 6], "points": [1, 1], "expected_factor": 5},
        {"kind": "only-global-equalities", "n": 77,
         "roots": [1]*128, "points": [1]*128, "expected_factor": None},
        {"kind": "prime-square-proper-hit", "n": 49,
         "roots": [1, 8, 1], "points": [1], "expected_factor": 7},
    ]
    for c in controls:
        c["result"] = recovery(c["n"], c["roots"], c["points"], include_signals=True)
        assert c["result"]["factor"] == c["expected_factor"]
    return {"exact_batches": checked, "summed_gcd_calls": bounds, "controls": controls}


def ceil_sqrt(n):
    s = math.isqrt(n)
    return s+(s*s < n)


def sixth_width(n):
    s = int(gmpy2.iroot(n, 6)[0])
    return s+(s**6 < n)


def candidate_pair_count(width):
    half = width//2
    return half*half+2*half+(half+1)*(width % 2)


def labelled_inputs():
    rnd = random.Random(SEED+1)
    cases = []
    for bits in (32, 40, 48, 64, 80):
        lo, hi = 1 << (bits//2-1), 1 << (bits//2)
        while True:
            p = int(gmpy2.next_prime(rnd.randrange(lo, hi)))
            q = int(gmpy2.next_prime(rnd.randrange(lo, hi)))
            if p != q and (p*q).bit_length() == bits:
                break
        cases.append({"kind": "fresh", "n": p*q, "bits": bits,
                      "reference_primes": sorted((p, q))})
    p, q = 661911275027, 720957498683
    cases.append({"kind": "saved-four-rough", "n": p*q,
                  "bits": (p*q).bit_length(), "reference_primes": [p, q]})
    return cases


def literal_roots(n, weight_width, baby_width):
    """Public-input construction of the actual coupled weighted anchors."""
    if n <= 1 or n % 2 == 0:
        raise ValueError("odd modulus greater than one required")
    anchors, weights = [], []
    square_roots = exponent_bits = weight_pairs = 0
    for a in range(1, weight_width+1):
        for b in range(a, min(2*a, weight_width)+1):
            weight_pairs += 1
            if math.gcd(a, b) != 1:
                continue
            c = ceil_sqrt(4*n*a*b)
            square_roots += 1
            e = a*n+b-c
            assert e >= 0 and (c-1)**2 < 4*n*a*b <= c*c
            anchors.append(int(gmpy2.powmod(2, e, n)))
            weights.append([a, b, c])
            exponent_bits += e.bit_length()
    points, v = [], 1
    for _ in range(baby_width):
        points.append(v)
        v = v*2 % n
    assert weight_pairs == candidate_pair_count(weight_width)
    assert weight_pairs >= (weight_width//4)**2
    return anchors, points, weights, {
        "literal_centres": True, "integer_square_roots": square_roots,
        "candidate_weight_pairs": weight_pairs, "weight_coprimality_gcds": weight_pairs,
        "anchor_powers": len(anchors), "anchor_exponent_bits": exponent_bits,
        "baby_updates": baby_width, "weight_width": weight_width,
        "baby_width": baby_width, "sixth_budget": sixth_width(n),
        "full_box_candidate_pairs_formula": candidate_pair_count(sixth_width(n)),
        "full_box_pair_lower_bound": (sixth_width(n)//4)**2,
        "full_sixth_weight_box": weight_width == sixth_width(n),
        "full_sixth_baby_interval": baby_width == sixth_width(n)}


def literal_factor(n, weight_width, baby_width, method):
    roots, points, weights, construction = literal_roots(n, weight_width, baby_width)
    result = recovery(n, roots, points, method)
    result["construction"] = construction
    if result["factor"] is not None:
        result["weighted_witness"] = weights[result["root_index"]]
    return result


def replay(repeats=3):
    regression = validate()
    rnd = random.Random(SEED+2)
    cases = labelled_inputs()
    benchmarks = []
    # Every timed call rebuilds its polynomial, derivative, and remainder trees.
    recovery(323, list(range(32)), list(range(32)))
    for case in (cases[0], cases[-2], cases[-1]):
        n = case["n"]
        for width in (128, 512, 1024, 2048):
            roots, points = list(range(width)), list(range(width))
            times = {"explicit": [], "implicit": []}
            results = {}
            for _ in range(repeats):
                methods = ["explicit", "implicit"]
                rnd.shuffle(methods)
                for method in methods:
                    start = time.perf_counter()
                    result = recovery(n, roots, points, method)
                    times[method].append(1000*(time.perf_counter()-start))
                    results[method] = result
                assert results["explicit"]["factor"] == results["implicit"]["factor"]
            benchmarks.append({"kind": "all-points-shared", "n": n,
                "bits": case["bits"], "width": width, "elapsed_ms": times,
                "median_speedup": statistics.median(times["explicit"])/
                    statistics.median(times["implicit"]), "results": results,
                "public_construction": "consecutive residues 0 through width-1"})
    literal = []
    for case in cases:
        n = case["n"]
        width = min(sixth_width(n), 128)
        times = {"explicit": [], "implicit": []}
        results = {}
        for _ in range(repeats):
            methods = ["explicit", "implicit"]
            rnd.shuffle(methods)
            for method in methods:
                start = time.perf_counter()
                result = literal_factor(n, width, width, method)
                times[method].append(1000*(time.perf_counter()-start))
                results[method] = result
            assert results["explicit"]["factor"] == results["implicit"]["factor"]
        literal.append({**case, "elapsed_ms": times, "results": results,
                        "median_speedup": statistics.median(times["explicit"])/
                            statistics.median(times["implicit"])})
    paths = ("scripts/probe_semiprime_batch_recovery.py",
             "scripts/probe_semiprime_long_period.py",
             "scripts/probe_semiprime_weighted_batch.py",
             "scripts/probe_semiprime_quadratic_extraction.py",
             "scripts/probe_semiprime_single_extraction.py",
             "RiemannGaussian/SemiprimeCartesianCompletion.lean",
             "RiemannGaussian/SemiprimeRoughProjection.lean")
    return {"seed": SEED, "repeats": repeats,
            "scope": "recovery for supplied roots; no universal one-sixth coverage or construction bound",
            "arithmetic": "exact integer residues and integer square roots; no floating-point centres",
            "ordering": "deterministic sort/dedup and merge; no hash-table complexity assumption",
            "regression": regression, "inputs": cases,
            "shared_root_benchmarks": benchmarks, "literal_row_replay": literal,
            "source_hashes": {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--validate-only", action="store_true")
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("repeats must be positive")
    result = validate() if args.validate_only else replay(args.repeats)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"exact_batches": (result if args.validate_only else result["regression"])["exact_batches"],
                      "output": str(args.output) if args.output else None,
                      "universal_sixth_guarantee": False}))


if __name__ == "__main__":
    main()

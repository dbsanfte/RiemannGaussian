#!/usr/bin/env python3
"""Optional exact replay of the universal literal-centre arithmetic cover.

The factoring kernel takes only N, uses every k from 1 through B² when
needed, and keeps the exact integer square-root centres. It streams rows
and uses the previously saved polynomial prefix; the Lean specification
materializes its candidate list and specifies the prefix by its product.
This replay checks arithmetic agreement, not the Lean implementation's
runtime or a one-sixth bit-operation bound. Reference primes occur only
in corpus generation and untimed validation.
"""
from __future__ import annotations

import argparse
from collections import Counter
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
GROUP = runpy.run_path(str(ROOT / "scripts/probe_semiprime_group_coverage.py"))
SEED = 202610021613


def sixth_width(n):
    root = int(gmpy2.iroot(n, 6)[0])
    return root + (root**6 < n)


def ceil_sqrt(n):
    root = math.isqrt(n)
    return root + (root*root < n)


def full_candidate_count(b):
    """Exact grouped sum of B/isqrt(k)+1 for 1<=k<=B².

    The interval m²..(m+1)²-1 has 2m+1 terms; the last row is B².
    Computing this diagnostic does not enumerate or construct the rows.
    """
    if b == 0:
        return 0
    return sum((2*m+1)*(b//m+1) for m in range(1, b)) + 2


def recover(n):
    """Public arithmetic baseline with a complete, uncapped candidate cover."""
    if n < 4:
        raise ValueError("semiprime input N>=4 required")
    start = time.perf_counter()
    b = sixth_width(n)
    counts = {
        "sixth_root_calls": 1, "square_input_root_calls": 0,
        "trial_gcds": 0, "weight_product_rows_visited": 0,
        "centre_square_roots": 0, "weight_product_square_roots": 0,
        "candidate_discriminants": 0, "discriminant_square_roots": 0,
        "square_discriminant_gcds": 0,
    }
    prefix_result = None

    def result(factor, stage, witness=None):
        assert 1 < factor < n and n % factor == 0
        return {"factor": factor, "stage": stage, "width": b,
                "counts": counts, "prefix": prefix_result,
                "weighted_witness": witness,
                "elapsed_ms": 1000*(time.perf_counter()-start)}

    if b < 4:
        for candidate in range(n):
            counts["trial_gcds"] += 1
            factor = math.gcd(n, candidate)
            if 1 < factor < n:
                return result(factor, "finite-small-input")
        raise AssertionError("input not semiprime or small-input scan failed")

    counts["square_input_root_calls"] += 1
    root = math.isqrt(n)
    if root*root == n:
        return result(root, "square")

    prefix_result = GROUP["prefix"](n, b)
    if prefix_result["factor"] is not None:
        return result(int(prefix_result["factor"]), "quadratic-prefix")
    # In this complement the Lean theorem supplies a true weighted sum in
    # this public list. Nothing about a hidden prime is consulted here.
    for k in range(1, b*b+1):
        counts["weight_product_rows_visited"] += 1
        centre = ceil_sqrt(4*k*n)
        counts["centre_square_roots"] += 1
        counts["weight_product_square_roots"] += 1
        width = b//math.isqrt(k)+1
        for offset in range(width):
            s = centre+offset
            d = s*s-4*k*n
            assert d >= 0
            counts["candidate_discriminants"] += 1
            counts["discriminant_square_roots"] += 1
            r = math.isqrt(d)
            if r*r != d:
                continue
            counts["square_discriminant_gcds"] += 1
            factor = math.gcd(n, (s+r)//2)
            if 1 < factor < n:
                return result(factor, "literal-weighted-cover",
                              {"k": k, "centre": centre, "offset": offset,
                               "sum": s, "discriminant_root": r,
                               "quadratic_root": (s+r)//2})
    raise AssertionError("complete arithmetic cover exhausted on purported semiprime")


def validate():
    """Finite reference checks, distinct from the universal Lean proof."""
    for b in range(65):
        explicit = sum(b//math.isqrt(k)+1 for k in range(1, b*b+1))
        assert full_candidate_count(b) == explicit >= b*b
    # Complete small prime-pair corpus includes squares, even inputs,
    # both sides of B=4 and several sharp square-root/width boundaries.
    primes = [n for n in range(2, 102) if gmpy2.is_prime(n)]
    stages = Counter()
    checked = 0
    for index, p in enumerate(primes):
        for q in primes[index:]:
            n = p*q
            result = recover(n)
            assert result["factor"] in (p, q)
            b = result["width"]
            assert (b-1)**6 < n <= b**6
            assert result["counts"]["candidate_discriminants"] <= full_candidate_count(b)
            if result["prefix"] is not None:
                # Independent integer-product oracle, outside recovery.
                gcd = math.gcd(n, math.factorial(b*b))
                assert ((gcd == 1) == (result["prefix"]["factor"] is None))
            stages[result["stage"]] += 1
            checked += 1
    return {"small_semiprimes": checked, "prime_limit": 101,
            "candidate_count_widths": 65, "stages": dict(stages),
            "oracle_scope": "reference factors and factorial used only outside recovery"}


def inputs():
    rng = random.Random(SEED)
    out = []
    for bits in (32, 40, 48):
        lo, hi = 1 << (bits//2-1), 1 << (bits//2)
        for index in range(4):
            while True:
                p = int(gmpy2.next_prime(rng.randrange(lo, hi)))
                q = int(gmpy2.next_prime(rng.randrange(lo, hi)))
                if p != q and (p*q).bit_length() == bits:
                    break
            out.append({"kind": "fresh-balanced", "index": index,
                        "n": p*q, "bits": bits, "reference_primes": sorted((p, q))})
    for p, q, kind in ((248909, 249521, "saved-curve-menu-control"),
                       (203653, 230003, "saved-separated-control"),
                       (7, 2147483647, "unbalanced"),
                       (65537, 65537, "prime-square")):
        out.append({"kind": kind, "n": p*q, "bits": (p*q).bit_length(),
                    "reference_primes": [p, q]})
    return out


def audit(repeats):
    regression = validate()
    rows = []
    recover(323)
    for case in inputs():
        results = [recover(case["n"]) for _ in range(repeats)]
        for result in results:
            assert result["factor"] in case["reference_primes"]
        first = results[0]
        assert all(result["counts"] == first["counts"] for result in results)
        b = first["width"]
        rows.append({**case, "result": first,
                     "elapsed_ms": [result["elapsed_ms"] for result in results],
                     "median_ms": statistics.median(result["elapsed_ms"] for result in results),
                     "explicit_lean_list_entries": full_candidate_count(b),
                     "explicit_lean_list_lower_bound": b*b,
                     "full_cover_rows": b*b})
    # Counts for large inputs are diagnostics from the public budget only.
    # These inputs are deliberately not reported as timed factoring runs.
    costs = []
    for bits in (32, 40, 48, 64, 80, 96):
        n = (1 << bits)-1
        b = sixth_width(n)
        costs.append({"public_n": n, "bits": bits, "width": b,
                      "full_cover_rows": b*b,
                      "explicit_candidate_list_entries": full_candidate_count(b)})
    paths = ("scripts/probe_semiprime_lehman_coverage.py",
             "scripts/probe_semiprime_group_coverage.py",
             "scripts/probe_semiprime_group_selection.py",
             "scripts/probe_semiprime_long_period.py",
             "scripts/probe_semiprime_weighted_batch.py",
             "scripts/probe_semiprime_quadratic_extraction.py",
             "scripts/probe_semiprime_single_extraction.py",
             "RiemannGaussian/SemiprimeLehmanCoverage.lean",
             "RiemannGaussian/SemiprimeGroupCoverage.lean",
             "scripts/CheckSemiprimeLehmanCoverage.lean")
    return {"seed": SEED, "repeats": repeats,
            "scope": "exact arithmetic replay of a complete classical cover; no one-sixth bit bound",
            "kernel_inputs": "N only; no factor ratio, order, curve or private weight",
            "implementation_difference": "Python streams rows and uses a polynomial-tree prefix; Lean specifies the full candidate list and prefix product",
            "timing_scope": "all public width setup, square checks, prefix construction/evaluation, visited centres and discriminants",
            "construction_scope": "full materialized Lean list size charged separately even if Python returns early",
            "regression": regression, "factoring_replay": rows,
            "public_cover_costs_without_factoring": costs,
            "source_hashes": {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--validate-only", action="store_true")
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("repeats must be positive")
    result = validate() if args.validate_only else audit(args.repeats)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    regression = result if args.validate_only else result["regression"]
    print(json.dumps({"small_semiprimes": regression["small_semiprimes"],
                      "replay_inputs": 0 if args.validate_only else len(result["factoring_replay"]),
                      "output": str(args.output) if args.output else None,
                      "universal_sixth_bit_bound": False}))


if __name__ == "__main__":
    main()

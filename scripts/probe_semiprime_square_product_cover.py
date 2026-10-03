#!/usr/bin/env python3
"""Exact coverage diagnostic for short square-class centre caches.

Public centre/weight construction takes N and a fixed class menu. The
coverage oracle then uses labelled reference primes: this is deliberately
NOT a public factoring algorithm or factoring benchmark. It tests whether
the smaller family can inherit the universal literal-window theorem.
All centres, offsets and strict window boundaries use integer arithmetic.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import math
from pathlib import Path
import random

import gmpy2
from sympy import isprime

ROOT = Path(__file__).resolve().parents[1]
SEED = 202610021622
CONTROL_PRIMES = (46337, 65521)
WIDE_CONTROL_PRIMES = (13309, 15767)
WIDE_SEARCH_SEED = 202610021623


def sixth_width(n):
    root = int(gmpy2.iroot(n, 6)[0])
    return root + (root**6 < n)


def ceil_sqrt(n):
    root = math.isqrt(n)
    return root + (root*root < n)


def squarefree_classes(limit):
    return [d for d in range(1, limit+1)
            if all(d % (ell*ell) for ell in range(2, math.isqrt(d)+1))]


@dataclass
class ClassCache:
    d: int
    maximum_index: int
    centres: list[int]
    splits: list[tuple[int, int]]


def construct(n, class_limit):
    """Complete public cache; construction uses no private factor labels."""
    if n < 1 or class_limit < 1:
        raise ValueError("positive N and class limit required")
    b = sixth_width(n)
    caches = []
    square_roots = split_tests = 0
    for d in squarefree_classes(class_limit):
        maximum = math.isqrt((b*b)//d)
        assert d*maximum*maximum <= b*b < d*(maximum+1)**2
        centres = [ceil_sqrt(4*n*d*m*m) for m in range(1, maximum+1)]
        square_roots += maximum
        splits = []
        for da in range(1, d+1):
            split_tests += 1
            if d % da == 0:
                splits.append((da, d//da))
        caches.append(ClassCache(d, maximum, centres, splits))
    return b, caches, {"sixth_root_calls": 1,
                       "class_width_square_roots": len(caches),
                       "literal_centre_square_roots": square_roots,
                       "class_split_divisibility_tests": split_tests,
                       "class_limit": class_limit,
                       "classes": [c.d for c in caches]}


def public_rows(cache):
    """Every generated row and its centre come from public integers.

    (a,b)=(h*da*u²,h*db*v²), with da*db=d and h*u*v<=maximum.
    Duplicates are retained, so every constructed representation is charged.
    """
    for da, db in cache.splits:
        for h in range(1, cache.maximum_index+1):
            for u in range(1, cache.maximum_index//h+1):
                for v in range(1, cache.maximum_index//(h*u)+1):
                    m = h*u*v
                    a, b = h*da*u*u, h*db*v*v
                    yield a, b, m, cache.centres[m-1], (da, db, h, u, v)


def representation_count(maximum):
    return sum(maximum//(h*u) for h in range(1, maximum+1)
               for u in range(1, maximum//h+1))


def public_discriminant_control(n, b, class_limit, wide):
    """Replay the exact finite public candidate list certified by Lean.

    This also visits non-squarefree d; duplicate products are retained.
    Its exhaustive list is a correctness diagnostic, not the proposed
    fast modular batching kernel or a one-sixth factoring algorithm.
    """
    centre_roots = candidate_roots = square_discriminants = proper_factors = 0
    for d in range(1, class_limit+1):
        for m in range(1, math.isqrt(b*b//d)+1):
            k = d*m*m
            centre = ceil_sqrt(4*n*k)
            centre_roots += 1
            width = b if wide else b//(4*m)+1
            for offset in range(width):
                s = centre+offset
                discr = s*s-4*k*n
                root = math.isqrt(discr)
                candidate_roots += 1
                if root*root == discr:
                    square_discriminants += 1
                    factor = math.gcd(n, (s+root)//2)
                    proper_factors += 1 < factor < n
    return {"public_n": n, "width": b, "all_classes_through": class_limit,
            "window": "all_offsets_below_B" if wide else "padded_sharp_width",
            "centre_square_roots": centre_roots,
            "candidate_discriminant_square_roots": candidate_roots,
            "square_discriminants": square_discriminants,
            "proper_factors": proper_factors}


def diagnose(p, q, class_limit):
    """Labelled reference oracle; p and q are not factoring-kernel inputs."""
    p, q = sorted((p, q))
    n = p*q
    b, caches, counts = construct(n, class_limit)
    minimum = None
    wide_hits = sharp_hits = rows = 0
    first_wide = first_sharp = None
    per_class = []
    for cache in caches:
        class_rows = class_wide = class_sharp = 0
        for a, bw, m, centre, representation in public_rows(cache):
            k = a*bw
            assert k == cache.d*m*m and k <= b*b
            offset = a*q+bw*p-centre
            assert offset >= 0
            rows += 1
            class_rows += 1
            candidate = (offset, cache.d, a, bw, m, centre, representation)
            if minimum is None or candidate < minimum:
                minimum = candidate
            wide = offset < b
            # Strict sharp bound offset < B/(4*m*sqrt(d)), squared with
            # both sides nonnegative. There is no floating-point sqrt.
            sharp = (4*m*offset)**2*cache.d < b*b
            if wide:
                wide_hits += 1
                class_wide += 1
                if first_wide is None:
                    first_wide = candidate
            if sharp:
                sharp_hits += 1
                class_sharp += 1
                if first_sharp is None:
                    first_sharp = candidate
        expected = len(cache.splits)*representation_count(cache.maximum_index)
        assert class_rows == expected
        per_class.append({"d": cache.d, "maximum_centre_index": cache.maximum_index,
                          "centre_entries": len(cache.centres),
                          "weight_representations": class_rows,
                          "wide_literal_hits": class_wide,
                          "sharp_literal_hits": class_sharp})
    counts["weight_representations"] = rows
    counts["reference_weighted_sum_tests"] = rows
    counts["reference_sharp_boundary_tests"] = rows

    def witness(candidate):
        if candidate is None:
            return None
        offset, d, a, bw, m, centre, representation = candidate
        s = centre+offset
        discr = s*s-4*a*bw*n
        root = math.isqrt(discr)
        assert root*root == discr
        factor = math.gcd(n, (s+root)//2)
        if p != q and b*b < p:
            assert factor in (p, q)
        return {"offset": offset, "class": d, "a": a, "b": bw,
                "product": a*bw, "centre_index": m, "centre": centre,
                "representation": list(representation),
                "discriminant_root": root, "reference_factor": factor}

    return {"n": n, "bits": n.bit_length(), "width": b,
            "reference_primes": [p, q], "prefix_complement": b*b < p,
            "class_limit": class_limit, "counts": counts,
            "wide_literal_hits": wide_hits, "sharp_literal_hits": sharp_hits,
            "minimum": witness(minimum), "first_wide": witness(first_wide),
            "first_sharp": witness(first_sharp), "per_class": per_class}


def validate():
    comparisons = representations = 0
    # An independent all-positive-weight enumeration checks the public
    # parametrization on finite budgets, including nonprimitive weights.
    for b in range(1, 21):
        for limit in (1, 2, 6, 16):
            n = b**6
            width, caches, counts = construct(n, limit)
            assert width == b
            actual = set()
            for cache in caches:
                seen = 0
                for a, bw, m, centre, representation in public_rows(cache):
                    del representation
                    actual.add((a, bw))
                    assert centre == ceil_sqrt(4*n*a*bw)
                    assert (centre-1)**2 < 4*n*a*bw <= centre*centre
                    seen += 1
                assert seen == len(cache.splits)*representation_count(cache.maximum_index)
                representations += seen
            expected = set()
            classes = squarefree_classes(limit)
            for a in range(1, b*b+1):
                for bw in range(1, b*b//a+1):
                    k = a*bw
                    if any(k % d == 0 and math.isqrt(k//d)**2 == k//d for d in classes):
                        expected.add((a, bw))
            assert actual == expected
            assert counts["literal_centre_square_roots"] == sum(c.maximum_index for c in caches)
            comparisons += 1
    p, q = CONTROL_PRIMES
    assert isprime(p) and isprime(q)
    control = diagnose(p, q, 1)
    assert control["width"] == 39 and control["counts"]["weight_representations"] == 384
    assert control["wide_literal_hits"] == control["sharp_literal_hits"] == 0
    assert control["minimum"]["offset"] == 137
    assert (control["minimum"]["a"], control["minimum"]["b"]) == (25, 36)
    a, bw = 12, 17
    centre = ceil_sqrt(4*p*q*a*bw)
    assert a*q+bw*p == centre and math.isqrt(a*bw)**2 != a*bw
    assert math.gcd(p*q, (centre+math.isqrt(centre*centre-4*a*bw*p*q))//2) in (p, q)
    sharp_certificate = public_discriminant_control(p*q, 39, 16, False)
    assert sharp_certificate["candidate_discriminant_square_roots"] == 620
    assert sharp_certificate["proper_factors"] == 0
    wp, wq = WIDE_CONTROL_PRIMES
    assert isprime(wp) and isprime(wq)
    wide_control = diagnose(wp, wq, 16)
    assert wide_control["width"] == 25 and wide_control["prefix_complement"]
    assert wide_control["wide_literal_hits"] == 0
    assert wide_control["minimum"]["offset"] == 35
    wide_certificate = public_discriminant_control(wp*wq, 25, 16, True)
    assert wide_certificate["candidate_discriminant_square_roots"] == 3975
    assert wide_certificate["proper_factors"] == 0
    outside_centre = ceil_sqrt(4*wp*wq*16*19)
    assert 16*wq+19*wp == outside_centre and 16*19 == 19*4**2
    return {"all_weight_oracle_comparisons": comparisons,
            "exact_generated_representations": representations,
            "budget_widths": [1, 20], "class_limits": [1, 2, 6, 16],
            "square_control": control,
            "control_nonsquare_hit": {"a": a, "b": bw, "product": a*bw,
                                      "centre": centre, "offset": 0},
            "sharp_public_certificate": sharp_certificate,
            "wide_control": wide_control,
            "wide_public_certificate": wide_certificate,
            "wide_control_outside_menu_hit": {"a": 16, "b": 19, "product": 304,
                                               "class": 19, "centre": outside_centre, "offset": 0},
            "oracle_scope": "finite checks use all weights and reference primes outside public construction"}


def inputs():
    rng = random.Random(SEED)
    cases = [{"kind": "Lean-verified-square-control", "reference_primes": list(CONTROL_PRIMES)}]
    cases.append({"kind": "Lean-verified-wide-menu-control",
                  "reference_primes": list(WIDE_CONTROL_PRIMES)})
    for bits in (32, 40, 48, 64, 80):
        lo, hi = 1 << (bits//2-1), 1 << (bits//2)
        for index in range(2):
            while True:
                p = int(gmpy2.next_prime(rng.randrange(lo, hi)))
                q = int(gmpy2.next_prime(rng.randrange(lo, hi)))
                if p != q and (p*q).bit_length() == bits:
                    break
            assert isprime(p) and isprime(q)
            cases.append({"kind": "fresh-balanced", "nominal_bits": bits, "index": index,
                          "reference_primes": sorted((p, q))})
    return cases


def reproduce_wide_control():
    """Deterministic reference-prime search that produced the wide control."""
    rng = random.Random(WIDE_SEARCH_SEED)
    accepted = 0
    explored_bits = []
    for bits in (20, 24, 28, 32):
        explored_bits.append(bits)
        lo, hi = 1 << (bits//2-1), 1 << (bits//2)
        for _ in range(400):
            p = int(gmpy2.next_prime(rng.randrange(lo, hi)))
            q = int(gmpy2.next_prime(rng.randrange(lo, hi)))
            if p == q or (p*q).bit_length() != bits:
                continue
            accepted += 1
            result = diagnose(p, q, 16)
            if result["wide_literal_hits"] == 0:
                assert tuple(sorted((p, q))) == WIDE_CONTROL_PRIMES
                assert accepted == 503
                return {"scope": "untimed reference-prime diagnostic",
                        "seed": WIDE_SEARCH_SEED,
                        "accepted_prime_pairs_to_first_miss": accepted,
                        "nominal_bit_stages": explored_bits,
                        "trials_per_stage": 400,
                        "reference_primes": list(WIDE_CONTROL_PRIMES)}
    raise AssertionError("saved wide-window control search did not reproduce")


def audit():
    regression = validate()
    control_search = reproduce_wide_control()
    replay = []
    for case in inputs():
        p, q = case["reference_primes"]
        square = diagnose(p, q, 1)
        menu = diagnose(p, q, 16)
        assert square["prefix_complement"] and menu["prefix_complement"]
        assert square["wide_literal_hits"] <= menu["wide_literal_hits"]
        assert square["sharp_literal_hits"] <= menu["sharp_literal_hits"]
        replay.append({**case, "square_product": square, "small_class_menu": menu})
    paths = ("scripts/probe_semiprime_square_product_cover.py",
             "RiemannGaussian/SemiprimeSquareProductCover.lean",
             "scripts/CheckSemiprimeSquareProductCover.lean",
             "RiemannGaussian/SemiprimeLehmanCoverage.lean")
    return {"seed": SEED,
            "scope": "exact labelled coverage diagnostic; not a public factoring algorithm or a runtime benchmark",
            "public_construction_inputs": "N and fixed square-class menu only",
            "reference_oracle": "weighted sums use p and q only after public construction",
            "arithmetic": "integer roots, centres, discriminants and strict squared boundary tests",
            "complexity_scope": "exact centre and weight-representation counts; no formal bit-cost bound",
            "wide_control_search": control_search,
            "regression": regression, "replay": replay,
            "source_hashes": {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--validate-only", action="store_true")
    args = parser.parse_args()
    result = validate() if args.validate_only else audit()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    regression = result if args.validate_only else result["regression"]
    summary = {"exact_weight_oracle_comparisons": regression["all_weight_oracle_comparisons"],
               "output": str(args.output) if args.output else None,
               "universal_sixth_bit_bound": False}
    if not args.validate_only:
        summary["inputs"] = len(result["replay"])
        summary["wide_window_misses_square"] = sum(not r["square_product"]["wide_literal_hits"] for r in result["replay"])
        summary["wide_window_misses_small_menu"] = sum(not r["small_class_menu"]["wide_literal_hits"] for r in result["replay"])
        summary["sharp_window_misses_small_menu"] = sum(not r["small_class_menu"]["sharp_literal_hits"] for r in result["replay"])
    print(json.dumps(summary))


if __name__ == "__main__":
    main()

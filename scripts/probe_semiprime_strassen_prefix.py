#!/usr/bin/env python3
"""Exact replay of the complete polynomial small-factor prefix.

The public routine receives N and optional B only. Reference factors are
used afterwards to label coverage. This validates the polynomial/prefix
interface and charges each construction; it is not a complete sixth-root
factorizer or a formal bit-complexity certificate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import time

import gmpy2
from sympy import nextprime

ROOT = Path(__file__).resolve().parents[1]
MonicBatch = runpy.run_path(str(ROOT / "scripts/probe_semiprime_long_period.py"))["MonicBatch"]
SEED = 202610022104


def sixth_width(n):
    root = int(gmpy2.iroot(n, 6)[0])
    return root + (root**6 < n)


def factor_prefix(n, width=None, include_signals=False):
    """One B-root product and B-point evaluation; at most one lazy scan."""
    start = time.perf_counter()
    if n < 2:
        raise ValueError("modulus at least two required")
    b = sixth_width(n) if width is None else width
    if b < 0 or b*b >= n:
        raise ValueError("nonnegative width with B squared below N required")
    roots = [(-(i+1)) % n for i in range(b)]
    targets = [j*b for j in range(b)]
    batch = MonicBatch(n)
    polynomial = batch.tree(roots)[0]
    values = batch.evaluate(polynomial, targets)
    stats = {"root_residues": b, "target_residues": b,
             "polynomial_coefficients": len(polynomial),
             "covered_integers": b*b, "explicit_grid_candidates": 0,
             "column_gcds": 0, "leaf_gcds": 0,
             "whole_modulus_columns": 0, "lazy_integer_candidates": 0}
    factor = None
    for j, value in enumerate(values):
        stats["column_gcds"] += 1
        divisor = math.gcd(n, value)
        if divisor == 1:
            continue
        if divisor == n:
            stats["whole_modulus_columns"] += 1
            leaves = [j*b+i+1 for i in range(b)]
            stats["lazy_integer_candidates"] += len(leaves)
            assert all(0 < v < n for v in leaves)
            for v in leaves:
                stats["leaf_gcds"] += 1
                divisor = math.gcd(n, v)
                if 1 < divisor < n:
                    break
            else:
                raise AssertionError("nonunit block has no proper leaf")
        assert 1 < divisor < n and n % divisor == 0
        factor = divisor
        break
    stats.update(batch.stats())
    stats["gcd_calls"] = stats["column_gcds"] + stats["leaf_gcds"]
    stats["gcd_bound"] = 2*b
    assert stats["gcd_calls"] <= 2*b
    assert stats["whole_modulus_columns"] <= 1
    assert stats["lazy_integer_candidates"] <= b
    result = {"N": n, "width": b, "factor": factor,
              "status": "factor" if factor else "prefix-clear",
              "elapsed_ms": 1000*(time.perf_counter()-start), "metrics": stats}
    if include_signals:
        result["signals"] = values
    return result


def validate_small():
    """Independent exhaustive integer products, outside charged recovery."""
    checked = saturated = 0
    for n in range(4, 257):
        for b in range(math.isqrt(n-1)+1):
            result = factor_prefix(n, b, True)
            expected_values = [math.prod(j*b+i+1 for i in range(b)) % n
                               for j in range(b)]
            assert result["signals"] == expected_values
            clear = math.gcd(n, math.factorial(b*b)) == 1
            assert (result["factor"] is None) == clear
            checked += 1
            saturated += result["metrics"]["whole_modulus_columns"]
    controls = [factor_prefix(35, 4, True), factor_prefix(49, 4, True),
                factor_prefix(77, 6, True), factor_prefix(101, 10, True)]
    assert controls[0]["factor"] == 5
    assert controls[0]["signals"] == [24, 0, 15, 0]
    assert controls[0]["metrics"]["whole_modulus_columns"] == 1
    assert controls[1]["factor"] == 7
    assert controls[2]["factor"] in (7, 11)
    assert controls[3]["factor"] is None
    return {"exhaustive_batches": checked,
            "whole_modulus_recoveries": saturated, "controls": controls}


def fresh_pair(bits, regime, rng):
    """Choose the complete diagnostic corpus before observing a result."""
    pbits = bits//2 if regime == "balanced" else bits//3-1
    while True:
        p = int(nextprime(rng.randrange(1 << (pbits-1), (1 << pbits)-64)))
        lower = ((1 << (bits-1)) + p-1)//p
        upper = ((1 << bits)-1)//p
        q = int(nextprime(rng.randrange(lower, upper-256)))
        if p != q and q <= upper and (p*q).bit_length() == bits:
            return min(p, q), max(p, q)


def replay():
    validation = validate_small()
    rng = random.Random(SEED)
    inputs = [(bits, regime, *fresh_pair(bits, regime, rng))
              for bits in (32, 48, 64, 80)
              for regime in ("small-factor", "balanced") for _ in range(4)]
    inputs += [(32, "previous-coverage-control", 46337, 65521),
               (28, "previous-coverage-control", 13309, 15767),
               (36, "previous-long-period-control", 248909, 249521)]
    results = []
    for bits, regime, p, q in inputs:
        result = factor_prefix(p*q)
        expected = p <= result["width"]**2 or q <= result["width"]**2
        assert (result["factor"] is not None) == expected
        result.update({"input_bits": (p*q).bit_length(), "regime": regime,
                       "reference_p": p, "reference_q": q,
                       "expected_small_factor": expected})
        results.append(result)
    sources = ["RiemannGaussian/SemiprimeStrassenPrefix.lean",
               "RiemannGaussian/SemiprimeLehmanCoverage.lean",
               "RiemannGaussian/SemiprimeCartesianCompletion.lean",
               "RiemannGaussian/SemiprimeGroupCoverage.lean",
               "scripts/CheckSemiprimeStrassenPrefix.lean",
               "scripts/probe_semiprime_strassen_prefix.py",
               "scripts/probe_semiprime_long_period.py",
               "scripts/probe_semiprime_weighted_batch.py",
               "scripts/probe_semiprime_quadratic_extraction.py",
               "scripts/probe_semiprime_single_extraction.py"]
    return {"seed": SEED, "scope": "complete additive small-factor prefix only",
            "is_complete_semiprime_factorizer": False,
            "is_bit_complexity_certificate": False,
            "one_sixth_guarantee": "OPEN",
            "source_sha256": {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
                              for p in sources},
            "reference_algorithm": "https://arxiv.org/html/2010.05450#S2.SS3",
            "validation": validation, "fresh_and_prior_inputs": results,
            "input_count": len(results),
            "summary": {"factors": sum(r["factor"] is not None for r in results),
                        "clear_prefixes": sum(r["factor"] is None for r in results),
                        "explicit_grid_candidates": sum(r["metrics"]["explicit_grid_candidates"]
                                                        for r in results)},
            "limitations": "The original centre-coupled Lehman complement remains explicit; the Lean definition specifies polynomial values and does not implement this GMP product/remainder tree or prove its bit cost."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = replay()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"exact_batches": result["validation"]["exhaustive_batches"],
                      "whole_modulus_recoveries": result["validation"]["whole_modulus_recoveries"],
                      "input_count": result["input_count"],
                      "summary": result["summary"],
                      "one_sixth_guarantee": result["one_sixth_guarantee"]}, indent=2))


if __name__ == "__main__":
    main()

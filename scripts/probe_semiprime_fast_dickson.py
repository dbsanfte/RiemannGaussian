#!/usr/bin/env python3
"""Optional public-input high-degree Dickson collision audit.

Binary doubling evaluates the polynomial at each point without expanding
its coefficients. Degree N is cheap but injective in the smaller odd
prime field. Nearby degrees are experiments, never universal coverage.
Recovery takes only N and a public degree name. Private prime factors
appear solely in reproducible sample generation and labelled diagnostics.
No persistent lookup, hidden order oracle, or normal-CI execution.
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

ROOT = Path(__file__).resolve().parents[1]
API = runpy.run_path(str(ROOT / "scripts/probe_semiprime_group_selection.py"))
SEED = 2026100441
DEGREES = ("linear", "six", "twenty-four", "N", "N-1", "N+1")
CONTROLS = ((6827, 7187), (2346272483, 3649327547),
            (661911275027, 720957498683), (494041, 494191))


def dickson_binary(x, degree, modulus, counters=None):
    """D_degree(x,1) in two modular multiplications per degree bit."""
    if degree < 0 or modulus < 2:
        raise ValueError("nonnegative degree and modulus >= 2 required")
    if degree == 0:
        return 2 % modulus
    if degree == 1:
        return x % modulus
    a, b = 2 % modulus, x % modulus
    for bit in bin(degree)[2:]:
        cross = (a*b-x) % modulus
        if bit == "0":
            a, b = (a*a-2) % modulus, cross
        else:
            a, b = cross, (b*b-2) % modulus
        if counters is not None:
            counters["binary_updates"] += 1
            counters["modular_multiplications"] += 2
    return a


def degree_value(n, name):
    return {"linear": 1, "six": 6, "twenty-four": 24,
            "N": n, "N-1": n-1, "N+1": n+1}[name]


def partition_signature(values):
    """Canonical collision partition, without a quadratic pair scan."""
    labels = {}
    return [labels.setdefault(value, len(labels)) for value in values]


def factor_fold(n, degree_name="N-1"):
    """One charged B-by-B batch; budget exhaustion is an explicit result."""
    if n < 4:
        raise ValueError("N>=4 required")
    if n % 2 == 0:
        return {"status": "factor", "factor": 2, "stage": "even"}
    root = math.isqrt(n)
    if root*root == n:
        return {"status": "factor", "factor": root, "stage": "square"}
    width = API["SINGLE"]["ceil_root"](n, 6)
    degree = degree_value(n, degree_name)
    work = {"binary_updates": 0, "modular_multiplications": 0}
    counters = API["Counters"]()
    started = time.perf_counter()
    roots = [dickson_binary(i, degree, n, work) for i in range(width)]
    points = [dickson_binary(width*j, degree, n, work)
              for j in range(1, width+1)]
    result = API["scalar_collision"](n, roots, points, counters)
    elapsed = 1000*(time.perf_counter()-started)
    if result["factor"]:
        factor = result["factor"]
        assert 1 < factor < n and n % factor == 0
        assert math.gcd(result["certificate_signal"], n) == factor
    return {**result, "n": n, "degree_name": degree_name,
            "degree": str(degree), "degree_bits": degree.bit_length(),
            "bound": width, "points": 2*width,
            "fold_work": work, "batch_work": counters.data,
            "elapsed_ms": elapsed}


def exact_small_checks():
    checked = 0
    for modulus in (9, 15, 35, 77, 101):
        for x in range(-3, 15):
            a, b = 2 % modulus, x % modulus
            for degree in range(66):
                assert dickson_binary(x, degree, modulus) == a
                a, b = b, (x*b-a) % modulus
                checked += 1
    primes = [p for p in range(3, 200) if gmpy2.is_prime(p)]
    pair_count, both, exceptions = 0, 0, []
    for i, p in enumerate(primes):
        for q in primes[i+1:]:
            n = p*q
            assert math.gcd(n, p*p-1) == 1
            p_values = [dickson_binary(x, n, p) for x in range(p)]
            q_values = [dickson_binary(x, n, q) for x in range(q)]
            p_image, q_image = len(set(p_values)), len(set(q_values))
            for prime, values in ((p, p_values), (q, q_values)):
                effective = math.gcd(n, prime*prime-1)
                compressed = [dickson_binary(x, effective, prime) for x in range(prime)]
                assert partition_signature(values) == partition_signature(compressed)
            assert p_image == p
            assert (q_image == q) == (math.gcd(n, q*q-1) == 1)
            pair_count += 1
            both += q_image == q
            if q_image != q:
                assert (q-1) % p == 0 or (q+1) % p == 0
                exceptions.append({"p": p, "q": q, "larger_image": q_image})
    return {"binary_recurrence_checks": checked, "prime_pairs": pair_count,
            "full_prime_field_partition_checks": 2*pair_count,
            "smaller_permutations": pair_count, "both_permutations": both,
            "larger_field_exceptions": exceptions}


def fresh_corpus(count):
    """Private reproducible generator; the recovery functions get only N."""
    rng = random.Random(SEED)
    out = []
    for bits in (40, 48, 64):
        found = set()
        while len(found) < count:
            p = int(gmpy2.next_prime(rng.randrange(1 << (bits//2-1), 1 << (bits//2))))
            q = int(gmpy2.next_prime(rng.randrange(1 << (bits//2-1), 1 << (bits//2))))
            p, q = sorted((p, q))
            if p != q and (p*q).bit_length() == bits:
                found.add((p, q))
        out.extend(sorted(found))
    return out


def diagnose(p, q):
    n = p*q
    width = API["SINGLE"]["ceil_root"](n, 6)
    inputs = list(range(width))+[width*j for j in range(1, width+1)]
    gcds, collisions, checks = {}, {}, 0
    for name in DEGREES:
        degree = degree_value(n, name)
        gcds[name], collisions[name] = [], []
        for prime in (p, q):
            effective = math.gcd(degree, prime*prime-1)
            values = [dickson_binary(x, degree, prime) for x in inputs]
            compressed = [dickson_binary(x, effective, prime) for x in inputs]
            assert partition_signature(values) == partition_signature(compressed)
            gcds[name].append(effective)
            baby_counts = {}
            for value in values[:width]:
                baby_counts[value] = baby_counts.get(value, 0)+1
            collisions[name].append(sum(baby_counts.get(value, 0) for value in values[width:]))
            checks += 1
    return {"reference_only": True, "p": p, "q": q,
            "field_exponent_gcd": gcds, "private_cover_collisions": collisions,
            "cover_partition_checks": checks}


def replay(fresh_per_size):
    checks = exact_small_checks()
    populations = [("saved", CONTROLS), ("fresh", fresh_corpus(fresh_per_size))]
    rows, aggregate = [], {}
    for population, corpus in populations:
        totals = {name: {"hits": 0, "cases": len(corpus),
                         "modular_multiplications": 0, "elapsed_ms": 0.0}
                  for name in DEGREES}
        for p, q in corpus:
            results = [factor_fold(p*q, name) for name in DEGREES]
            for result in results:
                total = totals[result["degree_name"]]
                total["hits"] += bool(result["factor"])
                total["modular_multiplications"] += result["fold_work"]["modular_multiplications"]
                total["elapsed_ms"] += result["elapsed_ms"]
            rows.append({"population": population, "n": p*q,
                         "reference_diagnostic": diagnose(p, q), "results": results})
        aggregate[population] = totals
    sources = sorted((ROOT / "scripts").glob("probe_semiprime*.py"))
    sources.append(ROOT / "RiemannGaussian/SemiprimeFastDickson.lean")
    return {"schema": 1, "seed": SEED, "fresh_per_size": fresh_per_size,
            "fresh_exact_bit_lengths": [40, 48, 64], "degree_menu": list(DEGREES),
            "protocol": "Single full calls with warm imports; exploratory, no tuned classical comparison.",
            "conclusion": "Degree N has no new smaller-prime collisions. No universal nearby-degree coverage or N^(1/6) success theorem.",
            "checks": checks, "aggregate": aggregate, "rows": rows,
            "source_hashes": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                              for path in sources}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    factor = commands.add_parser("factor")
    factor.add_argument("n", type=int)
    factor.add_argument("--degree", choices=DEGREES, default="N-1")
    probe = commands.add_parser("probe")
    probe.add_argument("--fresh-per-size", type=int, default=8)
    probe.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.command == "factor":
        print(json.dumps(factor_fold(args.n, args.degree), indent=2))
    else:
        if args.fresh_per_size < 1:
            parser.error("--fresh-per-size must be positive")
        result = replay(args.fresh_per_size)
        if args.output:
            args.output.write_text(json.dumps(result, indent=2)+"\n")
        print(json.dumps({"checks": {key: value for key, value in result["checks"].items()
                                    if key != "larger_field_exceptions"},
                          "aggregate": result["aggregate"]}, indent=2))


if __name__ == "__main__":
    main()

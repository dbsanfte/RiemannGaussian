#!/usr/bin/env python3
"""Public centre-free collision cover with an explicitly charged reshape.

Optional exact research replay, outside ordinary builds and CI. It returns
an unresolved projection kernel when the fixed public base is insufficient.
The standard reshape constructs O(B^(3/2)) inputs; this is not a complete
sixth-root factorizer or a Lean bit-complexity certificate.
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
from sympy import n_order

ROOT = Path(__file__).resolve().parents[1]
RECOVERY = runpy.run_path(str(ROOT / "scripts/probe_semiprime_batch_recovery.py"))["recovery"]
PREFIX = runpy.run_path(str(ROOT / "scripts/probe_semiprime_strassen_prefix.py"))
SEED = 202610022233


def geometric(start, ratio, length, n):
    values = []
    value = start
    for _ in range(length):
        values.append(value)
        value = value*ratio % n
    return values


def reshape_inputs(n, b, alpha, m):
    """No literal centres, full exponent interval or pair matrix."""
    blocks = 3*b*b//m+1
    axis = pow(alpha, n, n)
    root = axis*pow(alpha, b*b, n) % n
    shift = pow(pow(alpha, -1, n), m, n)
    roots = []
    for _ in range(b):
        roots.extend(geometric(root, shift, blocks, n))
        root = root*axis % n
    points = geometric(1, alpha, m, n)
    return roots, points, blocks


def centre_free_pass(n, base=2):
    """The constructor receives public N and a fixed base only."""
    start = time.perf_counter()
    b = PREFIX["sixth_width"](n)
    stats = {"literal_centre_roots": 0, "explicit_pair_candidates": 0,
             "projection_powers": 0, "projection_exponent_bits": 0,
             "projection_gcds": 0, "short_roots": 0, "short_points": 0,
             "shifted_roots": 0, "baby_points": 0, "long_gcds": 0}
    result = {"N": n, "width": b, "base": base, "factor": None,
              "status": "unresolved", "metrics": stats}

    def finish(status, factor=None):
        if factor is not None:
            assert 1 < factor < n and n % factor == 0
        result.update(status=status, factor=factor,
                      elapsed_ms=1000*(time.perf_counter()-start))
        return result

    prefix = PREFIX["factor_prefix"](n)
    result["prefix"] = prefix
    if prefix["factor"] is not None:
        return finish("prefix-factor", prefix["factor"])
    divisor = math.gcd(base, n)
    if 1 < divisor < n:
        return finish("base-factor", divisor)
    if divisor != 1:
        return finish("nonunit-base")
    alpha = pow(base, n-1, n)
    stats["projection_powers"] += 1
    stats["projection_exponent_bits"] += (n-1).bit_length()
    repetition = n.bit_length()  # clog 2 (N+1), for positive N
    for i in range(1, b+1):
        stats["projection_gcds"] += 1
        divisor = math.gcd(alpha-1, n)
        if 1 < divisor < n:
            result["alpha"] = alpha
            return finish("projection-factor", divisor)
        if divisor == n:
            result["alpha"] = alpha
            return finish("projection-kernel")
        if i >= 2:
            exponent = i**repetition
            alpha = pow(alpha, exponent, n)
            stats["projection_powers"] += 1
            stats["projection_exponent_bits"] += exponent.bit_length()
    stats["projection_gcds"] += 1
    divisor = math.gcd(alpha-1, n)
    result["alpha"] = alpha
    if 1 < divisor < n:
        return finish("projection-factor", divisor)
    if divisor == n:
        return finish("projection-kernel")

    short_width = 2*b+1
    short_roots = geometric(1, alpha, short_width, n)
    step = pow(alpha, short_width, n)
    short_points = geometric(step, step, short_width, n)
    short = RECOVERY(n, short_roots, short_points)
    stats.update(short_roots=len(short_roots), short_points=len(short_points))
    result["short_pass"] = short
    if short["factor"] is not None:
        return finish("short-period-factor", short["factor"])

    long_start = time.perf_counter()
    m = math.isqrt(3*b**3)+1
    roots, points, blocks = reshape_inputs(n, b, alpha, m)
    stats.update(shifted_roots=len(roots), baby_points=len(points),
                 long_gcds=0, reshape_blocks=blocks, reshape_size=m)
    assert (len(roots)+len(points))**2 > 12*b**3
    long = RECOVERY(n, roots, points)
    stats["long_gcds"] = long["metrics"]["gcd_calls"]
    result["long_pass"] = long
    result["long_elapsed_ms"] = 1000*(time.perf_counter()-long_start)
    if long["factor"] is None:
        return finish("no-proper-collision")
    a = long["root_index"]//blocks+1
    j = long["root_index"] % blocks
    i = long["point_index"]
    u = j*m+i
    original = (pow(alpha, u, n)-pow(alpha, a*n+b*b, n)) % n
    assert math.gcd(original, n) == long["factor"]
    result["original_witness"] = {"a": a, "u": u, "block": j, "baby": i,
                                  "residue": original}
    return finish("centre-free-factor", long["factor"])


def relation_witness(p, q, b):
    """Reference arithmetic, run only after the public constructor."""
    for a in range(1, b+1):
        near = a*q//p
        for weight in (near, near+1):
            delta = a*q-weight*p
            if weight > 0 and a*weight <= b*b and delta*delta*b*b < p*q:
                u = b*b+weight+delta
                assert a+weight <= b*b+1 and 0 <= u <= 3*b*b
                assert a*p*q+b*b == u+(p-1)*(a*q+weight)
                return {"a": a, "b": weight, "delta": delta, "u": u}
    raise AssertionError("universal relation missing")


def annotate(result, p, q, regime):
    """Private references label the completed public computation only."""
    n, b = result["N"], result["width"]
    assert p*q == n
    result.update(reference_p=p, reference_q=q, input_bits=n.bit_length(), regime=regime)
    if p > b*b:
        witness = relation_witness(p, q, b)
        result["reference_relation"] = witness
        if "alpha" in result:
            alpha = result["alpha"]
            orders = [int(n_order(alpha % p, p)), int(n_order(alpha % q, q))]
            result["reference_local_orders"] = orders
            assert math.gcd(*orders) == 1
            if result["status"] in ("short-period-factor", "centre-free-factor",
                                     "no-proper-collision"):
                for period in orders:
                    assert all(period % int(r) for r in
                               gmpy2_primes_up_to(b))
            if result["status"] == "centre-free-factor":
                assert min(orders) > (2*b+1)**2
                u, a = witness["u"], witness["a"]
                assert math.gcd(pow(alpha, u, n)-pow(alpha, a*n+b*b, n), n) == p
    if result["status"] not in ("projection-kernel", "nonunit-base"):
        assert result["factor"] is not None
    return result


def gmpy2_primes_up_to(b):
    r = 2
    while r <= b:
        yield r
        r = int(gmpy2.next_prime(r))


def validate_small():
    checked = kernels = 0
    primes = list(gmpy2_primes_up_to(59))
    for i, p in enumerate(primes):
        for q in primes[i+1:]:
            for base in (2, 3):
                result = annotate(centre_free_pass(p*q, base), p, q, "small-exact")
                checked += 1
                kernels += result["status"] == "projection-kernel"
    # Verify every shifted difference against the original observable.
    shifts = 0
    for n, alpha, b, m in ((35, 2, 3, 5), (77, 3, 4, 7), (143, 2, 4, 6)):
        roots, points, blocks = reshape_inputs(n, b, alpha, m)
        for index, root in enumerate(roots):
            a, j = index//blocks+1, index % blocks
            for i, point in enumerate(points):
                assert math.gcd(point-root, n) == math.gcd(
                    pow(alpha, j*m+i, n)-pow(alpha, a*n+b*b, n), n)
                shifts += 1
    return {"small_public_runs": checked, "exposed_kernels": kernels,
            "exact_gcd_shift_checks": shifts}


def replay():
    validation = validate_small()
    rng = random.Random(SEED)
    corpus = [(bits, regime, *PREFIX["fresh_pair"](bits, regime, rng))
              for bits in (32, 40, 48)
              for regime in ("balanced", "small-factor") for _ in range(4)]
    corpus += [(32, "prior-long-control", 44963, 62347),
               (40, "prior-long-control", 714107, 1013003),
               (21, "explicit-base-kernel", 829, 1657)]
    results = [annotate(centre_free_pass(p*q), p, q, regime)
               for _, regime, p, q in corpus]
    sources = ["RiemannGaussian/SemiprimeCentreFreeCover.lean",
               "RiemannGaussian/SemiprimeLehmanCoverage.lean",
               "RiemannGaussian/SemiprimeOrderSeparation.lean",
               "RiemannGaussian/SemiprimeRHCancellation.lean",
               "RiemannGaussian/SemiprimeStrassenPrefix.lean",
               "RiemannGaussian/SemiprimeCartesianCompletion.lean",
               "scripts/CheckSemiprimeCentreFreeCover.lean",
               "scripts/probe_semiprime_centre_free_cover.py",
               "scripts/probe_semiprime_batch_recovery.py",
               "scripts/probe_semiprime_strassen_prefix.py",
               "scripts/probe_semiprime_long_period.py",
               "scripts/probe_semiprime_weighted_batch.py",
               "scripts/probe_semiprime_quadratic_extraction.py",
               "scripts/probe_semiprime_single_extraction.py"]
    statuses = sorted({r["status"] for r in results})
    return {"seed": SEED, "scope": "centre-free cover with standard explicit reshape",
            "is_complete_semiprime_factorizer": False,
            "is_bit_complexity_certificate": False, "one_sixth_guarantee": "OPEN",
            "source_sha256": {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
                              for p in sources},
            "validation": validation, "fresh_and_prior_inputs": results,
            "input_count": len(results),
            "summary": {status: sum(r["status"] == status for r in results)
                        for status in statuses},
            "limitations": "All setup is timed; private reference factors/orders are computed afterwards. The long pass constructs B*(floor(3*B^2/m)+1) shifted roots and m babies, which is not a one-sixth input budget. Projection kernels remain exposed; Lean certifies the algebra and recovery specification, not this Python engine or bit cost."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = replay()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: result[k] for k in
                      ("validation", "input_count", "summary", "one_sixth_guarantee")}, indent=2))


if __name__ == "__main__":
    main()

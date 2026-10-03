#!/usr/bin/env python3
"""Replay the public bounded-collision branch with exact global-order stripping.

This mirrors SemiprimeCollisionPeeling: reduce a derived annihilator using
power equalities, retain the exact prime-test residues, scan their GCDs,
then use the compressed common-modulus progression. All factor searches,
powers, unit checks, lookup setup and polynomial work are timed and counted.
Small orders and above-cap orders remain explicit. Research replay only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
PROGRESSION = runpy.run_path(str(ROOT/"scripts/probe_semiprime_progression_prefix.py"))
COMMON, PREFIX = PROGRESSION["COMMON"], PROGRESSION["PREFIX"]
PARENT = "docs/semiprime-progression-prefix-audit.json"
REPLAY_ID = 202610030801


def prime_list(value, metrics):
    """Trial factorization of a collision-derived integer, with multiplicity."""
    metrics["trial_factorizations"] += 1
    factors = COMMON["trial_factors"](value, metrics)
    return [p for p, multiplicity in sorted(factors.items()) for _ in range(multiplicity)]


def new_metrics():
    return dict(peel_unit_gcds=0, annihilator_verification_powers=0,
                trial_factorizations=0, trial_divisor_tests=0, trial_strip_divisions=0,
                stripping_power_queries=0, stripping_rounds=0,
                final_order_verification_powers=0, final_prime_power_queries=0,
                prime_test_gcds=0, geometric_rows=0, explicit_grid_candidates=0)


def peel_order(n, base, exponent, metrics):
    """The numerical order is derived from public power equalities only."""
    metrics["peel_unit_gcds"] += 1
    if exponent < 1 or n < 2 or math.gcd(n, base) != 1:
        raise ValueError("positive annihilator and a unit modulo N>=2 required")
    metrics["annihilator_verification_powers"] += 1
    if pow(base, exponent, n) != 1:
        raise ValueError("input exponent does not annihilate the public base")
    original, trace = exponent, []
    while True:
        primes = prime_list(exponent, metrics)
        if not trace:
            initial_length = len(primes)
        for prime in primes:
            metrics["stripping_power_queries"] += 1
            value = pow(base, exponent//prime, n)
            trace.append(dict(exponent=exponent, prime=prime, value=value))
            if value == 1:
                exponent //= prime
                metrics["stripping_rounds"] += 1
                break
        else:
            assert 2**metrics["stripping_rounds"] <= original
            assert 2**initial_length <= original
            assert metrics["stripping_power_queries"] <= (metrics["stripping_rounds"]+1)*initial_length
            return exponent, trace


def factor_collision(n, base, width=None, block=None):
    """Public input N/base/width; no numerical order or hidden factors."""
    start = time.perf_counter()
    width = PREFIX["sixth_width"](n) if width is None else width
    block = 2*width if block is None else block
    if n < 4 or width < 1 or block < 1:
        raise ValueError("N>=4 and positive public widths required")
    metrics = new_metrics()
    metrics.update(square_root_queries=1, base_gcds=0)
    result = dict(N=n, base=base, width=width, block=block, factor=None, metrics=metrics)

    def finish(status, factor=None):
        if factor is not None:
            assert 1 < factor < n and n % factor == 0
        result.update(status=status, factor=factor, elapsed_ms=1000*(time.perf_counter()-start))
        return result

    root = math.isqrt(n)
    if root*root == n:
        return finish("square-factor", root)
    result["prefix"] = PREFIX["factor_prefix"](n, width)
    if result["prefix"]["factor"] is not None:
        return finish("prefix-factor", result["prefix"]["factor"])
    metrics["base_gcds"] += 1
    divisor = math.gcd(n, base)
    if 1 < divisor < n:
        return finish("base-factor", divisor)
    if divisor != 1:
        return finish("nonunit-base")
    result["collision"] = PROGRESSION["bounded_power_collision"](n, base, block)
    match = result["collision"]["match"]
    if match is None:
        return finish("bounded-order-exhausted")
    exponent = match["annihilator"]
    order, trace = peel_order(n, base, exponent, metrics)
    result.update(certified_order=order, stripping_trace=trace)
    primes = prime_list(order, metrics)
    metrics["final_order_verification_powers"] += 1
    assert pow(base, order, n) == 1
    # Retain the whole labeled source before the GCD scan, as in Lean.
    values = []
    for prime in primes:
        metrics["final_prime_power_queries"] += 1
        values.append((pow(base, order//prime, n)-1) % n)
    result["prime_power_values"] = [dict(prime=p, value=v) for p, v in zip(primes, values)]
    for value in values:
        metrics["prime_test_gcds"] += 1
        divisor = math.gcd(n, value)
        assert divisor < n  # Exact order excludes a globally trivial test.
        if divisor > 1:
            return finish("exact-order-prime-factor", divisor)
    if order < width:
        return finish("unresolved-small-order")
    result["progression"] = PROGRESSION["progression_prefix"](n, order, width)
    if result["progression"]["factor"] is not None:
        return finish("exact-order-progression-factor", result["progression"]["factor"])
    return finish("unresolved-progression")


def validate():
    # These reference orders/factors are never called by the public routines.
    from sympy import factorint, n_order, primerange

    reductions = nonexact = 0
    for n in range(2, 97):
        for base in range(1, n):
            if math.gcd(n, base) != 1:
                continue
            expected = int(n_order(base, n))
            for multiplier in (1, 2, 3):
                metrics = new_metrics()
                actual, _ = peel_order(n, base, multiplier*expected, metrics)
                assert actual == expected
                reductions += 1
                nonexact += int(multiplier != 1)

    covered = nonkernel = prime_factors = progression_factors = 0
    primes = list(primerange(5, 110))
    for index, p in enumerate(primes):
        for q in primes[index+1:]:
            n, width = p*q, PREFIX["sixth_width"](p*q)
            if p <= width*width:
                continue
            for base in range(2, 10):
                if math.gcd(n, base) != 1:
                    continue
                order = int(n_order(base, n))
                if not (width <= order <= 4*width*width):
                    continue
                actual = factor_collision(n, base)
                assert actual["factor"] in (p, q)
                assert actual["certified_order"] == order
                initial = actual["collision"]["match"]["annihilator"]
                assert len(actual["prime_power_values"]) <= sum(factorint(initial).values())
                if "progression" in actual:
                    assert actual["metrics"]["prime_test_gcds"]+actual["progression"]["metrics"]["gcd_calls"] <= sum(factorint(initial).values())+2*width
                covered += 1
                nonkernel += int(pow(base, n-1, n) != 1)
                prime_factors += int(actual["status"] == "exact-order-prime-factor")
                progression_factors += int(actual["status"] == "exact-order-progression-factor")

    controls = [factor_collision(n, base) for n, base in
                ((2929, 2535), (13747, 4), (1373653, 3), (769841, 508038),
                 (697, 696), (14608133, 64))]
    assert [c["factor"] for c in controls] == [29, 59, 829, 641, None, None]
    assert [c.get("certified_order") for c in controls] == [4, 29, 207, 40, 2, None]
    assert controls[0]["collision"]["match"]["annihilator"] == 8
    assert controls[2]["collision"]["match"]["annihilator"] == 414
    assert controls[2]["progression"]["metrics"]["whole_modulus_columns"] == 1
    assert controls[4]["status"] == "unresolved-small-order"
    assert controls[5]["status"] == "bounded-order-exhausted"
    for control in controls:
        if "certified_order" in control:
            assert control["certified_order"] == int(n_order(control["base"], control["N"]))
    return dict(exact_reductions=reductions, nonexact_annihilator_reductions=nonexact,
                covered_unit_cases=covered, covered_nonkernel_cases=nonkernel,
                exact_order_prime_factors=prime_factors, common_progression_factors=progression_factors,
                controls=controls,
                literal_base_provenance="2535 and 508038 are frozen offline diagnostics; all other bases are public literals. No universal seed-menu coverage is claimed.")


def source_inventory():
    parent = json.loads((ROOT/PARENT).read_text())
    for path, expected in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT, "RiemannGaussian/SemiprimeCollisionPeeling.lean",
                  "scripts/CheckSemiprimeCollisionPeeling.lean",
                  "scripts/probe_semiprime_collision_peeling.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    parent = json.loads((ROOT/PARENT).read_text())
    result = dict(replay_id=REPLAY_ID, scope="complete bounded collision-to-factor transport",
                  is_complete_semiprime_factorizer=False, is_bit_complexity_certificate=False,
                  one_sixth_guarantee="OPEN", validation=validate(),
                  inherited_corpus=dict(source=PARENT, input_count=parent["input_count"],
                                        recovered_count=parent["recovered_count"],
                                        replay_status="frozen parent; source hashes verified; not rerun"),
                  source_sha256=source_inventory(),
                  timing_protocol="Every covered call includes square and ordinary-prefix work, all unit checks, both power sources, sorting/merge, every repeated trial factorization, stripping powers, final prime-power sources/GCDs and any progression polynomial. Reference validation is outside timing.",
                  limitations="Useful seed coverage and above-cap orders remain open. Prime-factorization trial loops, residue backend and the complete every-run bit bound are not formalized. This variant reduces globally before the final GCD scan, so it can do more work than the frozen early-GCD prototype.")
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: v for k, v in result["validation"].items() if k not in ("controls", "literal_base_provenance")}, indent=2))


if __name__ == "__main__":
    main()

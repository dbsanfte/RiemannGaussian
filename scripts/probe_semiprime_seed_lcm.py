#!/usr/bin/env python3
"""Charged N-only factor-or-large-order routing by small seeds and LCMs.

The preceding ordinary prefix makes the small integer seeds units. A
nonroot of X^M-1 is found directly from N/M, then its bounded annihilator
is reduced by public powers. Clear exact-order tests certify an LCM
extension. A seed above the cap remains an explicit nonfactor result.
No reference prime, order, factor table or primality oracle enters routing.
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
PEELING = runpy.run_path(str(ROOT/"scripts/probe_semiprime_collision_peeling.py"))
PROGRESSION, PREFIX = PEELING["PROGRESSION"], PEELING["PREFIX"]
LEHMAN = runpy.run_path(str(ROOT/"scripts/probe_semiprime_lehman_coverage.py"))
PARENT = "docs/semiprime-collision-peeling-audit.json"
CORPUS = "docs/semiprime-progression-prefix-audit.json"
REPLAY_ID = 202610030901


def public_route(n):
    start = time.perf_counter()
    if n < 4:
        raise ValueError("semiprime input N>=4 required")
    width = PREFIX["sixth_width"](n)
    block, fuel = 2*width, (width-1).bit_length()
    metrics = dict(sixth_root_queries=1, square_root_queries=0,
                   seed_power_queries=0, seed_signal_gcds=0, seed_unit_gcds=0,
                   lookup_stages=0, lcm_updates=0, geometric_rows=0,
                   explicit_grid_candidates=0)
    result = dict(N=n, width=width, block=block, order_cap=block*block,
                  fuel=fuel, factor=None, large_base=None, stages=[], metrics=metrics)

    def finish(status, factor=None, large_base=None):
        if factor is not None:
            assert 1 < factor < n and n % factor == 0
        moduli = [stage["modulus"] for stage in result["stages"]]
        assert len(moduli) <= fuel
        assert sum(m+1 for m in moduli) <= width*fuel
        assert metrics["seed_power_queries"] <= sum(m+1 for m in moduli)
        assert metrics["lookup_stages"] <= len(moduli)
        result.update(status=status, factor=factor, large_base=large_base,
                      seed_moduli=moduli, elapsed_ms=1000*(time.perf_counter()-start))
        return result

    if width < 4:
        assert n <= 729
        result["finite_baseline"] = LEHMAN["recover"](n)
        return finish("finite-small-factor", factor=result["finite_baseline"]["factor"])
    metrics["square_root_queries"] += 1
    root = math.isqrt(n)
    if root*root == n:
        return finish("square-factor", factor=root)
    result["prefix"] = PREFIX["factor_prefix"](n, width)
    if result["prefix"]["factor"] is not None:
        return finish("prefix-factor", factor=result["prefix"]["factor"])

    modulus, remaining = 1, fuel
    while True:
        if modulus >= width:
            result["progression"] = PROGRESSION["progression_prefix"](n, modulus, width)
            result["certified_common_modulus"] = modulus
            if result["progression"]["factor"] is not None:
                return finish("lcm-progression-factor", factor=result["progression"]["factor"])
            return finish("unresolved-progression")
        if remaining == 0:
            return finish("unresolved-fuel")
        remaining -= 1
        stage = dict(modulus=modulus, candidate_power_queries=0)
        result["stages"].append(stage)
        for base in range(1, modulus+2):
            metrics["seed_power_queries"] += 1
            stage["candidate_power_queries"] += 1
            power = pow(base, modulus, n)
            if power != 1:
                break
        else:
            return finish("unresolved-seed-scan")
        stage.update(base=base, candidate_power=power)
        metrics["seed_signal_gcds"] += 1
        divisor = math.gcd(n, power-1)
        stage["seed_signal_gcd"] = divisor
        if 1 < divisor < n:
            return finish("seed-signal-factor", factor=divisor)
        metrics["seed_unit_gcds"] += 1
        divisor = math.gcd(n, base)
        if divisor != 1:
            if 1 < divisor < n:
                return finish("seed-base-factor", factor=divisor)
            return finish("unresolved-nonunit")

        metrics["lookup_stages"] += 1
        stage["collision"] = PROGRESSION["bounded_power_collision"](n, base, block)
        match = stage["collision"]["match"]
        if match is None:
            return finish("certified-large-order", large_base=base)
        stripping = PEELING["new_metrics"]()
        order, trace = PEELING["peel_order"](n, base, match["annihilator"], stripping)
        stage.update(derived_order=order, stripping_trace=trace, stripping_metrics=stripping)
        primes = PEELING["prime_list"](order, stripping)
        values = []
        for prime in primes:
            stripping["final_prime_power_queries"] += 1
            values.append((pow(base, order//prime, n)-1) % n)
        stage["prime_power_values"] = [dict(prime=p, value=v) for p, v in zip(primes, values)]
        for value in values:
            stripping["prime_test_gcds"] += 1
            divisor = math.gcd(n, value)
            assert divisor < n
            if divisor > 1:
                return finish("exact-order-prime-factor", factor=divisor)
        next_modulus = math.lcm(modulus, order)
        metrics["lcm_updates"] += 1
        assert next_modulus >= 2*modulus
        stage["next_modulus"] = next_modulus
        modulus = next_modulus


def check_route(actual, p, q):
    """Independent validation, outside every public call and its timing."""
    from sympy import n_order

    n, width = p*q, actual["width"]
    assert actual["N"] == n and (width-1)**6 < n <= width**6
    assert not actual["status"].startswith("unresolved")
    if actual["factor"] is not None:
        assert actual["factor"] in (p, q)
    else:
        assert actual["status"] == "certified-large-order"
        base = actual["large_base"]
        if p == q:
            reference_order = int(n_order(base, n))
        else:
            reference_order = math.lcm(int(n_order(base, p)), int(n_order(base, q)))
        assert reference_order > actual["order_cap"]
    for stage in actual["stages"]:
        modulus = stage["modulus"]
        assert modulus < width and (p-1) % modulus == (q-1) % modulus == 0
        assert pow(stage["base"], modulus, n) != 1
        assert stage["base"] <= modulus+1
        if "derived_order" in stage:
            assert stage["derived_order"] == int(n_order(stage["base"], n))
        if "next_modulus" in stage:
            new = stage["next_modulus"]
            assert new >= 2*modulus and (p-1) % new == (q-1) % new == 0


def validate():
    from sympy import primerange

    primes = list(primerange(2, 200))
    cases, factors, large, squares, extensions, max_stages = 0, 0, 0, 0, 0, 0
    for index, p in enumerate(primes):
        for q in primes[index:]:
            actual = public_route(p*q)
            check_route(actual, p, q)
            cases += 1
            factors += int(actual["factor"] is not None)
            large += int(actual["large_base"] is not None)
            squares += int(p == q)
            extensions += actual["metrics"]["lcm_updates"]
            max_stages = max(max_stages, len(actual["stages"]))
    controls = []
    for p, q in ((13367, 164511353), (59, 233), (2207, 6619), (29, 101), (17, 41)):
        actual = public_route(p*q)
        check_route(actual, p, q)
        actual.update(reference_p=p, reference_q=q)
        controls.append(actual)
    assert controls[0]["status"] == "certified-large-order"
    assert controls[0]["seed_moduli"] == [1, 41]
    assert [stage["base"] for stage in controls[0]["stages"]] == [2, 3]
    assert controls[0]["large_base"] == 3
    prior = PEELING["factor_collision"](controls[0]["N"], 2)
    assert prior["status"] == "unresolved-small-order" and prior["certified_order"] == 41
    return dict(semiprime_cases=cases, proper_factors=factors, certified_large_units=large,
                prime_squares=squares, lcm_updates=extensions, maximum_seed_stages=max_stages,
                unresolved_cases=0, controls=controls, prior_small_order_control=prior)


def source_inventory():
    parent = json.loads((ROOT/PARENT).read_text())
    for path, expected in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT, "RiemannGaussian/SemiprimeSeedLcm.lean",
                  "scripts/CheckSemiprimeSeedLcm.lean", "scripts/probe_semiprime_seed_lcm.py",
                  "scripts/probe_semiprime_lehman_coverage.py", CORPUS))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources = source_inventory()
    validation = validate()
    inputs = []
    for previous in json.loads((ROOT/CORPUS).read_text())["inputs"]:
        actual = public_route(previous["N"])
        check_route(actual, previous["reference_p"], previous["reference_q"])
        actual.update(regime=previous["regime"], reference_p=previous["reference_p"],
                      reference_q=previous["reference_q"])
        inputs.append(actual)
    result = dict(replay_id=REPLAY_ID, scope="universal N-only factor-or-large-order seed routing",
                  is_complete_semiprime_factorizer=False, is_bit_complexity_certificate=False,
                  one_sixth_guarantee="OPEN", validation=validation, inputs=inputs,
                  input_count=len(inputs), factor_count=sum(c["factor"] is not None for c in inputs),
                  certified_large_count=sum(c["large_base"] is not None for c in inputs),
                  unresolved_count=sum(c["status"].startswith("unresolved") for c in inputs),
                  source_sha256=sources,
                  timing_protocol="All N-specific root/prefix work, seed scans and GCDs, every bounded lookup/sort, repeated trial factorizations, power reductions, prime-test residues/GCDs, LCM updates and any final progression polynomial are included. Independent reference orders and validation are outside timing.",
                  limitations="Above-cap units are certificates, not factors. Both large-kernel and large-nonkernel extraction remain open at sixth-root cost; the complete residue and bit backend is unproved. The tiny-input fallback is used only for N<=729. This deterministic replay generates no fresh random corpus.")
    assert result["unresolved_count"] == 0
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: result[k] for k in ("input_count", "factor_count", "certified_large_count", "unresolved_count", "one_sixth_guarantee")}, indent=2))
    print(json.dumps({k: v for k, v in validation.items() if k not in ("controls", "prior_small_order_control")}, indent=2))


if __name__ == "__main__":
    main()

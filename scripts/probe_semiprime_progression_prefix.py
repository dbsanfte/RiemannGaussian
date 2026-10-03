#!/usr/bin/env python3
"""Charged bounded order acquisition and a compressed common-modulus prefix.

Public routines receive N, a base and optional public widths. Global
collisions are retained by sorting and merging two lists; they are not
deflated away. All group powers, sorting, trial factors, GCD certificates
and progression polynomial work are charged. Orders beyond the cap and
small common orders remain unresolved. Optional research replay only.
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
COMMON = runpy.run_path(str(ROOT/"scripts/probe_semiprime_common_order.py"))
PREFIX, STAGED = COMMON["PREFIX"], COMMON["STAGED"]
PARENT = "docs/semiprime-common-order-audit.json"
REPLAY_ID = 202610030701


def progression_prefix(n, modulus, width):
    start = time.perf_counter()
    if n < 2 or modulus < 1 or width < 1:
        raise ValueError("positive modulus and width, N>=2 required")
    metrics = dict(polynomial_sources=0, root_residues=0, target_residues=0,
                   column_gcds=0, leaf_gcds=0, whole_modulus_columns=0,
                   lazy_integer_candidates=0, explicit_grid_candidates=0,
                   geometric_rows=0)
    result = dict(N=n, modulus=modulus, width=width, factor=None, metrics=metrics)
    if modulus*width*width+1 >= n:
        result.update(status="extent-outside-modulus", elapsed_ms=1000*(time.perf_counter()-start))
        return result
    batch = PREFIX["MonicBatch"](n)
    polynomial = batch.tree([(-(modulus*(i+1)+1)) % n for i in range(width)])[0]
    values = batch.evaluate(polynomial, [modulus*j*width % n for j in range(width)])
    metrics.update(polynomial_sources=1, root_residues=width, target_residues=width,
                   polynomial_coefficients=len(polynomial), **batch.stats())
    result["column_values"] = values
    factor = None
    for column, value in enumerate(values):
        metrics["column_gcds"] += 1
        divisor = math.gcd(n, value)
        if divisor == 1:
            continue
        if divisor == n:
            metrics["whole_modulus_columns"] += 1
            for offset in range(width):
                metrics["lazy_integer_candidates"] += 1
                leaf = modulus*(column*width+offset+1)+1
                assert 0 < leaf < n
                metrics["leaf_gcds"] += 1
                divisor = math.gcd(n, leaf)
                if 1 < divisor < n:
                    break
            else:
                raise AssertionError("nonunit block has no proper leaf")
        assert 1 < divisor < n and n % divisor == 0
        factor = divisor
        break
    metrics["gcd_calls"] = metrics["column_gcds"]+metrics["leaf_gcds"]
    assert metrics["gcd_calls"] <= 2*width
    assert metrics["whole_modulus_columns"] <= 1
    result.update(status="progression-factor" if factor else "progression-clear", factor=factor,
                  elapsed_ms=1000*(time.perf_counter()-start))
    return result


def sort_records(records, metrics):
    """Actual comparison merge sort; no hash-table or hidden order oracle."""
    if len(records) <= 1:
        return records[:]
    middle = len(records)//2
    left = sort_records(records[:middle], metrics)
    right = sort_records(records[middle:], metrics)
    out, i, j = [], 0, 0
    while i < len(left) and j < len(right):
        metrics["sort_comparisons"] += 1
        if left[i][0] <= right[j][0]:
            out.append(left[i])
            i += 1
        else:
            out.append(right[j])
            j += 1
    return out+left[i:]+right[j:]


def bounded_power_collision(n, base, block):
    """Two length-block sources cover positive global orders <=block^2."""
    start = time.perf_counter()
    if block < 1 or math.gcd(n, base) != 1:
        raise ValueError("positive block and unit base required")
    metrics = dict(baby_records=block, giant_records=block,
                   unit_gcds=1,
                   modular_powers=1, modular_multiplications=0,
                   sort_comparisons=0, merge_comparisons=0,
                   cartesian_pair_candidates=0)
    babies, value = [], 1
    for i in range(block):
        babies.append((value, i))
        if i+1 < block:
            value = value*base % n
            metrics["modular_multiplications"] += 1
    step = pow(base, block, n)
    giants, value = [], step
    for j in range(1, block+1):
        giants.append((value, j))
        if j < block:
            value = value*step % n
            metrics["modular_multiplications"] += 1
    babies = sort_records(babies, metrics)
    giants = sort_records(giants, metrics)
    i = j = 0
    match = None
    while i < block and j < block:
        metrics["merge_comparisons"] += 1
        if babies[i][0] == giants[j][0]:
            match = dict(baby_index=babies[i][1], giant_index=giants[j][1],
                         value=babies[i][0])
            match["annihilator"] = match["giant_index"]*block-match["baby_index"]
            assert 0 < match["annihilator"] <= block*block
            break
        if babies[i][0] < giants[j][0]:
            i += 1
        else:
            j += 1
    assert metrics["merge_comparisons"] <= 2*block
    assert metrics["modular_multiplications"] == 2*(block-1)
    result = dict(N=n, base=base, block=block, order_cap=block*block,
                  match=match, metrics=metrics,
                  elapsed_ms=1000*(time.perf_counter()-start))
    return result


def bounded_order_pass(n, base, width=None):
    """Factor or certify a bounded common order; retain every failure."""
    start = time.perf_counter()
    width = PREFIX["sixth_width"](n) if width is None else width
    if n < 4 or width < 1:
        raise ValueError("N>=4 and positive width required")
    result = dict(N=n, base=base, width=width, factor=None, power_trace=[])
    metrics = dict(square_root_queries=1, base_gcds=0, order_powers=0, order_gcds=0,
                   trial_divisor_tests=0, trial_strip_divisions=0,
                   certificate_powers=0, certificate_gcds=0,
                   reconstruction_square_roots=0, reconstruction_gcds=0, geometric_rows=0)
    result["metrics"] = metrics

    def finish(status, factor=None):
        if factor is not None:
            assert 1 < factor < n and n % factor == 0
        result.update(status=status, factor=factor, elapsed_ms=1000*(time.perf_counter()-start))
        return result

    root = math.isqrt(n)
    if root*root == n and 1 < root < n:
        return finish("square-factor", root)
    prefix = PREFIX["factor_prefix"](n, width)
    result["prefix"] = prefix
    if prefix["factor"] is not None:
        return finish("prefix-factor", prefix["factor"])
    metrics["base_gcds"] += 1
    divisor = math.gcd(n, base)
    if 1 < divisor < n:
        return finish("base-factor", divisor)
    if divisor != 1:
        return finish("nonunit-base")
    collision = bounded_power_collision(n, base, 2*width)
    result["collision"] = collision
    if collision["match"] is None:
        return finish("bounded-order-exhausted")
    exponent = collision["match"]["annihilator"]
    # This exponent is a derived public collision distance, rather than
    # a hidden numerical order or a proposed divisor of N-1.
    metrics["certificate_powers"] += 1
    assert pow(base, exponent, n) == 1
    factors = COMMON["trial_factors"](exponent, metrics)
    result["annihilator_factors"] = factors
    for prime in sorted(factors):
        while exponent % prime == 0:
            metrics["order_powers"] += 1
            power = pow(base, exponent//prime, n)
            metrics["order_gcds"] += 1
            divisor = math.gcd(n, power-1)
            result["power_trace"].append(dict(exponent=exponent, divisor=prime,
                                               value=power, gcd=divisor))
            if 1 < divisor < n:
                return finish("bounded-order-power-factor", divisor)
            if divisor == 1:
                break
            exponent //= prime
    prime_divisors = [p for p in sorted(factors) if exponent % p == 0]
    metrics["certificate_powers"] += 1
    assert pow(base, exponent, n) == 1
    for prime in prime_divisors:
        metrics["certificate_powers"] += 1
        power = pow(base, exponent//prime, n)
        metrics["certificate_gcds"] += 1
        assert math.gcd(n, power-1) == 1
    result.update(certified_order=exponent, order_prime_divisors=prime_divisors,
                  progression_size_bound=width <= exponent)
    if width > exponent:
        return finish("unresolved-small-order")
    metrics["reconstruction_square_roots"] += 1
    candidate = COMMON["wrapped_candidate"](n, exponent, 0)
    metrics["reconstruction_gcds"] += 1
    divisor = math.gcd(n, candidate)
    if 1 < divisor < n:
        return finish("bounded-common-order-factor", divisor)
    progression = progression_prefix(n, exponent, width)
    result["progression"] = progression
    if progression["factor"] is not None:
        return finish("bounded-progression-factor", progression["factor"])
    return finish("unresolved-progression")


def public_pass(n, scan_cap=None):
    start = time.perf_counter()
    previous = COMMON["public_pass"](n, scan_cap)
    result = dict(N=n, width=previous["width"], factor=previous["factor"],
                  status=previous["status"], prior_pass=previous)
    if previous["factor"] is None and "staged_pass" in previous:
        screened = previous["staged_pass"].get("raw_screen", {}).get("screened", [])
        kernels = [e["base"] for e in screened if e["status"] == "raw-kernel"]
        if kernels:
            attempted = bounded_order_pass(n, kernels[0], previous["width"])
            result.update(bounded_order_pass=attempted, status=attempted["status"],
                          factor=attempted["factor"])
    result["elapsed_ms"] = 1000*(time.perf_counter()-start)
    return result


def validate():
    from sympy import divisors, factorint, n_order, primerange
    column_comparisons = saturated_columns = 0
    for n in range(5, 129):
        for modulus in range(1, 7):
            for width in range(1, math.isqrt((n-2)//modulus)+1):
                actual = progression_prefix(n, modulus, width)
                expected = [math.prod(modulus*(j*width+i+1)+1 for i in range(width)) % n
                            for j in range(width)]
                assert actual["column_values"] == expected
                whole = math.prod(modulus*k+1 for k in range(1, width*width+1))
                assert (actual["factor"] is None) == (math.gcd(n, whole) == 1)
                column_comparisons += 1
                saturated_columns += actual["metrics"]["whole_modulus_columns"]
    order_comparisons = exhausted_orders = nonexact_distances = 0
    for n in range(4, 161):
        for base in range(2, min(n, 10)):
            if math.gcd(base, n) != 1:
                continue
            order = int(n_order(base, n))
            for block in range(1, 9):
                result = bounded_power_collision(n, base, block)
                assert (result["match"] is not None) == (order <= block*block)
                if result["match"] is not None:
                    distance = result["match"]["annihilator"]
                    assert distance % order == 0 and pow(base, distance, n) == 1
                    nonexact_distances += int(distance != order)
                else:
                    exhausted_orders += 1
                assert result["metrics"]["sort_comparisons"] <= 2*block*math.ceil(math.log2(block))
                order_comparisons += 1
    covered_common_moduli = 0
    primes = list(primerange(3, 250))
    for index, p in enumerate(primes):
        for q in primes[index:]:
            n, width = p*q, PREFIX["sixth_width"](p*q)
            if p <= width*width:
                continue
            for modulus in divisors(math.gcd(p-1, q-1)):
                if modulus < width:
                    continue
                actual = progression_prefix(n, modulus, width)
                assert actual["factor"] is not None and actual["metrics"]["gcd_calls"] <= 2*width
                covered_common_moduli += 1
    bounded_unit_cases = bounded_power_factors = bounded_nonkernel_cases = 0
    small_primes = list(primerange(5, 110))
    for index, p in enumerate(small_primes):
        for q in small_primes[index+1:]:
            n, width = p*q, PREFIX["sixth_width"](p*q)
            if p <= width*width:
                continue
            for base in range(2, 10):
                if math.gcd(n, base) != 1:
                    continue
                order = int(n_order(base, n))
                if not (width <= order <= 4*width*width):
                    continue
                actual = bounded_order_pass(n, base)
                assert actual["factor"] is not None
                bounded_unit_cases += 1
                bounded_power_factors += int(actual["status"] == "bounded-order-power-factor")
                bounded_nonkernel_cases += int(pow(base, n-1, n) != 1)
    controls = [bounded_order_pass(n, base) for n, base in
                ((2929, 2535), (13747, 4), (1373653, 3), (769841, 508038),
                 (697, 696), (14608133, 64))]
    assert controls[0]["certified_order"] == 4 and controls[0]["factor"] == 29
    assert controls[0]["status"] == "bounded-progression-factor"
    assert controls[1]["certified_order"] == 29 and controls[1]["factor"] == 59
    assert controls[2]["certified_order"] == 207 and controls[2]["factor"] == 829
    assert controls[3]["certified_order"] == 40 and controls[3]["factor"] == 641
    assert controls[4]["certified_order"] == 2 and controls[4]["status"] == "unresolved-small-order"
    assert controls[5]["status"] == "bounded-order-exhausted" and controls[5]["factor"] is None
    assert int(n_order(64, 14608133)) == 1103 > controls[5]["collision"]["order_cap"]
    prior_controls = [COMMON["kernel_rescue"](2929, 2535), COMMON["kernel_rescue"](13747, 4)]
    assert [c["status"] for c in prior_controls] == ["unresolved-common-order", "unresolved-rough-order"]
    for control in controls:
        if "certified_order" in control:
            assert int(n_order(control["base"], control["N"])) == control["certified_order"]
        if "annihilator_factors" in control:
            actual = {int(p): int(e) for p, e in factorint(control["collision"]["match"]["annihilator"]).items()}
            assert control["annihilator_factors"] == actual
        assert control["metrics"]["geometric_rows"] == 0
    saturated = progression_prefix(35, 2, 3)
    assert saturated["factor"] == 5 and saturated["metrics"]["whole_modulus_columns"] == 1
    return dict(exact_progression_batches=column_comparisons, saturated_progression_recoveries=saturated_columns,
                bounded_order_comparisons=order_comparisons, exhausted_order_comparisons=exhausted_orders,
                nonexact_collision_distances=nonexact_distances, covered_common_moduli=covered_common_moduli,
                bounded_unit_cases=bounded_unit_cases, bounded_power_factors=bounded_power_factors,
                bounded_nonkernel_cases=bounded_nonkernel_cases,
                controls=controls, prior_unresolved_controls=prior_controls, saturated_control=saturated,
                literal_base_provenance="2535 and 508038 are offline diagnostics; 4, 3, -1 and 64 are public literal controls. No universal base-menu coverage is inferred.")


def source_inventory():
    parent = json.loads((ROOT/PARENT).read_text())
    for path, expected in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT, "RiemannGaussian/SemiprimeProgressionPrefix.lean",
                  "scripts/CheckSemiprimeProgressionPrefix.lean",
                  "scripts/probe_semiprime_progression_prefix.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def replay():
    validation = validate()
    parent = json.loads((ROOT/PARENT).read_text())
    cases = []
    for prior in parent["inputs"]:
        actual = public_pass(prior["N"])
        baseline = COMMON["public_pass"](prior["N"])
        assert actual["factor"] is not None or baseline["factor"] is None
        actual.update(regime=prior["regime"], reference_p=prior["reference_p"],
                      reference_q=prior["reference_q"], fresh_common_order_baseline=baseline)
        cases.append(actual)
    return dict(replay_id=REPLAY_ID, scope="bounded global order acquisition and compressed common-modulus progression",
                is_complete_semiprime_factorizer=False, is_bit_complexity_certificate=False,
                one_sixth_guarantee="OPEN", validation=validation, inputs=cases,
                input_count=len(cases), recovered_count=sum(c["factor"] is not None for c in cases),
                summary={s: sum(c["status"] == s for c in cases) for s in sorted({c["status"] for c in cases})},
                source_sha256=source_inventory(),
                timing_protocol="Each bounded control includes square test, ordinary prefix, unit check, 2B baby/giant sources, both comparison sorts, merge, bounded trial factorization, every power/GCD certificate and any progression polynomial. Baselines are fresh separate passes. Independent oracle validation is outside timing.",
                limitations="Global orders above 4B^2 and common orders below B remain explicit. Seed-menu coverage, nonkernel residual acquisition and backend bit complexity are unproved. Sorting and the runtime trial-factor loop are not a formal complete bit-cost implementation.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = replay()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: result[k] for k in
                      ("input_count", "recovered_count", "summary", "one_sixth_guarantee")}, indent=2))


if __name__ == "__main__":
    main()

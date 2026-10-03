#!/usr/bin/env python3
"""Charged N-only kernel handling with one smaller residual routing call.

All smooth factors are found using one retained additive prefix and small
integer trial division. An active rough kernel has prime common order. A
checked residual factor identifies that order through one modular power,
then one quadratic candidate recovers the original factor. A nonfactor
child stays explicit and retains both parent and active unit information.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
LOCAL = runpy.run_path(str(ROOT/"scripts/probe_semiprime_local_order_routing.py"))
COMMON = LOCAL["SEEDS"]["PEELING"]["PROGRESSION"]["COMMON"]
MonicBatch = LOCAL["BATCH"]["MonicBatch"]
PARENT = "docs/semiprime-local-order-routing-audit.json"
REPLAY_ID = 202610031101


def minimum_prime(value, metrics):
    if value <= 1:
        raise ValueError("minimal prime factor requires value>1")
    divisor = 2
    while divisor*divisor <= value:
        metrics["trial_divisor_tests"] += 1
        if value % divisor == 0:
            return divisor
        divisor += 1
    return value


def split_small(exponent, width):
    if exponent < 1 or width < 1:
        raise ValueError("positive exponent and width required")
    start = time.perf_counter()
    fuel = exponent.bit_length()
    metrics = dict(polynomial_sources=0, root_records=0, target_records=0,
                   column_gcds=0, leaf_gcds=0, recomputed_leaf_gcds=0,
                   trial_divisor_tests=0, prime_stages=0,
                   residual_divisions=0, explicit_grid_candidates=0)
    values, backend = [], {}
    if exponent > width*width:
        batch = MonicBatch(exponent)
        polynomial = batch.tree([(-(i+1)) % exponent for i in range(width)])[0]
        values = batch.evaluate(polynomial, [j*width for j in range(width)])
        metrics.update(polynomial_sources=1, root_records=width, target_records=width)
        backend = batch.stats()
    remaining, primes, trace = exponent, [], []
    for stage in range(fuel):
        if remaining <= 1:
            break
        before, before_trials = remaining, metrics["trial_divisor_tests"]
        record = dict(residual=remaining)
        if remaining <= width*width:
            prime = minimum_prime(remaining, metrics)
            record["kind"] = "small-trial-tail"
        else:
            for column, value in enumerate(values):
                metrics["column_gcds"] += 1
                if math.gcd(remaining, value) != 1:
                    break
            else:
                record.update(kind="certified-rough", columns=len(values))
                trace.append(record)
                break
            for offset in range(width):
                leaf = column*width+offset+1
                metrics["leaf_gcds"] += 1
                if math.gcd(remaining, leaf) > 1:
                    break
            else:
                raise AssertionError("nonunit retained block has no nonunit leaf")
            metrics["recomputed_leaf_gcds"] += 1
            divisor = math.gcd(remaining, leaf)
            assert 1 < divisor <= width*width
            prime = minimum_prime(divisor, metrics)
            record.update(kind="retained-column-leaf", column=column, leaf=leaf,
                          small_divisor=divisor)
        assert metrics["trial_divisor_tests"]-before_trials <= width
        assert 1 < prime <= width*width and remaining % prime == 0
        primes.append(prime)
        remaining //= prime
        metrics["residual_divisions"] += 1
        metrics["prime_stages"] += 1
        record.update(prime=prime, next_residual=remaining)
        trace.append(record)
        assert remaining < before
    else:
        assert remaining == 1
    smooth = math.prod(primes)
    assert smooth*remaining == exponent and len(primes) <= fuel
    metrics["gcd_queries"] = (metrics["column_gcds"]+metrics["leaf_gcds"]+
                              metrics["recomputed_leaf_gcds"])
    assert metrics["gcd_queries"] <= (2*width+1)*fuel
    return dict(exponent=exponent, width=width, fuel=fuel, residual=remaining,
                primes=primes, smooth=smooth, retained_values=values, trace=trace,
                metrics=metrics, polynomial_backend=backend,
                elapsed_ms=1000*(time.perf_counter()-start))


def order_from_primes(n, base, primes):
    """Public prime-list recursion; no numerical order or fresh factoring."""
    current, multiplier, queries, trace = base, 1, 0, []
    for i, prime in enumerate(primes):
        tail = math.prod(primes[i+1:])
        value = pow(current, tail, n)
        queries += 1
        trace.append(dict(prime=prime, tail_exponent=tail, value=value))
        if value != 1:
            current = pow(current, prime, n)
            queries += 1
            multiplier *= prime
    assert queries <= 2*len(primes)
    return multiplier, queries, trace


def public_route(n):
    start = time.perf_counter()
    previous = LOCAL["public_route"](n)
    width = previous["width"]
    metrics = dict(active_projection_powers=0, retained_prime_order_powers=0,
                   order_selection_powers=0, candidate_square_roots=0,
                   candidate_gcds=0, child_routing_calls=0,
                   explicit_grid_candidates=0)
    result = dict(N=n, width=width, previous_route=previous, factor=None,
                  status=previous["status"], metrics=metrics)

    def finish(status, factor=None):
        if factor is not None:
            assert 1 < factor < n and n % factor == 0
        assert metrics["child_routing_calls"] <= 1
        result.update(status=status, factor=factor,
                      elapsed_ms=1000*(time.perf_counter()-start))
        return result

    def recover(modulus, status):
        candidate = COMMON["wrapped_candidate"](n, modulus, 0)
        metrics["candidate_square_roots"] += 1
        metrics["candidate_gcds"] += 1
        divisor = math.gcd(n, candidate)
        result.update(selected_order=modulus, quadratic_candidate=candidate)
        if 1 < divisor < n:
            return finish(status, divisor)
        return finish("unresolved-quadratic-recovery")

    if previous["factor"] is not None:
        return finish(previous["status"], previous["factor"])
    if previous["status"] == "certified-projected-long":
        return finish("certified-projected-long")
    if previous["status"] != "certified-large-kernel":
        return finish("unresolved-previous-route")
    base = previous["base"]
    split = split_small(n-1, width)
    result.update(base=base, split=split)
    metrics["active_projection_powers"] += 1
    alpha = pow(base, split["smooth"], n)
    result["active_base"] = alpha
    residual = split["residual"]
    if alpha == 1:
        order, queries, trace = order_from_primes(n, base, split["primes"])
        metrics["retained_prime_order_powers"] += queries
        result["order_trace"] = trace
        return recover(order, "smooth-kernel-factor")
    if residual <= width**4:
        return recover(residual, "rough-prime-kernel-factor")
    metrics["child_routing_calls"] += 1
    child = LOCAL["public_route"](residual)
    result["child_route"] = child
    assert 2*residual < n
    if child["factor"] is not None:
        divisor = child["factor"]
        metrics["order_selection_powers"] += 1
        value = pow(alpha, divisor, n)
        order = divisor if value == 1 else residual//divisor
        result["order_selection_value"] = value
        return recover(order, "residual-child-kernel-factor")
    return finish("certified-smaller-residual")


def check_route(actual, p, q):
    """Independent factor and order checks outside the charged routine."""
    from sympy import factorint, isprime, n_order

    n = p*q
    assert actual["N"] == n and not actual["status"].startswith("unresolved")
    LOCAL["check_route"](actual["previous_route"], p, q)
    if actual["factor"] is not None:
        assert actual["factor"] in (p,q)
    if "split" not in actual:
        return
    split = actual["split"]
    remaining, width = split["residual"], actual["width"]
    assert all(isprime(r) and r <= width*width for r in split["primes"])
    assert all(int(r) > width*width for r in factorint(remaining))
    alpha = actual["active_base"]
    if alpha == 1:
        assert actual["selected_order"] == int(n_order(actual["base"], n))
        return
    order = int(n_order(alpha, n))
    assert isprime(order) and order > width*width
    assert (p-1) % order == (q-1) % order == 0 and n < order**3
    if "child_route" in actual:
        fs = factorint(remaining)
        assert sum(fs.values()) == 2 and 2*remaining < n
        residual_primes = [int(r) for r,e in fs.items() for _ in range(e)]
        LOCAL["check_route"](actual["child_route"], *sorted(residual_primes))
    if actual["factor"] is not None:
        assert actual["selected_order"] == order


def validate():
    from sympy import factorint, n_order, primerange

    split_cases, order_cases = 0, 0
    for exponent in range(1, 513):
        width = LOCAL["SEEDS"]["PREFIX"]["sixth_width"](exponent+1)
        actual = split_small(exponent, width)
        assert all(p > width*width for p in factorint(actual["residual"]))
        assert all(factorint(p) == {p:1} for p in actual["primes"])
        split_cases += 1
    for modulus in range(2, 65):
        primes = [int(p) for p,e in factorint(math.factorial(modulus)).items() for _ in range(e)]
        for base in range(1, modulus):
            if math.gcd(base, modulus) != 1:
                continue
            order, _, _ = order_from_primes(modulus, base, primes)
            assert order == int(n_order(base, modulus))
            order_cases += 1
    primes = list(primerange(2, 200))
    counts = Counter()
    for i,p in enumerate(primes):
        for q in primes[i:]:
            actual = public_route(p*q)
            check_route(actual,p,q)
            counts[actual["status"]] += 1
    controls = []
    for p,q in ((29759,119033),(20543,61627),(13367,164511353),(2207,6619),
                (7681,15361),(14159,56633),(148199,592793)):
        actual = public_route(p*q)
        check_route(actual,p,q)
        actual.update(reference_p=p,reference_q=q)
        controls.append(actual)
    assert controls[0]["status"] == "residual-child-kernel-factor"
    assert controls[0]["factor"] == 29759 and controls[0]["split"]["residual"] == 590383841
    assert controls[0]["child_route"]["factor"] == 39679
    assert controls[0]["selected_order"] == 14879
    assert controls[1]["factor"] == 20543
    assert controls[4]["status"] == "smooth-kernel-factor"
    assert controls[4]["factor"] == 7681 and controls[4]["selected_order"] == 3840
    assert controls[4]["metrics"]["candidate_square_roots"] == 1
    assert controls[5]["status"] == "rough-prime-kernel-factor"
    assert controls[5]["factor"] == 14159 and controls[5]["split"]["residual"] == 7079
    assert controls[6]["status"] == "certified-smaller-residual"
    assert controls[6]["factor"] is None and controls[6]["split"]["residual"] == 14641888301
    assert controls[6]["child_route"]["status"] == "certified-projected-long"
    assert controls[6]["metrics"]["candidate_square_roots"] == 0
    prior = COMMON["kernel_rescue"](3542303047,2)
    assert prior["status"] == "unresolved-rough-order"
    return dict(split_cases=split_cases, retained_prime_order_cases=order_cases,
                semiprime_cases=sum(counts.values()), status_counts=dict(sorted(counts.items())),
                control_count=len(controls),
                control_status_counts=dict(sorted(Counter(x["status"] for x in controls).items())),
                control_discovery="Three fixed additional fixtures exercise the smooth, rough-prime, and pending-child branches. They were selected outside timing from prime families (2t+1,4t+1) with 2/3/5-smooth t, and (2r+1,8r+1) with prime r. No family search or reference order is used by the N-only routine.",
                controls=controls, prior_unresolved_control=prior)


def source_inventory():
    parent=json.loads((ROOT/PARENT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths=set(parent["source_sha256"])
    paths.update((PARENT,"RiemannGaussian/SemiprimeKernelResidual.lean",
                  "scripts/CheckSemiprimeKernelResidual.lean",
                  "scripts/probe_semiprime_kernel_residual.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    sources=source_inventory()
    validation=validate()
    inputs=[]
    for prior in json.loads((ROOT/PARENT).read_text())["inputs"]:
        actual=public_route(prior["N"])
        check_route(actual,prior["reference_p"],prior["reference_q"])
        actual.update(regime=prior["regime"],reference_p=prior["reference_p"],reference_q=prior["reference_q"])
        inputs.append(actual)
    result=dict(replay_id=REPLAY_ID,scope="N-only kernel factor-or-smaller-residual routing",
                is_complete_semiprime_factorizer=False,is_bit_complexity_certificate=False,
                one_sixth_guarantee="OPEN",validation=validation,inputs=inputs,
                input_count=len(inputs),factor_count=sum(x["factor"] is not None for x in inputs),
                summary=dict(sorted(Counter(x["status"] for x in inputs).items())),source_sha256=sources,
                timing_protocol="Every input-specific previous route, cached prefix construction, residual GCD/leaf scans, minimal-prime trial test, prime division, list-product construction, active and order powers, optional child public route, order selection, candidate square root and GCD is timed. Independent factor/order validation is outside timing.",
                limitations="A nonfactor child retains an explicit smaller-semiprime task; recursive solving and its full width/bit budget are not free. Original projected-long inputs are unchanged. Python target sorting and minimal-prime scan order can differ from the Lean specification, while preserving the proven contracts. No fresh random corpus is generated.")
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:result[k] for k in ("input_count","factor_count","summary","one_sixth_guarantee")},indent=2))
    print(json.dumps({k:v for k,v in validation.items() if k not in ("controls","prior_unresolved_control")},indent=2))


if __name__=="__main__":
    main()

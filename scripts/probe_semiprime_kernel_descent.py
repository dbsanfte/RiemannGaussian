#!/usr/bin/env python3
"""N-only complete kernel descent, retaining all parent transport carriers.

An already computed child route is reused by the preceding kernel handler.
No child factoring oracle or numerical order enters the timed procedure.
The remaining projected-long leaf is explicit; this is not a factorizer.
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
PARENT = "docs/semiprime-kernel-residual-audit.json"
KERNEL = runpy.run_path(str(ROOT/"scripts/probe_semiprime_kernel_residual.py"))
LOCAL = KERNEL["LOCAL"]
REPLAY_ID = 202610031201


def extend_existing(n, route, metrics):
    """Reuse one actual route while charging any new child routing call.

    The adapter supplies the actual current result to the old wrapper's
    initial route request. Its subsequent smaller-input request executes
    the real public router. The hook is local and restored before descent.
    """
    original = LOCAL["public_route"]

    def existing_or_child(value):
        if value == n:
            metrics["reused_current_routes"] += 1
            return route
        metrics["local_routing_calls"] += 1
        child = original(value)
        metrics["routing_and_kernel_width_slots"] += child["width"]
        return child

    LOCAL["public_route"] = existing_or_child
    try:
        actual = KERNEL["public_route"](n)
    finally:
        LOCAL["public_route"] = original
    return actual


def descend(n, route, fuel, metrics):
    if fuel == 0:
        return dict(N=n,kind="unresolved",route=route)
    metrics["descent_levels"] += 1
    metrics["descended_width"] += route["width"]
    metrics["prefix_allowance"] += (2*route["width"]+1)*n.bit_length()
    if route["factor"] is not None:
        return dict(N=n,kind="factor",factor=route["factor"],route=route)
    if route["status"] == "certified-projected-long":
        return dict(N=n,kind="projected-long",route=route)
    if route["status"] != "certified-large-kernel":
        return dict(N=n,kind="unresolved",route=route)
    metrics["kernel_handlers"] += 1
    metrics["routing_and_kernel_width_slots"] += route["width"]
    actual = extend_existing(n, route, metrics)
    metrics["small_prime_gcds"] += actual["split"]["metrics"]["gcd_queries"]
    metrics["handler_candidate_queries"] += actual["metrics"]["candidate_gcds"]
    if actual["factor"] is not None:
        return dict(N=n,kind="factor",factor=actual["factor"],route=route,kernel=actual)
    if actual["status"] != "certified-smaller-residual":
        return dict(N=n,kind="unresolved",route=route,kernel=actual)
    residual = actual["split"]["residual"]
    assert 2*residual < n
    child = descend(residual, actual["child_route"], fuel-1, metrics)
    return dict(N=n,kind="child",route=route,kernel=actual,child=child)


def recovered_factor(trace, metrics):
    if trace["kind"] == "factor":
        return trace["factor"]
    if trace["kind"] != "child":
        return None
    factor = recovered_factor(trace["child"], metrics)
    if factor is None:
        return None
    n, residual = trace["N"], trace["child"]["N"]
    active = trace["kernel"]["active_base"]
    value = pow(active, factor, n)
    order = factor if value == 1 else residual//factor
    candidate = KERNEL["COMMON"]["wrapped_candidate"](n, order, 0)
    divisor = math.gcd(n, candidate)
    metrics["trace_recovery_calls"] += 1
    metrics["trace_order_powers"] += 1
    metrics["trace_candidate_square_roots"] += 1
    metrics["trace_candidate_gcds"] += 1
    trace["transport"] = dict(child_factor=factor,order_selection_value=value,
                              selected_order=order,candidate=candidate,factor=divisor)
    assert 1 < divisor < n and n % divisor == 0
    return divisor


def public_trace(n):
    start = time.perf_counter()
    if n < 4:
        raise ValueError("semiprime input N>=4 required")
    metrics = dict(local_routing_calls=1,reused_current_routes=0,descent_levels=0,
                   kernel_handlers=0,descended_width=0,routing_and_kernel_width_slots=0,
                   prefix_allowance=0,small_prime_gcds=0,handler_candidate_queries=0,
                   trace_recovery_calls=0,trace_order_powers=0,
                   trace_candidate_square_roots=0,trace_candidate_gcds=0,
                   explicit_grid_candidates=0)
    initial = LOCAL["public_route"](n)
    width, fuel = initial["width"], n.bit_length()
    metrics["routing_and_kernel_width_slots"] += width
    trace = descend(n, initial, fuel, metrics)
    factor = recovered_factor(trace, metrics)
    leaf = trace
    while leaf["kind"] == "child":
        leaf = leaf["child"]
    assert metrics["descent_levels"] <= fuel
    assert metrics["descended_width"] <= width*fuel
    assert metrics["routing_and_kernel_width_slots"] <= 3*metrics["descended_width"]
    assert metrics["small_prime_gcds"] <= metrics["prefix_allowance"]
    assert metrics["prefix_allowance"] <= (2*width+1)*fuel*fuel
    assert metrics["trace_recovery_calls"] <= metrics["descent_levels"]
    assert metrics["handler_candidate_queries"] <= metrics["kernel_handlers"]
    return dict(N=n,width=width,fuel=fuel,trace=trace,metrics=metrics,factor=factor,
                status="factor" if factor is not None else leaf["kind"],
                leaf_input=leaf["N"],leaf_base=leaf["route"].get("base"),
                elapsed_ms=1000*(time.perf_counter()-start))


def check_trace(actual, p, q):
    """Independent literal route/order/factor validation outside timing."""
    from sympy import factorint,n_order

    assert actual["N"] == p*q and actual["status"] in ("factor","projected-long")
    if actual["factor"] is not None:
        assert actual["factor"] in (p,q)
    node = actual["trace"]
    while True:
        primes = [int(r) for r,e in factorint(node["N"]).items() for _ in range(e)]
        assert len(primes) == 2
        LOCAL["check_route"](node["route"], *sorted(primes))
        if "kernel" in node:
            KERNEL["check_route"](node["kernel"], *sorted(primes))
        if node["kind"] != "child":
            assert node["kind"] in ("factor","projected-long")
            assert node["N"] == actual["leaf_input"] <= actual["N"]
            break
        assert 2*node["child"]["N"] < node["N"]
        if "transport" in node:
            assert node["transport"]["selected_order"] == int(n_order(node["kernel"]["active_base"],node["N"]))
        node = node["child"]


def source_inventory():
    parent = json.loads((ROOT/PARENT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT,"RiemannGaussian/SemiprimeKernelDescent.lean",
                  "scripts/CheckSemiprimeKernelDescent.lean",
                  "scripts/probe_semiprime_kernel_descent.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def main():
    from sympy import primerange

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    sources = source_inventory()
    parent = json.loads((ROOT/PARENT).read_text())
    counts, max_depth = Counter(), 0
    primes = list(primerange(2,200))
    for i,p in enumerate(primes):
        for q in primes[i:]:
            actual = public_trace(p*q)
            check_trace(actual,p,q)
            counts[actual["status"]] += 1
            max_depth = max(max_depth,actual["metrics"]["descent_levels"])
    populations = {}
    for name, prior_inputs in (("inputs",parent["inputs"]),
                               ("controls",parent["validation"]["controls"])):
        population = []
        for prior in prior_inputs:
            actual = public_trace(prior["N"])
            check_trace(actual,prior["reference_p"],prior["reference_q"])
            actual.update(reference_p=prior["reference_p"],reference_q=prior["reference_q"])
            if "regime" in prior:
                actual["regime"] = prior["regime"]
            population.append(actual)
        populations[name] = population
    assert populations["controls"][0]["factor"] == 29759
    assert populations["controls"][1]["factor"] == 20543
    pending = populations["controls"][6]
    assert pending["status"] == "projected-long" and pending["factor"] is None
    assert pending["leaf_input"] == 14641888301 and pending["metrics"]["descent_levels"] == 2
    assert pending["metrics"]["local_routing_calls"] == 2
    assert pending["metrics"]["reused_current_routes"] == 1
    assert pending["metrics"]["descended_width"] == 117
    result = dict(replay_id=REPLAY_ID,scope="N-only complete kernel descent to factor or projected-long leaf",
                  one_sixth_guarantee="OPEN",is_complete_semiprime_factorizer=False,
                  is_bit_complexity_certificate=False,source_sha256=sources,
                  validation=dict(semiprime_cases=sum(counts.values()),status_counts=dict(counts),
                                  max_small_case_depth=max_depth,control_count=len(populations["controls"])),
                  summary=dict(sorted(Counter(x["status"] for x in populations["inputs"]).items())),
                  timing_protocol="Initial and new child public routing, kernel cached split and retained-prime powers, trace construction, all successful handler recovery, and every downstream transport power, square root and GCD are timed. Each actual child route is reused; no reference factorization or order enters the routine. Independent route/order/factor checks are outside timing.",
                  limitations="The projected-long leaf remains unsolved. Base-width slots and small-prime query allowances do not certify full source construction or bit complexity. Fixed regressions exercise an immediate child factor and one descent to a long leaf; universal multi-kernel termination is a Lean theorem, not a benchmark coverage claim.",
                  **populations)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(dict(summary=result["summary"],validation=result["validation"],
                          source_pins=len(sources),one_sixth_guarantee="OPEN",
                          pending_leaf=pending["leaf_input"],pending_metrics=pending["metrics"]),indent=2))


if __name__ == "__main__":
    main()

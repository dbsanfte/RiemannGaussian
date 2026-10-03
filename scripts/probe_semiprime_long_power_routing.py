#!/usr/bin/env python3
"""Public N/N+1 short refinement of the retained kernel-descent leaf.

The timed routine accepts N only and keeps every parent transport frame.
No numerical order or reference factor enters it. An unresolved long leaf
is retained explicitly; this is neither a complete factorizer nor a bit
complexity certificate.
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
PARENT = "docs/semiprime-kernel-descent-audit.json"
DESCENT = runpy.run_path(str(ROOT/"scripts/probe_semiprime_kernel_descent.py"))
LOCAL = DESCENT["LOCAL"]
REPLAY_ID = 202610031301


def refine_long(n, width, base):
    """Regenerate the actual projection and charge all four possible tests."""
    metrics = dict(unit_gcds=1, projection_raw_powers=0, projection_stage_powers=0,
                   projection_exponent_queries=0, projection_exponent_bits=0,
                   n_power_queries=0, successor_multiplications=0, direct_gcds=0,
                   short_batches=0, short_source_powers=0,
                   short_source_multiplications=0, short_gcds=0,
                   maximum_roots=0, maximum_targets=0, explicit_grid_candidates=0)
    result = dict(N=n,width=width,base=base,metrics=metrics,channels=[])

    def finish(status, factor=None):
        metrics["all_refinement_gcds"] = (
            metrics["unit_gcds"]+metrics["direct_gcds"]+metrics["short_gcds"])
        assert metrics["all_refinement_gcds"] <= 8*width+3
        assert metrics["short_batches"] <= 2
        assert metrics["maximum_roots"] <= 2*width
        assert metrics["maximum_targets"] <= 2*width
        result.update(status=status,factor=factor)
        return result

    if math.gcd(base,n) != 1:
        return finish("unresolved-nonunit")
    alpha = pow(base,n-1,n)
    metrics["projection_raw_powers"] += 1
    repetitions = n.bit_length()
    for stage in range(1,width+1):
        exponent = stage**repetitions
        metrics["projection_exponent_queries"] += 1
        metrics["projection_exponent_bits"] += exponent.bit_length()
        alpha = pow(alpha,exponent,n)
        metrics["projection_stage_powers"] += 1
    result["active_base"] = alpha
    value = pow(alpha,n,n)
    metrics["n_power_queries"] += 1
    for channel in ("N","N+1"):
        if channel == "N+1":
            value = value*alpha % n
            metrics["successor_multiplications"] += 1
        divisor = math.gcd((value-1) % n,n)
        metrics["direct_gcds"] += 1
        data = dict(channel=channel,value=value,direct_gcd=divisor)
        result["channels"].append(data)
        if 1 < divisor < n:
            return finish(channel+"-direct-factor",divisor)
        batch = LOCAL["short_batch"](n,value,2*width)
        data["short_batch"] = batch
        metrics["short_batches"] += 1
        construction = batch["construction"]
        metrics["short_source_powers"] += construction["modular_powers"]
        metrics["short_source_multiplications"] += construction["modular_multiplications"]
        metrics["short_gcds"] += batch["metrics"]["gcd_calls"]
        metrics["maximum_roots"] = max(metrics["maximum_roots"],construction["root_records"])
        metrics["maximum_targets"] = max(metrics["maximum_targets"],construction["target_records"])
        assert batch["metrics"]["pair_products"] == 0
        if batch["factor"] is not None:
            return finish(channel+"-short-factor",batch["factor"])
    return finish("strengthened-long")


def lift_factor(trace, factor, metrics):
    """Lift only a new proper leaf factor through the existing active units."""
    n = trace["N"]
    if trace["kind"] == "factor":
        return trace["factor"]
    if trace["kind"] == "projected-long":
        divisor = math.gcd(n,factor)
        metrics["leaf_candidate_gcds"] += 1
        assert 1 < divisor < n
        return divisor
    assert trace["kind"] == "child"
    child_factor = lift_factor(trace["child"],factor,metrics)
    residual = trace["child"]["N"]
    active = trace["kernel"]["active_base"]
    value = pow(active,child_factor,n)
    order = child_factor if value == 1 else residual//child_factor
    candidate = DESCENT["KERNEL"]["COMMON"]["wrapped_candidate"](n,order,0)
    divisor = math.gcd(n,candidate)
    metrics["transport_order_powers"] += 1
    metrics["transport_square_roots"] += 1
    metrics["transport_gcds"] += 1
    trace["leaf_transport"] = dict(child_factor=child_factor,order_selection_value=value,
                                   selected_order=order,candidate=candidate,factor=divisor)
    assert 1 < divisor < n and n % divisor == 0
    return divisor


def public_packet(n):
    """One complete N-only descent followed by one actual leaf refinement."""
    start = time.perf_counter()
    source = DESCENT["public_trace"](n)
    node = source["trace"]
    while node["kind"] == "child":
        node = node["child"]
    metrics = dict(leaf_refinement_calls=0,leaf_candidate_gcds=0,
                   transport_order_powers=0,transport_square_roots=0,transport_gcds=0)
    if node["kind"] == "factor":
        leaf = dict(N=node["N"],status="existing-factor",factor=node["factor"])
    else:
        assert node["kind"] == "projected-long"
        metrics["leaf_refinement_calls"] += 1
        leaf = refine_long(node["N"],node["route"]["width"],node["route"]["base"])
    factor = source["factor"]
    if factor is None and leaf["factor"] is not None:
        factor = lift_factor(source["trace"],leaf["factor"],metrics)
    if factor is not None:
        assert 1 < factor < n and n % factor == 0
    else:
        assert leaf["status"] == "strengthened-long"
    assert metrics["transport_order_powers"] <= source["metrics"]["descent_levels"]
    assert metrics["leaf_candidate_gcds"] <= 1
    return dict(N=n,width=source["width"],source=source,leaf=leaf,factor=factor,
                status="factor" if factor is not None else "strengthened-long",
                metrics=metrics,elapsed_ms=1000*(time.perf_counter()-start))


def check_packet(actual, p, q):
    """Independent factor, local order and known-order decoding checks."""
    from sympy import factorint,n_order

    assert actual["N"] == p*q
    DESCENT["check_trace"](actual["source"],p,q)
    if actual["factor"] is not None:
        assert actual["factor"] in (p,q)
    leaf = actual["leaf"]
    node = actual["source"]["trace"]
    while node["kind"] == "child":
        if "leaf_transport" in node:
            assert node["leaf_transport"]["selected_order"] == int(
                n_order(node["kernel"]["active_base"],node["N"]))
        node = node["child"]
    assert leaf["N"] == node["N"] <= actual["N"]
    if leaf["status"] == "existing-factor":
        return
    assert leaf["active_base"] == node["route"]["projection"]["final_alpha"]
    primes = sorted(int(r) for r,e in factorint(leaf["N"]).items() for _ in range(e))
    assert len(primes) == 2
    lp,lq = primes
    alpha,cap = leaf["active_base"],(2*leaf["width"])**2
    ap,aq = int(n_order(alpha,lp)),int(n_order(alpha,lq))
    assert ap > cap and aq > cap and math.gcd(ap,aq) == 1
    order = math.lcm(ap,aq)
    assert ((lp-1)*(lq-1)) % order == 0 and lp+lq < order
    assert math.gcd(order,leaf["N"]-1) == 1
    signal = (leaf["N"]+1) % order
    assert signal == lp+lq
    candidate = (signal-math.isqrt(signal*signal-4*leaf["N"]))//2
    assert candidate == lp and math.gcd(candidate,leaf["N"]) == lp
    # These reference values are validation, never inputs to public_packet.
    actual["known_order_reference"] = dict(local_p=lp,local_q=lq,left_order=ap,
                                           right_order=aq,global_order=order,
                                           factor_sum_signal=signal,decoded_factor=candidate,
                                           order_acquisition="outside timed routine")
    if leaf["factor"] is not None:
        assert leaf["factor"] in (lp,lq)
    else:
        assert leaf["status"] == "strengthened-long"
        assert all(c["short_batch"]["factor"] is None for c in leaf["channels"])
        assert math.gcd(order,leaf["N"]) == 1
        assert math.gcd(ap,leaf["N"]+1) == 1


def source_inventory():
    parent = json.loads((ROOT/PARENT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT,"RiemannGaussian/SemiprimeLongPowerRouting.lean",
                  "scripts/CheckSemiprimeLongPowerRouting.lean",
                  "scripts/probe_semiprime_long_power_routing.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def main():
    from sympy import primerange

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    sources = source_inventory()
    parent = json.loads((ROOT/PARENT).read_text())
    counts,squares = Counter(),0
    primes = list(primerange(2,200))
    for i,p in enumerate(primes):
        for q in primes[i:]:
            actual = public_packet(p*q)
            check_packet(actual,p,q)
            counts[actual["status"]] += 1
            squares += int(p == q)
    populations = {}
    for name in ("inputs","controls"):
        population = []
        for prior in parent[name]:
            actual = public_packet(prior["N"])
            check_packet(actual,prior["reference_p"],prior["reference_q"])
            actual.update(reference_p=prior["reference_p"],reference_q=prior["reference_q"])
            if "regime" in prior:
                actual["regime"] = prior["regime"]
            population.append(actual)
        populations[name] = population
    positive = []
    for p,q,status,factor in ((10163,20327,"N-direct-factor",20327),
                              (11483,22963,"N+1-direct-factor",11483)):
        actual = public_packet(p*q)
        check_packet(actual,p,q)
        actual.update(reference_p=p,reference_q=q)
        assert actual["source"]["status"] == "projected-long"
        assert actual["leaf"]["status"] == status and actual["factor"] == factor
        positive.append(actual)
    assert populations["controls"][0]["factor"] == 29759
    assert populations["controls"][1]["factor"] == 20543
    pending = populations["controls"][6]
    assert pending["factor"] is None and pending["leaf"]["N"] == 14641888301
    assert pending["source"]["metrics"]["descent_levels"] == 2
    assert pending["source"]["metrics"]["reused_current_routes"] == 1
    result = dict(replay_id=REPLAY_ID,scope="N-only complete descent with public power leaf refinement",
                  one_sixth_guarantee="OPEN",is_complete_semiprime_factorizer=False,
                  is_bit_complexity_certificate=False,source_sha256=sources,
                  validation=dict(semiprime_cases=sum(counts.values()),prime_squares=squares,
                                  status_counts=dict(counts),control_count=len(populations["controls"]),
                                  positive_power_control_count=len(positive)),
                  summary=dict(sorted(Counter(x["status"] for x in populations["inputs"]).items())),
                  positive_controls=positive,
                  positive_control_selection="Oracle-assisted discovery outside timing: cross family q=2p+1; successor family p=2r+1,q=4r-1. Only N is passed to each timed routine. These two selected examples are not an unbiased coverage or scaling sample.",
                  timing_protocol="The entire preceding public descent, projection regeneration from public leaf seed (B+1 modular powers plus B constructed exponents), N power, successor multiplication when reached, both direct GCDs, both possible short sources and all sorting/polynomial/deflation/witness/GCD work, packet retention and every successful factor transport are timed. Reference primality, factorization, local orders, global order and quadratic order decoder checks are outside timing.",
                  limitations="Known global order decodes the factor sum exactly, but obtaining it is not implemented or free. All three previous projected-long leaves survive both additional short batches. Linear source/GCD allowances are not a complete bit-cost certificate. The Python backend sorts targets, so universality of successful recovery rather than equality of first returned factors is the formal interface. No full pair matrix, random scaling corpus or tuned software baseline is generated.",
                  **populations)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(dict(summary=result["summary"],validation=result["validation"],
                          source_pins=len(sources),one_sixth_guarantee="OPEN",
                          positive_factors=[x["factor"] for x in positive],
                          surviving_leaf=pending["leaf"]["N"]),indent=2))


if __name__ == "__main__":
    main()

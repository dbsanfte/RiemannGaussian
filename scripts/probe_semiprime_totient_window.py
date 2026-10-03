#!/usr/bin/env python3
"""Retain global collision labels around a public quarter-totient centre.

Only N enters the timed routine. The active unit is reused from the
preceding public packet. No true order, totient, cofactor or reference
factor is supplied. A larger fixed control survives; no universal
one-sixth factorizer or complete bit-cost bound is claimed.
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
PARENT_AUDIT = "docs/semiprime-long-power-routing-audit.json"
PARENT = runpy.run_path(str(ROOT/"scripts/probe_semiprime_long_power_routing.py"))
SORTER = PARENT["LOCAL"]["SEEDS"]["PROGRESSION"]["sort_records"]
REPLAY_ID = 202610031401


def build_source(n, alpha, width):
    """Two actual sorted linear sources, keeping the first global match."""
    block = 2*width
    metrics = dict(centre_square_roots=1,modular_powers=2,modular_inverses=1,
                   modular_multiplications=0,baby_records=block,giant_records=block,
                   sort_comparisons=0,merge_comparisons=0,candidate_square_roots=0,
                   candidate_gcds=0,projection_regeneration_powers=0,
                   explicit_grid_candidates=0)
    centre = (n+1-2*math.isqrt(n))//4
    target = pow(alpha,centre,n)
    step = pow(pow(alpha,-1,n),block,n)
    babies,giants = [],[]
    baby,giant = 1,target
    for i in range(block):
        babies.append((baby,i))
        giants.append((giant,i))
        if i+1 < block:
            baby = baby*alpha % n
            giant = giant*step % n
            metrics["modular_multiplications"] += 2
    babies,giants = SORTER(babies,metrics),SORTER(giants,metrics)
    collision,i,j = None,0,0
    while i < block and j < block:
        metrics["merge_comparisons"] += 1
        if babies[i][0] == giants[j][0]:
            collision = dict(baby_index=babies[i][1],giant_index=giants[j][1],
                             value=babies[i][0],offset=block*giants[j][1]+babies[i][1])
            break
        if babies[i][0] < giants[j][0]:
            i += 1
        else:
            j += 1
    factor,candidate = None,None
    if collision is not None:
        modulus = max(centre-collision["offset"],0)
        signal = (n+1) % modulus if modulus > 0 else n+1
        discriminant = max(signal*signal-4*n,0)
        smaller = max(signal-math.isqrt(discriminant),0)//2
        metrics["candidate_square_roots"] += 1
        divisor = math.gcd(n,smaller)
        metrics["candidate_gcds"] += 1
        candidate = dict(modulus=modulus,sum_signal=signal,discriminant=discriminant,
                         smaller_candidate=smaller,gcd=divisor)
        if 1 < divisor < n:
            factor = divisor
    assert len(babies) == len(giants) == block
    assert metrics["merge_comparisons"] <= 2*block
    assert metrics["sort_comparisons"] <= 2*block*(block-1).bit_length()
    assert metrics["modular_multiplications"] == 2*(block-1)
    assert metrics["candidate_gcds"] <= 1
    return dict(N=n,width=width,block=block,active_base=alpha,centre=centre,target=target,
                inverse_step=step,babies=babies,giants=giants,collision=collision,
                candidate=candidate,factor=factor,metrics=metrics)


def public_packet(n):
    """Compute the preceding public packet once and reuse its rich leaf."""
    start = time.perf_counter()
    parent = PARENT["public_packet"](n)
    metrics = dict(leaf_candidate_gcds=0,transport_order_powers=0,
                   transport_square_roots=0,transport_gcds=0,new_source_calls=0)
    source = None
    factor = parent["factor"]
    if factor is None:
        leaf = parent["leaf"]
        assert leaf["status"] == "strengthened-long"
        source = build_source(leaf["N"],leaf["active_base"],leaf["width"])
        metrics["new_source_calls"] += 1
        if source["factor"] is not None:
            factor = PARENT["lift_factor"](parent["source"]["trace"],source["factor"],metrics)
    if factor is not None:
        assert 1 < factor < n and n % factor == 0
    else:
        assert source is not None and source["factor"] is None
    assert metrics["transport_order_powers"] <= parent["source"]["metrics"]["descent_levels"]
    return dict(N=n,width=parent["width"],parent=parent,source=source,factor=factor,
                status="factor" if factor is not None else "large-sum-gap",
                metrics=metrics,elapsed_ms=1000*(time.perf_counter()-start))


def check_packet(actual, p, q):
    """Validate literal orders, quarter-totient coverage and transports."""
    PARENT["check_packet"](actual["parent"],p,q)
    assert actual["N"] == p*q
    if actual["factor"] is not None:
        assert actual["factor"] in (p,q)
    source = actual["source"]
    if source is None:
        assert actual["parent"]["factor"] == actual["factor"]
        return
    reference = actual["parent"]["known_order_reference"]
    lp,lq = reference["local_p"],reference["local_q"]
    n,cap = source["N"],source["block"]**2
    phi = (lp-1)*(lq-1)
    assert phi % 4 == 0
    quarter = phi//4
    order = reference["global_order"]
    assert quarter % order == 0 and quarter > lp+lq
    assert order > cap
    offset = (lp+lq-2*math.isqrt(n))//4
    assert source["centre"] == quarter+offset
    covered = offset < cap
    actual["window_reference"] = dict(local_p=lp,local_q=lq,quarter_totient=quarter,
                                      global_order=order,cofactor=phi//order,
                                      true_offset=offset,offset_cap=cap,covered=covered,
                                      arithmetic_acquisition="outside timed routine")
    if covered:
        assert source["collision"] is not None
        assert source["collision"]["offset"] == offset
        assert source["candidate"]["modulus"] == quarter
        assert source["factor"] == lp
    if source["factor"] is not None:
        assert source["factor"] in (lp,lq)
    else:
        assert not covered and lp+lq-2*math.isqrt(n) >= 4*cap
    assert source["active_base"] == actual["parent"]["leaf"]["active_base"]
    assert source["block"] <= 2*actual["width"]


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeTotientWindow.lean",
                  "scripts/CheckSemiprimeTotientWindow.lean",
                  "scripts/probe_semiprime_totient_window.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def main():
    from sympy import primerange

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    sources = source_inventory()
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    counts,squares = Counter(),0
    primes = list(primerange(2,200))
    for i,p in enumerate(primes):
        for q in primes[i:]:
            actual = public_packet(p*q)
            check_packet(actual,p,q)
            counts[actual["status"]] += 1
            squares += int(p == q)
    populations = {}
    for name in ("inputs","controls","positive_controls"):
        population = []
        for prior in parent[name]:
            actual = public_packet(prior["N"])
            check_packet(actual,prior["reference_p"],prior["reference_q"])
            actual.update(reference_p=prior["reference_p"],reference_q=prior["reference_q"])
            if "regime" in prior:
                actual["regime"] = prior["regime"]
            population.append(actual)
        populations[name] = population
    new_hits = [x for x in populations["inputs"]+populations["controls"]
                if x["parent"]["factor"] is None and x["factor"] is not None]
    assert [x["source"]["collision"]["offset"] for x in new_hits] == [354,6515,7423]
    assert [x["factor"] for x in new_hits] == [44963,714107,148199]
    assert new_hits[2]["source"]["factor"] == 74099
    assert new_hits[2]["metrics"]["transport_order_powers"] == 1
    assert new_hits[2]["metrics"]["transport_gcds"] == 1
    p,q = 1000000007,1400000543
    negative = public_packet(p*q)
    check_packet(negative,p,q)
    negative.update(reference_p=p,reference_q=q)
    assert negative["status"] == "large-sum-gap" and negative["factor"] is None
    assert negative["source"]["collision"] is None
    assert negative["window_reference"]["true_offset"] == 8392042
    assert negative["window_reference"]["offset_cap"] == 4477456
    result = dict(replay_id=REPLAY_ID,scope="N-only labelled quarter-totient window after retained power descent",
                  one_sixth_guarantee="OPEN",is_complete_semiprime_factorizer=False,
                  is_bit_complexity_certificate=False,source_sha256=sources,
                  validation=dict(semiprime_cases=sum(counts.values()),prime_squares=squares,
                                  status_counts=dict(counts),new_window_factors=len(new_hits),
                                  control_count=len(populations["controls"]),
                                  prior_positive_control_count=len(populations["positive_controls"])),
                  summary=dict(sorted(Counter(x["status"] for x in populations["inputs"]).items())),
                  negative_controls=[negative],
                  negative_selection="First safe primes at or above twice 500000000 and twice 700000000 plus one, selected outside timing; only N is passed to the timed routine. Reference order and primality checks occur outside timing. This single selected larger example is not an asymptotic lower bound or random corpus.",
                  timing_protocol="The whole preceding public power packet and retained descent are timed. Each new source reuses its active unit, pays a new integer square root and centre, centre power, inverse and inverse-step power, both linear power lists, both actual comparison merge sorts, the ordered match, optional quadratic square root and GCD, packet retention and every successful leaf/parent transport. No projection regeneration, true order, totient, cofactor or reference factor is supplied to the new source. Independent coverage/order/primality/transport validation is outside timing.",
                  limitations="The covered offset is less than (2B)^2, and the new larger control survives. Closing three prior leaves proves neither universal coverage nor an asymptotic exponent. Source and merge bounds exclude a full pair matrix but do not supply the complete bit backend. The Python source uses cached geometric recurrences while Lean specifies the equal residue lists by public powers; their full bit implementation is not certified.",
                  **populations)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(dict(summary=result["summary"],validation=result["validation"],
                          source_pins=len(sources),new_factors=[x["factor"] for x in new_hits],
                          surviving_negative=negative["N"],one_sixth_guarantee="OPEN"),indent=2))


if __name__ == "__main__":
    main()

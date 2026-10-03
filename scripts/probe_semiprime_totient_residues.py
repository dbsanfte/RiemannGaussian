#!/usr/bin/env python3
"""Reuse quarter-window records for one proper-residue polynomial batch.

Only N enters the timed public procedure. Every preceding source and
transport frame is retained. Local periods and factor-sum offsets are
acquired only for independent validation after timing. A larger control
still survives; this is not universal one-sixth factorization.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-totient-window-audit.json"
WINDOW = runpy.run_path(str(ROOT/"scripts/probe_semiprime_totient_window.py"))
BATCH = WINDOW["PARENT"]["LOCAL"]["BATCH"]
REPLAY_ID = 202610031501


def build_residue_source(window):
    """Cast the cached records and retain the actual polynomial signals."""
    roots = [entry[0] for entry in window["giants"]]
    targets = [entry[0] for entry in window["babies"]]
    batch = BATCH["recovery"](window["N"],roots,targets,include_signals=True)
    assert batch["metrics"]["pair_products"] == 0
    assert batch["metrics"]["gcd_calls"] <= 4*window["width"]
    assert len(roots) == len(targets) == 2*window["width"]
    return dict(N=window["N"],width=window["width"],roots=roots,targets=targets,
                batch=batch,factor=batch["factor"],
                construction=dict(cached_record_casts=len(roots)+len(targets),
                                  new_window_powers=0,new_projection_powers=0,
                                  explicit_grid_candidates=0))


def public_packet(n):
    """Compute the preceding window once, then reuse its failed sources."""
    start = time.perf_counter()
    parent = WINDOW["public_packet"](n)
    factor = parent["factor"]
    source = None
    metrics = dict(new_residue_batches=0,leaf_candidate_gcds=0,
                   transport_order_powers=0,transport_square_roots=0,transport_gcds=0)
    if factor is None:
        window = parent["source"]
        assert window is not None and window["factor"] is None
        assert window["collision"] is None
        source = build_residue_source(window)
        metrics["new_residue_batches"] += 1
        if source["factor"] is not None:
            trace = parent["parent"]["source"]["trace"]
            factor = WINDOW["PARENT"]["lift_factor"](trace,source["factor"],metrics)
    if factor is not None:
        assert 1 < factor < n and n % factor == 0
    else:
        assert source is not None and source["factor"] is None
    assert metrics["transport_order_powers"] <= parent["parent"]["source"]["metrics"]["descent_levels"]
    return dict(N=n,width=parent["width"],parent=parent,source=source,factor=factor,
                status="factor" if factor is not None else "large-reduced-offsets",
                metrics=metrics,elapsed_ms=1000*(time.perf_counter()-start))


def check_packet(actual,p,q):
    """Validate local coverage outside the timed public procedure."""
    WINDOW["check_packet"](actual["parent"],p,q)
    assert actual["N"] == p*q
    if actual["factor"] is not None:
        assert actual["factor"] in (p,q)
    source = actual["source"]
    if source is None:
        assert actual["parent"]["factor"] == actual["factor"]
        return
    window = actual["parent"]["source"]
    reference = actual["parent"]["window_reference"]
    order_reference = actual["parent"]["parent"]["known_order_reference"]
    lp,lq = reference["local_p"],reference["local_q"]
    left,right = order_reference["left_order"],order_reference["right_order"]
    offset,cap = reference["true_offset"],reference["offset_cap"]
    assert left > cap and right > cap
    reduced_left,reduced_right = offset % left,offset % right
    covered = min(reduced_left,reduced_right) < cap
    actual["residue_reference"] = dict(local_p=lp,local_q=lq,left_order=left,right_order=right,
                                       true_offset=offset,left_offset=reduced_left,
                                       right_offset=reduced_right,offset_cap=cap,
                                       covered=covered,arithmetic_acquisition="outside timed routine")
    assert source["roots"] == [entry[0] for entry in window["giants"]]
    assert source["targets"] == [entry[0] for entry in window["babies"]]
    assert window["collision"] is None
    assert source["width"] <= actual["width"]
    assert source["construction"]["new_window_powers"] == 0
    batch = source["batch"]
    assert batch["metrics"]["shared_points"] == 0
    assert batch["metrics"]["gcd_calls"] <= 4*actual["width"]
    if covered:
        assert source["factor"] is not None
    if source["factor"] is not None:
        assert source["factor"] in (lp,lq)
        divisor = source["factor"]
        assert (batch["point"]-batch["root"]) % divisor == 0
        assert batch["point"] != batch["root"]
        assert source["roots"][batch["root_index"]] == batch["root"]
        assert source["targets"][batch["point_index"]] == batch["point"]
    else:
        assert reduced_left >= cap and reduced_right >= cap


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeTotientResidues.lean",
                  "scripts/CheckSemiprimeTotientResidues.lean",
                  "scripts/probe_semiprime_totient_residues.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import primerange

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    sources = source_inventory()
    prior = json.loads((ROOT/PARENT_AUDIT).read_text())
    counts,squares = Counter(),0
    primes = list(primerange(2,200))
    for i,p in enumerate(primes):
        for q in primes[i:]:
            actual = public_packet(p*q)
            check_packet(actual,p,q)
            counts[actual["status"]] += 1
            squares += int(p == q)
    populations = {}
    for name in ("inputs","controls","positive_controls","negative_controls"):
        population = []
        for previous in prior[name]:
            p,q = previous["reference_p"],previous["reference_q"]
            actual = public_packet(p*q)
            check_packet(actual,p,q)
            actual.update(reference_p=p,reference_q=q)
            if "regime" in previous:
                actual["regime"] = previous["regime"]
            population.append(actual)
        populations[name] = population
    p,q = 1000000007,5828428559
    wrapped = public_packet(p*q)
    check_packet(wrapped,p,q)
    wrapped.update(reference_p=p,reference_q=q)
    assert wrapped["parent"]["factor"] is None and wrapped["parent"]["source"]["collision"] is None
    assert wrapped["factor"] == p
    assert wrapped["residue_reference"]["true_offset"] == 500000208
    assert wrapped["residue_reference"]["left_offset"] == 205
    assert wrapped["residue_reference"]["offset_cap"] == 7203856
    negative = populations["negative_controls"][0]
    assert negative["factor"] is None
    assert negative["residue_reference"]["left_offset"] == 8392042
    assert negative["residue_reference"]["right_offset"] == 8392042
    result = dict(replay_id=REPLAY_ID,
                  scope="N-only proper-residue refinement of cached quarter-window sources",
                  one_sixth_guarantee="OPEN",is_complete_semiprime_factorizer=False,
                  is_bit_complexity_certificate=False,source_sha256=sources,
                  validation=dict(semiprime_cases=sum(counts.values()),prime_squares=squares,
                                  status_counts=dict(counts),normal_cases=len(populations["inputs"]),
                                  prior_controls=len(populations["controls"]),
                                  prior_positive_controls=len(populations["positive_controls"]),
                                  retained_negatives=len(populations["negative_controls"]),
                                  new_wrapped_controls=1),
                  summary=dict(sorted(Counter(x["status"] for x in populations["inputs"]).items())),
                  wrapped_controls=[wrapped],
                  wrapped_selection="Outside timing, fix p=1000000007 and choose the first safe prime strictly above 3*p+2*floor(sqrt(2*p*p)). This places the quarter offset just above (p-1)/2. Only N enters the timed procedure; this selected example is not a random coverage or scaling corpus.",
                  timing_protocol="Time the whole preceding public window packet and descent, casting its cached lists, deterministic distinct-root/target sorting, polynomial tree and remainder/derivative evaluation, all column GCDs, possible lazy leaf scan or witness recovery, retained signals and every successful transport. No new window, centre, power or projection is constructed. All factor, period and reduced-offset acquisitions occur after timing for independent validation.",
                  limitations="Both local reduced offsets can exceed the window cap, as the retained 61-bit negative demonstrates. The new sufficient coverage theorem and linear GCD/source bounds do not provide universal coverage or a complete bit implementation. Lean retains actual polynomial columns; the Python backend uses the previously validated packed polynomial/remainder implementation with separate operation counts.",
                  **populations)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(dict(validation=result["validation"],summary=result["summary"],
                          source_pins=len(sources),wrapped_factor=wrapped["factor"],
                          surviving_negative=negative["N"],one_sixth_guarantee="OPEN"),indent=2))


if __name__ == "__main__":
    main()

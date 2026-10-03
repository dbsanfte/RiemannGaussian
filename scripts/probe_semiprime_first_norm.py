#!/usr/bin/env python3
"""Public scalar norm scan, followed by at most one saturated-row jet.

The full explicit norm source retains B^(3/2) input scale. This replay
counts native construction and GCD work; it is not a bit-cost certificate.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-multiplier-norm-audit.json"
NORM = runpy.run_path(str(ROOT/"scripts/probe_semiprime_multiplier_norm.py"))
BIT, PARENT, BATCH, WINDOW = (NORM[k] for k in ("BIT", "PARENT", "BATCH", "WINDOW"))
JET, ScalarLedger = NORM["JET"], NORM["ScalarLedger"]
REPLAY_ID = 202610032401


def shared_products(n, alpha, targets, length, width, ring=None, inverse=None):
    """One channel per shared polynomial/tree, with exact full blocks and tail."""
    if length < 0 or width <= 0:
        raise ValueError("nonnegative interval and positive width required")
    ring = ScalarLedger(n) if ring is None else ring
    inverse = ring.inverse(alpha) if inverse is None else inverse
    targets = list(targets)
    count = len(targets)
    blocks, tail = divmod(length, width)
    offset = blocks*width
    batch = BATCH["MonicBatch"](n)

    def polynomial(degree):
        roots, y = [], 1
        for _ in range(degree):
            roots.append(y)
            y = ring.mul(y, alpha)
        return batch.tree(roots)[0]

    baby = polynomial(width)
    shift = ring.power(inverse, width)
    points = []
    for x in targets:
        z = x
        for j in range(blocks):
            points.append(z)
            if j+1 < blocks:
                z = ring.mul(z, shift)
    values = batch.evaluate(baby, points)
    phase_step = ring.power(alpha, width*width)
    products = []
    for row in range(count):
        product, phase = 1, 1
        for j in range(blocks):
            product = ring.mul(product, ring.mul(phase, values[row*blocks+j]))
            if j+1 < blocks:
                phase = ring.mul(phase, phase_step)
        products.append(product)
    tail_shift = ring.power(inverse, offset)
    tail_points = [ring.mul(x, tail_shift) for x in targets]
    if tail:
        tail_values = batch.evaluate(polynomial(tail), tail_points)
        phase = ring.power(alpha, offset*tail)
        products = [ring.mul(p, ring.mul(phase, t)) for p, t in zip(products, tail_values)]
    metrics = dict(row_count=count, interval_length=length, block_width=width,
        full_blocks=blocks, tail_degree=tail, root_polynomials=1+int(tail > 0),
        derivative_polynomials=0, derivative_rows=0,
        full_point_inputs=len(points), tail_point_inputs=len(tail_points),
        constructed_point_inputs=len(points)+len(tail_points),
        evaluated_point_inputs=len(points)+(len(tail_points) if tail else 0),
        explicit_input_count=width+len(points)+tail+len(tail_points),
        point_trees=int(bool(points))+int(bool(tail_points) and tail > 0),
        exact_interval=True, padded_interval=False, explicit_interval_targets=0,
        explicit_pair_grid_products=0, **batch.stats())
    assert metrics["explicit_input_count"] == width+count*blocks+tail+count
    return dict(rows=[dict(x=x, product=p, length=length) for x, p in zip(targets, products)],
                metrics=metrics)


def consume_selected(n, alpha, row, divisor, b, ring, inverse):
    """Reuse a proper scan GCD; build one jet only for a saturated winner."""
    if 1 < divisor < n:
        return dict(factor=divisor, stage="product", additional_gcds=0,
                    late_jet=None, late_metrics=None)
    assert divisor == n and row["product"] == 0
    report = NORM["exact_shared_jets"](n, alpha, [row["x"]], row["length"],
                                        math.isqrt(row["length"])+1, ring, inverse)
    jet = report["rows"][0]
    assert jet["product"] == row["product"]
    decoded = NORM["decode_norm"](n, jet, 2*b, ring)
    return dict(factor=decoded["factor"], stage=decoded.get("stage", "unrecoverable-saturated"),
                additional_gcds=decoded["gcd_calls"], late_jet=jet,
                late_metrics=report["metrics"], decoded=decoded)


def build_source(window):
    n, b, alpha, beta = (window[k] for k in ("N", "width", "active_base", "target"))
    length = (2*b)**2
    ring = ScalarLedger(n)
    inverse, beta_inverse = ring.inverse(alpha), ring.inverse(beta)
    centres, positive, negative = [], beta, beta_inverse
    for k in range(1, b+1):
        centres.extend((positive, negative))
        if k < b:
            positive, negative = ring.mul(positive, beta), ring.mul(negative, beta_inverse)
    groups, inspected, offset, group_size, selected = [], [], 0, 1, None
    while offset < len(centres) and selected is None:
        count = min(group_size, len(centres)-offset)
        width = math.isqrt(count*length)+1
        report = shared_products(n, alpha, centres[offset:offset+count], length, width, ring, inverse)
        assert report["metrics"]["explicit_input_count"] <= 4*width
        assert report["metrics"]["explicit_input_count"]**2 <= 32*count*length+32
        groups.append(dict(first_centre=offset, **report["metrics"]))
        for local, row in enumerate(report["rows"]):
            index = offset+local
            divisor = math.gcd(n, row["product"])
            record = dict(index=index, multiplier=index//2+1, negative=bool(index % 2),
                          row=row, divisor=divisor)
            inspected.append(record)
            if divisor != 1:
                selected = dict(**record,
                    recovery=consume_selected(n, alpha, row, divisor, b, ring, inverse))
                break
        offset += count
        group_size *= 2
    late = selected["recovery"]["late_metrics"] if selected else None
    totals = {key: sum(g[key] for g in groups)+(late[key] if late else 0)
        for key in ("full_point_inputs", "tail_point_inputs", "constructed_point_inputs",
                    "evaluated_point_inputs", "explicit_input_count", "root_polynomials",
                    "point_trees", "convolutions", "packed_coefficients", "monic_reductions")}
    totals.update(retained_signed_centres=len(centres), examined_norms=len(inspected),
        evaluated_norms=sum(g["row_count"] for g in groups), norm_gcd_calls=len(inspected),
        recovery_gcd_calls=selected["recovery"]["additional_gcds"] if selected else 0,
        late_derivative_rows=int(late is not None),
        derivative_polynomials=2*late["root_polynomials"] if late else 0,
        groups=len(groups), **ring.stats())
    totals["total_source_gcd_calls"] = totals["norm_gcd_calls"]+totals["recovery_gcd_calls"]
    assert totals["total_source_gcd_calls"] <= 6*b+2
    assert ring.max_product_bits <= 2*n.bit_length()
    return dict(N=n, width=b, interval_length=length, centres=centres, groups=groups,
        inspected=inspected, selected=selected,
        factor=selected["recovery"]["factor"] if selected else None, metrics=totals)


def public_packet(n):
    """Only N enters: complete old prefix, scalar norms and original transport."""
    start = time.perf_counter()
    parent = BIT["public_packet"](n)
    factor, source = parent["factor"], None
    metrics = dict(new_first_norm_sources=0, leaf_candidate_gcds=0,
        transport_order_powers=0, transport_square_roots=0, transport_gcds=0)
    if factor is None:
        window = parent["parent"]["source"]
        assert window is not None and window["factor"] is None
        source = build_source(window)
        metrics["new_first_norm_sources"] = 1
        if source["factor"] is not None:
            trace = parent["parent"]["parent"]["source"]["trace"]
            factor = WINDOW["PARENT"]["lift_factor"](trace, source["factor"], metrics)
    if factor is not None:
        assert 1 < factor < n and n % factor == 0
    return dict(N=n, width=parent["width"], parent=parent, source=source, factor=factor,
        status="factor" if factor is not None else "failure",
        metrics=metrics, elapsed_ms=1000*(time.perf_counter()-start))


def validate_components():
    rnd = random.Random(REPLAY_ID)
    rows = 0
    for _ in range(192):
        n = rnd.choice((4, 9, 15, 25, 35, 49, 77, 143, 323))
        alpha = rnd.choice([a for a in range(1, n) if math.gcd(a, n) == 1])
        targets = [rnd.randrange(n) for _ in range(rnd.randrange(1, 9))]
        length, width = rnd.randrange(65), rnd.randrange(1, 32)
        actual = shared_products(n, alpha, targets, length, width)
        for row in actual["rows"]:
            assert row["product"] == JET["direct_jet"](n, alpha, row["x"], length)[0]
            rows += 1
        assert actual["metrics"]["derivative_polynomials"] == 0
    controls = []
    for control in json.loads((ROOT/PARENT_AUDIT).read_text())["validation"]["saturated_and_shared_controls"]:
        row = control["row"]
        n, alpha, b = 10403, 2, 2
        ring = ScalarLedger(n)
        scalar = shared_products(n, alpha, [row["x"]], 16, 7, ring)["rows"][0]
        divisor = math.gcd(n, scalar["product"])
        result = consume_selected(n, alpha, scalar, divisor, b, ring, ring.inverse(alpha))
        assert result["factor"] == control["decoded"]["factor"]
        assert (result["late_jet"] is not None) == (row["product"] == 0)
        controls.append(dict(name=control["name"], scalar=scalar, recovery=result))
    return dict(shared_product_groups=192, direct_product_rows=rows,
        saturated_controls=controls, no_derivative_polynomials_in_scalar_groups=True)


def check_packet(actual, previous, p, q):
    """Private reference acquisition and independent jets are outside timing."""
    PARENT["check_packet"](actual["parent"], p, q)
    assert actual["factor"] == previous["factor"] and actual["factor"] in (p, q)
    assert (actual["parent"]["factor"], actual["parent"]["status"]) == \
        (previous["parent"]["factor"], previous["parent"]["status"])
    source = actual["source"]
    if source is None:
        assert previous["source"] is None
        return
    old = previous["source"]
    assert source["centres"] == old["centres"]
    assert len(source["inspected"]) == len(old["examined"])
    for row, earlier in zip(source["inspected"], old["examined"]):
        assert row["row"]["x"] == earlier["jet"]["x"]
        assert row["row"]["product"] == earlier["jet"]["product"]
        assert (row["divisor"] == 1) == (row["index"] < source["selected"]["index"])
    assert source["selected"]["multiplier"] == old["successful_norm"]["multiplier"]
    assert source["selected"]["negative"] == old["successful_norm"]["negative"]
    window = actual["parent"]["parent"]["source"]
    chosen = {g["first_centre"] for g in source["groups"]}
    chosen.add(len(source["inspected"])-1)
    for index in sorted(chosen):
        row = source["inspected"][index]["row"]
        independent = JET["interval_jet"](source["N"], window["active_base"], row["x"], source["interval_length"])
        assert row["product"] == independent["product"]
    source["independent_large_products_checked"] = len(chosen)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeFirstNorm.lean",
        "scripts/CheckSemiprimeFirstNorm.lean", "scripts/probe_semiprime_first_norm.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import primerange
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources, components = source_inventory(), validate_components()
    counts, squares = Counter(), 0
    primes = list(primerange(2, 200))
    for i, p in enumerate(primes):
        for q in primes[i:]:
            actual = public_packet(p*q)
            PARENT["check_packet"](actual["parent"], p, q)
            assert actual["factor"] in (p, q) and actual["source"] is None
            counts[actual["status"]] += 1
            squares += int(p == q)
    prior = json.loads((ROOT/PARENT_AUDIT).read_text())
    populations, summaries, inherited = {}, [], 0
    for name in ("inputs", "controls", "positive_controls", "negative_controls", "wrapped_controls"):
        populations[name] = []
        for previous in prior[name]:
            p, q = previous["reference_p"], previous["reference_q"]
            actual = public_packet(p*q)
            check_packet(actual, previous, p, q)
            actual.update(reference_p=p, reference_q=q)
            if "regime" in previous:
                actual["regime"] = previous["regime"]
            if actual["source"] is None:
                inherited += 1
            else:
                source = actual["source"]
                summaries.append(dict(original_N=p*q, leaf_N=source["N"], factor=actual["factor"],
                    selected=source["selected"], **source["metrics"]))
            populations[name].append(actual)
    assert len(summaries) == 1 and summaries[0]["late_derivative_rows"] == 0
    assert source_inventory() == sources, "source changed during replay"
    result = dict(replay_id=REPLAY_ID, source_sha256=sources,
        scope="First nonunit scalar norm with at most one late derivative recovery",
        one_sixth_guarantee="OPEN", universal_lean_specification=True,
        is_complete_semiprime_factorizer=True, is_bit_complexity_certificate=False,
        is_formal_machine_refinement=False,
        validation=dict(semiprime_cases=sum(counts.values()), prime_squares=squares,
            status_counts=dict(counts), prior_final_factors_preserved=True,
            inherited_successes_preserved=inherited, first_norm_sources=len(summaries), **components),
        first_norm_sources=summaries, **populations,
        timing_protocol="Only N enters the outer timer. The entire bit-power/walk and residue prefix, public inverse and centre cache, scalar-only exact block/tail polynomials and one-channel point trees, all norm GCDs, at most one late three-channel jet and index recovery, diagnostics and original-input transport are charged. The old three-channel multiplier-norm source is not executed first. Private factors and independent reference products enter afterward.",
        limitations="Lean proves first-nonunit universal recovery, actual recursive scan GCD counts, and at most one late derivative consumer. Native scalar/group/polynomial construction and the complete machine/bit clock remain uncertified. The explicit full-family input count remains B^(3/2); finite successful replays do not prove the requested every-run one-sixth bit rate.")
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(dict(validation=result["validation"], source_pins=len(sources),
        first_norm_sources=summaries, one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()

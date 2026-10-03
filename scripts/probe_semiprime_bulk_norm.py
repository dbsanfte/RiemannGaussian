#!/usr/bin/env python3
"""Phase-free aggregate norm queries and left-first saturated recovery.

The explicit shared point layout still has B^(3/2) input scale. All
native construction is charged; these measurements are not a bit theorem.
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
PARENT_AUDIT = "docs/semiprime-first-norm-audit.json"
FIRST = runpy.run_path(str(ROOT/"scripts/probe_semiprime_first_norm.py"))
BIT, PARENT, BATCH, WINDOW, NORM, JET, ScalarLedger = (
    FIRST[k] for k in ("BIT", "PARENT", "BATCH", "WINDOW", "NORM", "JET", "ScalarLedger"))
REPLAY_ID = 202610032501


def bulk_product(n, alpha, targets, length, width, ring=None, inverse=None):
    """Share one polynomial per exact block/tail, fold directly to one scalar.

    Removed phases are units, so only GCD equality with the canonical
    product is asserted. No per-row norm outputs or derivative channels.
    """
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
    product = 1
    for value in batch.evaluate(baby, points):
        product = ring.mul(product, value)
    tail_shift = ring.power(inverse, offset)
    tail_points = [ring.mul(x, tail_shift) for x in targets]
    if tail:
        for value in batch.evaluate(polynomial(tail), tail_points):
            product = ring.mul(product, value)
    metrics = dict(row_count=count, interval_length=length, block_width=width,
        full_blocks=blocks, tail_degree=tail, root_polynomials=1+int(tail > 0),
        derivative_polynomials=0, derivative_rows=0,
        retained_norm_outputs=0, aggregate_outputs=1, computed_phase_factors=0,
        full_point_inputs=len(points), tail_point_inputs=len(tail_points),
        constructed_point_inputs=len(points)+len(tail_points),
        evaluated_point_inputs=len(points)+(len(tail_points) if tail else 0),
        explicit_input_count=width+len(points)+tail+len(tail_points),
        point_trees=int(bool(points))+int(bool(tail_points) and tail > 0),
        exact_interval=True, padded_interval=False, explicit_interval_targets=0,
        explicit_pair_grid_products=0, **batch.stats())
    assert metrics["explicit_input_count"] == width+count*blocks+tail+count
    return dict(product=product, metrics=metrics)


def query_groups(n, alpha, centres, length, b, ring, inverse):
    """Concrete doubling forest with unit dummy leaves outside the real prefix."""
    queries, inferred_right_zeros = [], []
    depth_limit = (2*b).bit_length()

    def query(start, depth, kind):
        targets = centres[start:min(start+(1 << depth), len(centres))]
        assert targets, "a chosen search block must contain a real row"
        width = math.isqrt(len(targets)*length)+1
        report = bulk_product(n, alpha, targets, length, width, ring, inverse)
        divisor = math.gcd(n, report["product"])
        assert report["metrics"]["explicit_input_count"] <= 4*width
        assert report["metrics"]["explicit_input_count"]**2 <= 32*len(targets)*length+32
        queries.append(dict(kind=kind, first_centre=start, virtual_depth=depth,
            virtual_span=1 << depth, product=report["product"], divisor=divisor,
            **report["metrics"]))
        return divisor

    def split(start, depth):
        while depth:
            depth -= 1
            divisor = query(start, depth, "left-child")
            if 1 < divisor < n:
                return dict(factor=divisor, stage="split-product", selected_index=None,
                    late_jet=None, late_metrics=None, recovery_gcd_calls=0)
            if divisor == 1:
                inferred_right_zeros.append(dict(first_centre=start+(1 << depth),
                    virtual_depth=depth, constructed_right_aggregate=False))
                start += 1 << depth
            else:
                assert divisor == n
        assert start < len(centres)
        report = NORM["exact_shared_jets"](n, alpha, [centres[start]], length,
            math.isqrt(length)+1, ring, inverse)
        jet = report["rows"][0]
        assert jet["product"] == 0
        decoded = NORM["decode_norm"](n, jet, 2*b, ring)
        return dict(factor=decoded["factor"], stage=decoded.get("stage", "unrecoverable-saturated"),
            selected_index=start, multiplier=start//2+1, negative=bool(start % 2),
            late_jet=jet, late_metrics=report["metrics"], decoded=decoded,
            recovery_gcd_calls=decoded["gcd_calls"])

    start, answer = 0, None
    for depth in range(depth_limit):
        if start >= len(centres):
            break
        divisor = query(start, depth, "root")
        if 1 < divisor < n:
            answer = dict(factor=divisor, stage="aggregate-product", selected_index=None,
                late_jet=None, late_metrics=None, recovery_gcd_calls=0)
            break
        if divisor == n:
            answer = split(start, depth)
            break
        assert divisor == 1
        start += 1 << depth
    return dict(queries=queries, answer=answer, inferred_right_zeros=inferred_right_zeros,
                public_depth=depth_limit)


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
    search = query_groups(n, alpha, centres, length, b, ring, inverse)
    answer, queries = search["answer"], search["queries"]
    late = answer["late_metrics"] if answer else None
    totals = {key: sum(g[key] for g in queries)+(late[key] if late else 0)
        for key in ("full_point_inputs", "tail_point_inputs", "constructed_point_inputs",
                    "evaluated_point_inputs", "explicit_input_count", "root_polynomials",
                    "point_trees", "convolutions", "packed_coefficients", "monic_reductions")}
    totals.update(retained_signed_centres=len(centres), retained_norm_outputs=0,
        aggregate_outputs=len(queries), computed_phase_factors=0,
        evaluated_norms=sum(g["row_count"] for g in queries),
        bulk_gcd_calls=len(queries), root_gcd_calls=sum(g["kind"] == "root" for g in queries),
        split_gcd_calls=sum(g["kind"] == "left-child" for g in queries),
        recovery_gcd_calls=answer["recovery_gcd_calls"] if answer else 0,
        inferred_right_zeros=len(search["inferred_right_zeros"]),
        late_derivative_rows=int(late is not None),
        derivative_polynomials=2*late["root_polynomials"] if late else 0, **ring.stats())
    totals["total_source_gcd_calls"] = totals["bulk_gcd_calls"]+totals["recovery_gcd_calls"]
    assert totals["bulk_gcd_calls"] <= 2*search["public_depth"]
    assert totals["total_source_gcd_calls"] <= 2*search["public_depth"]+4*b+2
    assert ring.max_product_bits <= 2*n.bit_length()
    return dict(N=n, width=b, interval_length=length, centres=centres, **search,
        factor=answer["factor"] if answer else None, metrics=totals)


def public_packet(n):
    """Only N enters the timer: old prefix, concrete bulk queries and transport."""
    start = time.perf_counter()
    parent = BIT["public_packet"](n)
    factor, source = parent["factor"], None
    metrics = dict(new_bulk_norm_sources=0, leaf_candidate_gcds=0,
        transport_order_powers=0, transport_square_roots=0, transport_gcds=0)
    if factor is None:
        window = parent["parent"]["source"]
        assert window is not None and window["factor"] is None
        source = build_source(window)
        metrics["new_bulk_norm_sources"] = 1
        if source["factor"] is not None:
            trace = parent["parent"]["parent"]["source"]["trace"]
            factor = WINDOW["PARENT"]["lift_factor"](trace, source["factor"], metrics)
    if factor is not None:
        assert 1 < factor < n and n % factor == 0
    return dict(N=n, width=parent["width"], parent=parent, source=source, factor=factor,
        status="factor" if factor is not None else "failure",
        metrics=metrics, elapsed_ms=1000*(time.perf_counter()-start))


def validate_components():
    rnd, rows = random.Random(REPLAY_ID), 0
    for _ in range(192):
        n = rnd.choice((4, 9, 15, 25, 35, 49, 77, 143, 323))
        alpha = rnd.choice([a for a in range(1, n) if math.gcd(a, n) == 1])
        targets = [rnd.randrange(n) for _ in range(rnd.randrange(1, 9))]
        length, width = rnd.randrange(65), rnd.randrange(1, 32)
        actual = bulk_product(n, alpha, targets, length, width)
        canonical = 1
        for x in targets:
            canonical = canonical*JET["direct_jet"](n, alpha, x, length)[0] % n
            rows += 1
        assert math.gcd(n, actual["product"]) == math.gcd(n, canonical)
        assert actual["metrics"]["derivative_polynomials"] == 0
        assert actual["metrics"]["retained_norm_outputs"] == 0
    n, alpha, b, length = 10403, 2, 2, 16
    inherited = json.loads((ROOT/PARENT_AUDIT).read_text())["validation"]["saturated_controls"]
    values = {c["name"]: c["scalar"]["x"] for c in inherited}
    saturated = values["saturated-distinct-indices"]
    unit = next(x for x in range(1, n) if math.gcd(x, n) == 1 and
        math.gcd(n, JET["direct_jet"](n, alpha, x, length)[0]) == 1)
    # Test one whole group directly, then the same paid split procedure.
    controls = []
    for name, targets, expected in (
        ("unit-group", [unit], None),
        ("proper-aggregate", [values["left-only-root"]], 101),
        ("mixed-local-root-aggregate", [values["left-only-root"], values["right-only-root"]], 101),
        ("two-saturated-rows", [saturated, saturated], 103),
        ("unit-left-saturated-right", [unit, saturated], 103),
        ("shared-global-outside-core", [values["shared-global-index"]], None)):
        ring = ScalarLedger(n)
        # Doubling prefix [unit], then the tested two-row block if needed.
        centres = targets if len(targets) == 1 else [unit]+targets
        report = query_groups(n, alpha, centres, length, b, ring, ring.inverse(alpha))
        answer = report["answer"]
        factor = answer["factor"] if answer else None
        assert factor == expected
        if name == "two-saturated-rows":
            jets = [JET["direct_jet"](n, alpha, x, length) for x in targets]
            assert NORM["combine"](jets[0], jets[1], ScalarLedger(n)) == (0, 0, 0)
        if name == "unit-left-saturated-right":
            assert report["inferred_right_zeros"] and answer["selected_index"] == 2
        controls.append(dict(name=name, centres=centres, **report, scalar_metrics=ring.stats()))
    return dict(aggregate_groups=192, direct_product_rows=rows, saturated_controls=controls,
        no_per_row_norm_outputs=True, no_phase_construction=True,
        right_zero_inferred_without_right_query=True)


def check_packet(actual, previous, p, q):
    """Private references and independent canonical products enter after timing."""
    PARENT["check_packet"](actual["parent"], p, q)
    assert actual["factor"] == previous["factor"] and actual["factor"] in (p, q)
    assert (actual["parent"]["factor"], actual["parent"]["status"]) == \
        (previous["parent"]["factor"], previous["parent"]["status"])
    source = actual["source"]
    if source is None:
        assert previous["source"] is None
        return
    assert source["centres"] == previous["source"]["centres"]
    assert source["metrics"]["retained_norm_outputs"] == 0
    assert source["metrics"]["computed_phase_factors"] == 0
    window = actual["parent"]["parent"]["source"]
    checks = []
    for query in source["queries"]:
        start, count = query["first_centre"], query["row_count"]
        # Paid canonical reference constructor is outside the public timer.
        reference = FIRST["shared_products"](source["N"], window["active_base"],
            source["centres"][start:start+count], source["interval_length"], query["block_width"])
        canonical = math.prod(row["product"] for row in reference["rows"]) % source["N"]
        assert math.gcd(source["N"], canonical) == query["divisor"]
        checks.append(dict(first_centre=start, row_count=count,
            canonical_product=canonical, canonical_gcd=query["divisor"],
            phase_free_product=query["product"], gcd_equal=True))
    answer = source["answer"]
    if answer["selected_index"] is not None:
        assert answer["selected_index"] == previous["source"]["selected"]["index"]
        assert answer["late_jet"]["product"] == 0
    source["independent_canonical_groups_checked"] = len(checks)
    source["independent_canonical_checks"] = checks


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeBulkNorm.lean",
        "scripts/CheckSemiprimeBulkNorm.lean", "scripts/probe_semiprime_bulk_norm.py"))
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
                    answer=source["answer"], public_depth=source["public_depth"],
                    independent_canonical_groups_checked=source["independent_canonical_groups_checked"],
                    **source["metrics"]))
            populations[name].append(actual)
    assert len(summaries) == 1 and summaries[0]["late_derivative_rows"] == 0
    assert source_inventory() == sources, "source changed during replay"
    result = dict(replay_id=REPLAY_ID, source_sha256=sources,
        scope="Phase-free aggregate forest with left-first saturated recovery and one optional late jet",
        one_sixth_guarantee="OPEN", universal_lean_specification=True,
        is_complete_semiprime_factorizer=True, is_bit_complexity_certificate=False,
        is_formal_machine_refinement=False,
        validation=dict(semiprime_cases=sum(counts.values()), prime_squares=squares,
            status_counts=dict(counts), prior_final_factors_preserved=True,
            inherited_successes_preserved=inherited, bulk_norm_sources=len(summaries), **components),
        bulk_norm_sources=summaries, **populations,
        timing_protocol="Only N enters the outer timer. The entire bit-power/walk and residue prefix, public inverse and signed centre cache, concrete phase-free block/tail polynomials and point trees, every aggregate/split GCD, at most one late exact three-channel jet and integer-index recovery, diagnostics and original-input transport are charged. Neither the preceding scalar norm source nor its per-row GCD scan is executed. Private factors and independently constructed canonical group products enter afterward.",
        limitations="Lean proves exact GCD preservation after unit phase cancellation, correctness and the recursive query clock of the doubling forest/left-first saturated search, and universal N-only semiprime recovery with one optional late jet. Native polynomial/group construction and a complete machine/bit clock remain uncertified. The explicit full-family shared input count remains B^(3/2); reducing retained outputs and GCD queries does not prove the requested every-run one-sixth bit rate.")
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(dict(semiprime_cases=sum(counts.values()), prime_squares=squares,
        inherited_successes_preserved=inherited, component_groups=components["aggregate_groups"],
        component_rows=components["direct_product_rows"], component_controls=len(components["saturated_controls"]),
        source_pins=len(sources), bulk_norm_sources=summaries, one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Audit the growing degree of a transposed scalar q-aggregate constructor.

This is a constructor experiment, not a replacement public factorizer or
a whole-pipeline timer. Public targets are supplied explicitly; their
acquisition is outside its constructor timer. No bit exponent is claimed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-bulk-norm-audit.json"
BULK = runpy.run_path(str(ROOT/"scripts/probe_semiprime_bulk_norm.py"))
BATCH, JET, ScalarLedger = (BULK[k] for k in ("BATCH", "JET", "ScalarLedger"))
REPLAY_ID = 202610032601


def transposed_product(n, alpha, targets, length, width=None):
    """Normalize target_i-alpha^(offset+u) by the unit -alpha^u.

    One shared s-root polynomial is scaled homogeneously for each
    target, then multiplied to a monic degree-r*s polynomial. Only
    L/s geometric giant points remain. Exact tails have degree r*T.
    All coefficient construction and point work is paid and counted.
    """
    start = time.perf_counter()
    targets = list(targets)
    rows = len(targets)
    if not rows or length < 0:
        raise ValueError("nonempty targets, nonnegative interval and unit alpha required")
    width = max(1, math.isqrt(length//rows)) if width is None else width
    if width <= 0:
        raise ValueError("positive public width required")
    blocks, tail = divmod(length, width)
    ring, batch = ScalarLedger(n), BATCH["MonicBatch"](n)
    inverse = ring.inverse(alpha)
    root_inputs = scaled_coefficient_visits = 0

    def polynomial(size):
        nonlocal root_inputs, scaled_coefficient_visits
        roots, y = [], 1
        for _ in range(size):
            roots.append(y)
            y = ring.mul(y, inverse)
        root_inputs += len(roots)
        base = batch.tree(roots)[0]
        level = []
        for x in targets:
            # x^size*base(X/x) uses no inverse of the target. It
            # retains repeated and nonunit targets over a composite ring.
            scaled, power = [0]*(size+1), 1
            scaled[size] = 1
            for j in range(size-1, -1, -1):
                power = ring.mul(power, x)
                scaled[j] = ring.mul(base[j], power)
            scaled_coefficient_visits += len(scaled)
            level.append(scaled)
        while len(level) > 1:
            next_level = [batch.mul(level[i], level[i+1])
                for i in range(0, len(level)-1, 2)]
            if len(level) % 2:
                next_level.append(level[-1])
            level = next_level
        result = level[0]
        assert len(result)-1 == rows*size and result[-1] == 1
        return result

    baby = polynomial(width)
    shift = ring.power(alpha, width)
    points, y = [], 1
    for _ in range(blocks):
        points.append(y)
        y = ring.mul(y, shift)
    product = 1
    for value in batch.evaluate(baby, points):
        product = ring.mul(product, value)
    if tail:
        product = ring.mul(product, batch.evaluate(polynomial(tail), [y])[0])
    budget = rows*width+blocks+rows*tail+1
    assert budget*budget > 4*rows*length
    metrics = dict(row_count=rows, interval_length=length, block_width=width,
        full_blocks=blocks, tail_width=tail, coefficient_degree=rows,
        baby_polynomial_degree=len(baby)-1, tail_polynomial_degree=rows*tail,
        explicit_degree_point_budget=budget, shared_root_inputs=root_inputs,
        scaled_coefficient_visits=scaled_coefficient_visits,
        constructed_giant_points=blocks, constructed_tail_points=1,
        evaluated_point_inputs=blocks+int(tail > 0),
        root_polynomials=1+int(tail > 0), point_trees=int(blocks > 0)+int(tail > 0),
        retained_norm_outputs=0, computed_phase_factors=0, derivative_polynomials=0,
        exact_interval=True, padded_interval=False, **batch.stats(), **ring.stats())
    divisor = math.gcd(n, product)
    metrics["gcd_calls"] = 1
    elapsed = 1000*(time.perf_counter()-start)
    return dict(product=product, divisor=divisor, metrics=metrics, elapsed_ms=elapsed)


def validate_components():
    rnd, rows = random.Random(REPLAY_ID), 0
    for _ in range(192):
        n = rnd.choice((4, 9, 15, 25, 35, 49, 77, 143, 323))
        alpha = rnd.choice([a for a in range(1, n) if math.gcd(a, n) == 1])
        targets = [rnd.randrange(n) for _ in range(rnd.randrange(1, 9))]
        length, width = rnd.randrange(65), rnd.randrange(1, 32)
        actual = transposed_product(n, alpha, targets, length, width)
        canonical = 1
        for x in targets:
            canonical = canonical*JET["direct_jet"](n, alpha, x, length)[0] % n
            rows += 1
        assert actual["divisor"] == math.gcd(n, canonical)
        assert actual["metrics"]["baby_polynomial_degree"] == len(targets)*width
        assert actual["metrics"]["retained_norm_outputs"] == 0
    prior = json.loads((ROOT/PARENT_AUDIT).read_text())
    controls = []
    for c in prior["validation"]["saturated_controls"]:
        actual = transposed_product(10403, 2, c["centres"], 16)
        canonical = math.prod(JET["direct_jet"](10403, 2, x, 16)[0] for x in c["centres"]) % 10403
        assert actual["divisor"] == math.gcd(10403, canonical)
        controls.append(dict(name=c["name"], canonical_product=canonical, **actual))
    return dict(component_groups=192, direct_row_products=rows, controls=controls,
                exact_aggregate_gcd_preserved=True, repeated_and_nonunit_targets_retained=True)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeQAggregate.lean",
        "scripts/CheckSemiprimeQAggregate.lean", "scripts/probe_semiprime_q_aggregate.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources, validation = source_inventory(), validate_components()
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    hard = next(c for c in parent["negative_controls"] if c["source"])
    source, window = hard["source"], hard["parent"]["parent"]["source"]
    n, alpha, length = source["N"], window["active_base"], source["interval_length"]
    groups = []
    for old in source["queries"]:
        start, rows = old["first_centre"], old["row_count"]
        targets = source["centres"][start:start+rows]
        actual = transposed_product(n, alpha, targets, length)
        assert actual["divisor"] == old["divisor"]
        reference = BULK["bulk_product"](n, alpha, targets, length, old["block_width"])
        assert reference["product"] == old["product"]
        groups.append(dict(first_centre=start, original_gcd=old["divisor"],
            prior_explicit_input_count=old["explicit_input_count"], **actual))
    scaling = []
    for b in (2, 8, 32, 128, 512):
        targets = source["centres"][:2*b]
        actual = transposed_product(n, alpha, targets, (2*b)**2)
        # Constructor shape controls, not full public runs at these widths.
        reference = BULK["bulk_product"](n, alpha, targets, (2*b)**2,
            math.isqrt(2*b*(2*b)**2)+1)
        assert actual["divisor"] == math.gcd(n, reference["product"])
        assert actual["metrics"]["tail_width"] == 0
        scaling.append(dict(width=b, **actual))
    assert source_inventory() == sources, "source changed during replay"
    report = dict(replay_id=REPLAY_ID, source_sha256=sources,
        scope="Transposed aggregate constructor and explicit growing-degree audit",
        one_sixth_guarantee="OPEN", universal_aggregate_gcd_identity_lean=True,
        is_complete_semiprime_factorizer=False, is_bit_complexity_certificate=False,
        is_formal_machine_refinement=False, validation=validation,
        saved_public_input=hard["N"], groups=groups, scaling_controls=scaling,
        timing_protocol="Each constructor timer receives only N, a public unit base, the explicit public target list, interval length and optional public width. It charges homogeneous coefficient scaling, shared root construction, polynomial products, inverse, power, geometric giant points, remainder trees, scalar fold and GCD. Target acquisition and the old public pipeline are outside this constructor timer. Private factors are never passed; saved public targets come from the frozen bulk replay. Canonical references enter afterward.",
        limitations="This candidate preserves the exact old aggregate GCD but does not establish the requested exponent. Lean proves recurrence coefficient degree r, baby degree r*s, and 32*B^3 < explicitInputs^2 for every positive width in the full 2B-row layout. Native construction and bit cost remain uncertified. This is a restriction on the explicit polynomial q-block construction, not a lower bound on all aggregate algorithms or on integer factorization.")
    if args.output:
        args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources), component_groups=validation["component_groups"],
        direct_row_products=validation["direct_row_products"], controls=len(validation["controls"]),
        group_gcds=[g["divisor"] for g in groups],
        group_input_budgets=[g["metrics"]["explicit_degree_point_budget"] for g in groups],
        group_constructor_ms=[g["elapsed_ms"] for g in groups],
        scaling=[dict(B=c["width"], degree=c["metrics"]["baby_polynomial_degree"],
            inputs=c["metrics"]["explicit_degree_point_budget"], elapsed_ms=c["elapsed_ms"]) for c in scaling],
        one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Original-source heads without a dense coefficient prefix.

Optional research replay. Public residual GCDs expose different local row
sets immediately. Globally zero rows use a homogeneous marked product tree.
The public source pass computes residuals first and derivative channels only
for saturated rows, reusing baby products. The residual source still has the
shared B^(3/2) input scale. No universal sixth-root bit bound is certified.
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
TAGGED = runpy.run_path(str(ROOT/"scripts/probe_semiprime_tagged_pooling.py"))
SHARED, JET = TAGGED["SHARED"], TAGGED["JET"]
CENTRE, PREFIX = TAGGED["CENTRE"], TAGGED["PREFIX"]
RECOVERY, MonicBatch = TAGGED["RECOVERY"], TAGGED["MonicBatch"]
SEED = 202610030307


def evaluate_channels(batch, polynomials, points):
    if not points:
        return [[] for _ in polynomials]
    tree = batch.tree(points)
    outputs = [[] for _ in polynomials]

    def visit(node, remainders):
        remainders = [batch.mod(p, node[0]) for p in remainders]
        if node[1] is None:
            for out, p in zip(outputs, remainders):
                out.append(p[0] if p else 0)
        else:
            visit(node[1], remainders)
            visit(node[2], remainders)

    visit(tree, polynomials)
    return outputs


def shared_products(n, alpha, targets, length, width=None):
    """One-channel original padded residuals; no derivative data yet."""
    start = time.perf_counter()
    targets = list(targets)
    if length <= 0 or math.gcd(alpha, n) != 1 or not targets:
        raise ValueError("positive interval, public unit and targets required")
    width = max(1, math.isqrt(len(targets)*length)+1) if width is None else width
    if width <= 0:
        raise ValueError("positive block width required")
    blocks = (length-1)//width+1
    batch = MonicBatch(n)
    baby_tree = batch.tree(CENTRE["geometric"](1, alpha, width, n))
    polynomial = baby_tree[0]
    shift = pow(pow(alpha, -1, n), width, n)
    points = [z for x in targets for z in CENTRE["geometric"](x, shift, blocks, n)]
    values = batch.evaluate(polynomial, points)
    phase_step = pow(alpha, width*width, n)
    rows = []
    for row, x in enumerate(targets):
        residual, phase = 1, 1
        for j in range(blocks):
            residual = residual*phase*values[row*blocks+j] % n
            phase = phase*phase_step % n
        rows.append({"x": x, "product": residual, "length": width*blocks})
    return {"rows": rows, "elapsed_ms": 1000*(time.perf_counter()-start),
            "metrics": {"row_count": len(targets), "baby_factors": width,
                        "block_width": width, "block_count": blocks,
                        "original_interval": length, "padded_interval": width*blocks,
                        "residual_point_inputs": len(points),
                        "residual_channel_evaluations": len(points),
                        "derivative_channel_evaluations": 0,
                        "point_trees": 1, "base_marking_built": False,
                        "reshape_input_count": width+len(points),
                        "explicit_pair_candidates": 0, "tail_factors": 0,
                        "epsilon_coefficients_constructed": 0, **batch.stats()},
            "context": {"n": n, "alpha": alpha, "targets": targets,
                        "width": width, "blocks": blocks, "batch": batch,
                        "baby_tree": baby_tree, "points": points, "values": values,
                        "shift": shift, "phase_step": phase_step}}


def selected_jets(source, selected):
    """Add only needed derivative channels using retained baby products."""
    start = time.perf_counter()
    ctx = source["context"]
    n, width, blocks, batch = (ctx[k] for k in ("n", "width", "blocks", "batch"))

    def marking(node, offset):
        if node[1] is None:
            return [offset*node[0][0] % n, 0], offset+1
        left, nxt = marking(node[1], offset)
        right, nxt = marking(node[2], nxt)
        return JET["add_polynomials"](batch.mul(left, node[2][0]),
                                      batch.mul(node[1][0], right), n), nxt

    base_jet, end = marking(ctx["baby_tree"], 0)
    assert end == width
    polynomial = ctx["baby_tree"][0]
    derivative = [i*polynomial[i] % n for i in range(1, len(polynomial))]
    points = [ctx["points"][row*blocks+j] for row in selected for j in range(blocks)]
    derivatives, base_values = evaluate_channels(batch, [derivative, base_jet], points)
    rows = []
    for t, row in enumerate(selected):
        x = ctx["targets"][row]
        jet, phase, shift_power = (1, 0, 0), 1, 1
        for j in range(blocks):
            z, p = ctx["points"][row*blocks+j], ctx["values"][row*blocks+j]
            d, e = derivatives[t*blocks+j], base_values[t*blocks+j]
            block = (phase*p % n, phase*shift_power*d % n,
                     phase*(width*width*j*p+e-width*j*z*d) % n)
            jet = JET["multiply_jets"](jet, block, n)
            phase = phase*ctx["phase_step"] % n
            shift_power = shift_power*ctx["shift"] % n
        assert jet[0] == source["rows"][row]["product"]
        rows.append({**source["rows"][row], "target_derivative": jet[1],
                     "base_derivative": jet[2], "source_index": row})
    source["metrics"].update(derivative_channel_evaluations=2*len(points),
                             derivative_point_inputs=len(points),
                             selected_jet_rows=len(selected), point_trees=2,
                             base_marking_built=True, **batch.stats())
    return {"rows": rows, "elapsed_ms": 1000*(time.perf_counter()-start)}


def homogeneous_heads(n, rows):
    """A balanced two-channel tree; no deformation coefficients are stored."""
    batch = MonicBatch(n)
    zero_rows = [r for r in rows if r["product"] == 0]
    scale = 1
    for r in rows:
        if r["product"] != 0:
            scale = scale*r["product"] % n
    level = []
    for r in zero_rows:
        v, w = r["x"]*r["target_derivative"] % n, -r["base_derivative"] % n
        level.append(([-v*r["a"] % n, v], [w]))
    allocated = sum(len(q)+len(h) for q, h in level)
    levels = 0
    while len(level) > 1:
        nxt = []
        for i in range(0, len(level)-1, 2):
            q, h = level[i]
            s, t = level[i+1]
            nxt.append((batch.mul(q, s), JET["add_polynomials"](
                batch.mul(h, s), batch.mul(q, t), n)))
        if len(level) % 2:
            nxt.append(level[-1])
        allocated += sum(len(q)+len(h) for q, h in nxt)
        level = nxt
        levels += 1
    q, h = level[0] if level else ([1], [])
    return [scale*x % n for x in q], [scale*x % n for x in h], {
        "zero_rows": len(zero_rows), "head_tree_levels": levels,
        "head_tree_coefficient_slots_allocated": allocated,
        "epsilon_coefficients_constructed": 0, **batch.stats()}


def decode_public_heads(n, rows, length, gcds=None):
    start = time.perf_counter()
    gcds = [math.gcd(r["product"], n) for r in rows] if gcds is None else gcds
    result = {"factor": None, "row_gcds": gcds, "row_count": len(rows)}

    def finish(status, factor=None):
        if factor is not None:
            assert 1 < factor < n and n % factor == 0
        result.update(status=status, factor=factor, elapsed_ms=1000*(time.perf_counter()-start))
        return result

    for d in gcds:
        if 1 < d < n:
            return finish("residual-factor", d)
    q, h, metrics = homogeneous_heads(n, rows)
    result["head_metrics"] = metrics
    if not metrics["zero_rows"]:
        return finish("rows-clear")
    d = math.gcd(q[-1], n)
    if 1 < d < n:
        return finish("head-scale-factor", d)
    if d != 1:
        return finish("multiple-local-root")
    inverse = pow(q[-1], -1, n)
    q, h = [v*inverse % n for v in q], [v*inverse % n for v in h]
    result.update(locator=q, marked=h, decoded_indices=[])
    derivative = [i*q[i] % n for i in range(1, len(q))]
    zero_rows = [r for r in rows if r["product"] == 0]
    batch = MonicBatch(n)
    values, slopes, markings = SHARED["evaluate_three"](
        batch, [q, derivative, h], [r["a"] % n for r in zero_rows])
    for r, value, slope, weight in zip(zero_rows, values, slopes, markings):
        assert value == 0
        d = math.gcd(slope, n)
        if 1 < d < n:
            return finish("tag-derivative-factor", d)
        if d != 1:
            return finish("multiple-row-label")
        index = weight*pow(slope, -1, n) % n
        decoded = {"a": r["a"], "index": index}
        result["decoded_indices"].append(decoded)
        if index < length:
            decoded["status"] = "common-local-index"
            continue
        width = math.isqrt(length)+1
        decoded["recovery"] = RECOVERY(n, list(range(1, width+1)),
                                      [(index+1-j*width) % n for j in range(width)])
        if decoded["recovery"]["factor"] is not None:
            result["head_evaluation_metrics"] = batch.stats()
            return finish("marked-index-factor", decoded["recovery"]["factor"])
    result["head_evaluation_metrics"] = batch.stats()
    return finish("no-proper-labelled-hit")


def source_public_pass(n, base=2):
    start = time.perf_counter()
    b = PREFIX["sixth_width"](n)
    result = {"N": n, "width": b, "base": base, "groups": [], "factor": None}

    def finish(status, factor=None):
        if factor is not None:
            assert 1 < factor < n and n % factor == 0
        result.update(status=status, factor=factor, elapsed_ms=1000*(time.perf_counter()-start))
        return result

    result["prefix"] = PREFIX["factor_prefix"](n)
    if result["prefix"]["factor"] is not None:
        return finish("prefix-factor", result["prefix"]["factor"])
    d = math.gcd(base, n)
    if 1 < d < n:
        return finish("base-factor", d)
    if d != 1:
        return finish("nonunit-base")
    alpha = pow(base, n-1, n)
    for i in range(1, b+1):
        d = math.gcd(alpha-1, n)
        if 1 < d < n:
            return finish("projection-factor", d)
        if d == n:
            return finish("projection-kernel")
        if i >= 2:
            alpha = pow(alpha, i**n.bit_length(), n)
    d = math.gcd(alpha-1, n)
    if 1 < d < n:
        return finish("projection-factor", d)
    if d == n:
        return finish("projection-kernel")
    result["alpha"] = alpha
    short_width = 2*b+1
    step = pow(alpha, short_width, n)
    result["short_pass"] = RECOVERY(n, CENTRE["geometric"](1, alpha, short_width, n),
                                   CENTRE["geometric"](step, step, short_width, n))
    if result["short_pass"]["factor"] is not None:
        return finish("short-period-factor", result["short_pass"]["factor"])
    axis, length, first, group_size = pow(alpha, n, n), 3*b*b+1, 1, 1
    x = axis*pow(alpha, b*b, n) % n
    while first <= b:
        count = min(group_size, b-first+1)
        targets = CENTRE["geometric"](x, axis, count, n)
        source = shared_products(n, alpha, targets, length, min(b*b, math.isqrt(count*length)+1))
        gcds = [math.gcd(r["product"], n) for r in source["rows"]]
        group = {"first_a": first, "source_ms": source["elapsed_ms"],
                 "source_metrics": source["metrics"], "row_gcds": gcds}
        result["groups"].append(group)
        for d in gcds:
            if 1 < d < n:
                return finish("residual-factor", d)
        selected = [i for i, d in enumerate(gcds) if d == n]
        if selected:
            extra = selected_jets(source, selected)
            group["derivative_ms"] = extra["elapsed_ms"]
            for r in extra["rows"]:
                source["rows"][r["source_index"]].update(r)
            for i, r in enumerate(source["rows"]):
                r["a"] = first+i
            decoded = decode_public_heads(n, source["rows"], source["metrics"]["padded_interval"], gcds)
            group["head_decode"] = decoded
            if decoded["factor"] is not None:
                return finish(decoded["status"], decoded["factor"])
            assert decoded["status"] == "no-proper-labelled-hit", decoded
        first += count
        x = x*pow(axis, count, n) % n
        group_size *= 2
    return finish("no-proper-row")


def validate():
    rng = random.Random(SEED)
    source_comparisons = jet_comparisons = head_comparisons = 0
    statuses = {}
    for _ in range(128):
        n = rng.choice((35, 49, 77, 143, 221, 323, 1009))
        while True:
            alpha = rng.randrange(1, n)
            if math.gcd(alpha, n) == 1:
                break
        count, length = rng.randrange(1, 7), rng.randrange(1, 65)
        targets = [rng.randrange(0, n) for _ in range(count)]
        source = shared_products(n, alpha, targets, length)
        selected = [i for i, r in enumerate(source["rows"]) if r["product"] == 0]
        extra = selected_jets(source, selected) if selected else {"rows": []}
        for r in source["rows"]:
            expected = JET["direct_jet"](n, alpha, r["x"], r["length"])
            assert r["product"] == expected[0]
            source_comparisons += 1
        for r in extra["rows"]:
            expected = JET["direct_jet"](n, alpha, r["x"], r["length"])
            assert (r["product"], r["target_derivative"], r["base_derivative"]) == expected
            jet_comparisons += 1
    for p, q, length in ((5, 7, 3), (11, 17, 5), (17, 23, 4), (29, 31, 5)):
        n = p*q
        for _ in range(64):
            rows = []
            for a in range(1, rng.randrange(1, min(p, 8))+1):
                while True:
                    x = rng.randrange(1, n)
                    if math.gcd(x, n) == 1:
                        break
                values = JET["direct_jet"](n, 2, x, length)
                rows.append(dict(zip(("product", "target_derivative", "base_derivative"), values), x=x, a=a))
            actual = decode_public_heads(n, rows, length)
            expected = any(1 < math.gcd((pow(2, k, n)-r["x"]) % n, n) < n
                           for r in rows for k in range(length))
            assert (actual["factor"] is not None) == expected, (rows, actual)
            statuses[actual["status"]] = statuses.get(actual["status"], 0)+1
            # Independent literal full-pair deformation, after local reduction.
            for prime in (p, q):
                local = []
                for r in rows:
                    values = JET["direct_jet"](prime, 2, r["x"] % prime, length)
                    local.append(dict(zip(("product", "target_derivative", "base_derivative"), values),
                                      x=r["x"] % prime, a=r["a"]))
                order = sum(r["product"] == 0 for r in local)
                if order:
                    pairs = [{"product": (r["x"]-pow(2, u, prime)) % prime,
                              "x": r["x"], "target_derivative": 1,
                              "base_derivative": -u*pow(2, u, prime) % prime, "a": r["a"]}
                             for r in local for u in range(length)]
                    literal = TAGGED["tagged_heads"](prime, pairs, order)
                    linear = TAGGED["tagged_heads"](prime, local, order)
                    assert literal[:2] == linear[:2], (prime, pairs, literal, linear)
                    head_comparisons += 1
            if all(math.gcd(r["product"], n) in (1, n) for r in rows):
                order = sum(r["product"] == 0 for r in rows)
                if order:
                    fast = homogeneous_heads(n, rows)
                    dense = TAGGED["tagged_heads"](n, rows, order)
                    assert fast[:2] == dense[:2], (fast, dense)
                    head_comparisons += 1
    parent = json.loads((ROOT/"docs/semiprime-shared-interval-jet-audit.json").read_text())
    control = parent["validation"]["shared_control"]
    rows, n = control["all_rows"], control["N"]
    controls = []
    for kind, chosen in (("all-rows", rows),
                         ("different-row-labels", [r for r in rows if r["a"] in (3, 4)]),
                         ("same-labels-different-indices", [r for r in rows if r["a"] in (9, 13)])):
        actual = decode_public_heads(n, chosen, chosen[0]["length"])
        assert actual["factor"] is not None
        controls.append({"kind": kind, "N": n, **actual})
    small = []
    for a, x in ((1, 32), (2, 9)):
        values = JET["direct_jet"](35, 2, x, 3)
        small.append(dict(zip(("product", "target_derivative", "base_derivative"), values), x=x, a=a))
    actual = decode_public_heads(35, small, 3)
    assert actual["locator"] == [2, 32, 1] and actual["marked"] == [16, 3]
    controls.append({"kind": "original-source-control", "N": 35, **actual})
    # Exercise the lazy saturated path with original public control targets.
    lazy = shared_products(n, control["alpha"],
                           [r["x"] for r in rows if r["a"] in (9, 13)], 3*38*38+1)
    extra = selected_jets(lazy, [0, 1])
    selected_rows = []
    for a, r in zip((9, 13), extra["rows"]):
        r["a"] = a
        selected_rows.append(r)
    actual = decode_public_heads(n, selected_rows, selected_rows[0]["length"])
    assert actual["status"] == "marked-index-factor" and actual["factor"] == 62347
    controls.append({"kind": "lazy-saturated-source-control", "N": n,
                     "residual_source_metrics": lazy["metrics"],
                     "residual_source_ms": lazy["elapsed_ms"],
                     "selected_derivative_ms": extra["elapsed_ms"], **actual})
    # Generic coefficient identities also hold when zero rows are multiple.
    multiple_controls = []
    for prime, alpha, length, xs in ((5, 4, 6, (1, 4)), (7, 2, 9, (1, 2, 4))):
        local = []
        for a, x in enumerate(xs, 1):
            values = JET["direct_jet"](prime, alpha, x, length)
            local.append(dict(zip(("product", "target_derivative", "base_derivative"), values), x=x, a=a))
        order = sum(r["product"] == 0 for r in local)
        pairs = [{"product": (r["x"]-pow(alpha, u, prime)) % prime,
                  "x": r["x"], "target_derivative": 1,
                  "base_derivative": -u*pow(alpha, u, prime) % prime, "a": r["a"]}
                 for r in local for u in range(length)]
        literal = TAGGED["tagged_heads"](prime, pairs, order)
        linear = TAGGED["tagged_heads"](prime, local, order)
        assert literal[:2] == linear[:2]
        multiple_controls.append({"prime": prime, "alpha": alpha, "length": length,
                                  "row_zero_count": order, "head_at_zero_count": literal[0],
                                  "marked_at_zero_count_minus_one": literal[1],
                                  "simple_slopes": False})
    tree_controls = []
    for count in (8, 16, 32):
        # Fixed public target 520 has indices 1 mod 37 and 2 mod 43.
        # Other rows are global aliases. Reference primes stay in validation.
        hybrid = 520
        assert hybrid % 37 == 2 and hybrid % 43 == 4
        targets = [hybrid if a == count//2+1 else 2 for a in range(1, count+1)]
        source = shared_products(37*43, 2, targets, 3)
        assert all(r["product"] == 0 for r in source["rows"])
        extra = selected_jets(source, list(range(count)))
        for a, r in enumerate(extra["rows"], 1):
            r["a"] = a
        actual = decode_public_heads(37*43, extra["rows"], extra["rows"][0]["length"])
        assert actual["status"] == "marked-index-factor"
        depth = (count-1).bit_length()
        slots = (2*depth+4)*2**depth-1
        assert actual["head_metrics"]["head_tree_coefficient_slots_allocated"] == slots
        tree_controls.append({"row_count": count, "head_tree_slot_model": slots,
                              "dense_prefix_capacity": (count+1)**2,
                              "literal_interval": extra["rows"][0]["length"],
                              "source_metrics": source["metrics"], **actual})
    return {"residual_comparisons": source_comparisons, "selected_jet_comparisons": jet_comparisons,
            "head_comparisons": head_comparisons, "independent_small_batches": 256,
            "small_statuses": statuses, "controls": controls,
            "multiple_root_controls": multiple_controls,
            "homogeneous_tree_controls": tree_controls}


def source_inventory():
    parent_path = "docs/semiprime-tagged-pooling-audit.json"
    parent = json.loads((ROOT/parent_path).read_text())
    for path, expected in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected, path
    paths = set(parent["source_sha256"])
    paths.update((parent_path, "RiemannGaussian/SemiprimeSourceHead.lean",
                  "scripts/CheckSemiprimeSourceHead.lean", "scripts/probe_semiprime_source_head.py"))
    return {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def replay():
    validation = validate()
    rng = random.Random(SEED)
    corpus = [(regime, *PREFIX["fresh_pair"](bits, regime, rng))
              for bits in (32, 40, 48) for regime in ("balanced", "small-factor") for _ in range(3)]
    corpus += [("prior-long-control", 44963, 62347), ("prior-long-control", 714107, 1013003),
               ("explicit-base-kernel", 829, 1657)]
    cases = []
    for regime, p, q in corpus:
        actual = source_public_pass(p*q)
        baseline = SHARED["projected_shared_pass"](p*q)
        assert (actual["factor"] is not None) == (baseline["factor"] is not None)
        actual.update(regime=regime, reference_p=p, reference_q=q, input_bits=(p*q).bit_length(),
                      adaptive_shared=baseline)
        cases.append(actual)
    return {"seed": SEED, "scope": "literal source heads, public homogeneous trees and lazy derivative channels",
            "is_complete_semiprime_factorizer": False, "is_bit_complexity_certificate": False,
            "one_sixth_guarantee": "OPEN", "validation": validation, "inputs": cases,
            "input_count": len(cases), "summary": {s: sum(c["status"] == s for c in cases)
                                                  for s in sorted({c["status"] for c in cases})},
            "source_sha256": source_inventory(),
            "limitations": "No dense deformation prefix or full pair matrix is constructed. Original residuals and selected row derivatives are charged, and residual inputs still have B^(3/2) scale. Literal full-source comparisons are validation only. Fixed-base kernels and the total every-run bit-operation proof remain open."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = replay()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"validation_counts": {k: v for k, v in result["validation"].items()
                                           if k.endswith("comparisons") or k == "independent_small_batches"},
                      "input_count": result["input_count"], "summary": result["summary"],
                      "one_sixth_guarantee": result["one_sixth_guarantee"]}, indent=2))


if __name__ == "__main__":
    main()

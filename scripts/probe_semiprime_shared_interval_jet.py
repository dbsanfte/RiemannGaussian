#!/usr/bin/env python3
"""Share exact padded q-factorial jets across public centre-free rows.

Optional research replay. It retains each row's three scalar channels,
shares baby polynomials and the point tree, and grows row batches by powers
of two. Padding eliminates a separate long tail in every row. The remaining
worst-case explicit degree/point input count is O(B^(3/2)), not O(B).
No complete sixth-root factorizer or Lean bit-cost theorem is claimed.
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
JET = runpy.run_path(str(ROOT / "scripts/probe_semiprime_interval_jet.py"))
CENTRE = JET["CENTRE"]
PREFIX = JET["PREFIX"]
RECOVERY = JET["RECOVERY"]
MonicBatch = JET["MonicBatch"]
SEED = 202610030114


def evaluate_three(batch, polynomials, points):
    """One shared monic point tree, with separate derivative remainders."""
    if not points:
        return [[], [], []]
    tree = batch.tree(points)
    outputs = [[], [], []]

    def visit(node, remainders):
        remainders = [batch.mod(f, node[0]) for f in remainders]
        if node[1] is None:
            for out, f in zip(outputs, remainders):
                out.append(f[0] if f else 0)
        else:
            visit(node[1], remainders)
            visit(node[2], remainders)

    visit(tree, polynomials)
    return outputs


def shared_interval_jets(n, alpha, targets, length, width=None):
    """Exact row jets for one padded interval from shared normalized blocks."""
    start = time.perf_counter()
    if length <= 0 or math.gcd(alpha, n) != 1:
        raise ValueError("positive interval and public unit base required")
    targets = list(targets)
    count = len(targets)
    width = max(1, math.isqrt(count*length)+1) if width is None else width
    if width <= 0:
        raise ValueError("positive block width required")
    blocks = (length-1)//width+1
    padded = width*blocks
    batch = MonicBatch(n)
    polynomial, base_jet = JET["baby_polynomial_jet"](alpha, width, n, batch)
    derivative = [(i*polynomial[i]) % n for i in range(1, len(polynomial))]
    shift = pow(pow(alpha, -1, n), width, n)
    points = []
    for x in targets:
        points.extend(CENTRE["geometric"](x, shift, blocks, n))
    values, derivatives, base_values = evaluate_three(
        batch, [polynomial, derivative, base_jet], points)
    jets = []
    phase_step = pow(alpha, width*width, n)
    for row, x in enumerate(targets):
        result = (1, 0, 0)
        phase = shift_power = 1
        for j in range(blocks):
            i = row*blocks+j
            z, p, d, e = points[i], values[i], derivatives[i], base_values[i]
            block_jet = (phase*p % n, phase*shift_power*d % n,
                         phase*(width*width*j*p+e-width*j*z*d) % n)
            result = JET["multiply_jets"](result, block_jet, n)
            phase = phase*phase_step % n
            shift_power = shift_power*shift % n
        jets.append({"x": x, "product": result[0], "target_derivative": result[1],
                     "base_derivative": result[2], "length": padded})
    return {"rows": jets, "elapsed_ms": 1000*(time.perf_counter()-start),
            "metrics": {"row_count": count, "block_width": width, "block_count": blocks,
                        "original_interval": length, "padded_interval": padded,
                        "baby_factors": width, "polynomial_coefficients": len(polynomial),
                        "base_jet_coefficients": len(base_jet), "target_derivative_coefficients": len(derivative),
                        "unique_evaluation_point_inputs": len(points),
                        "three_channel_evaluations": 3*len(points), "point_trees": 1,
                        "tail_factors": 0, "explicit_interval_targets": 0,
                        "explicit_pair_candidates": 0,
                        "reshape_input_count": width+len(points), **batch.stats()}}


def decode_jet(n, row):
    """Decode a computed row without recomputing its original interval."""
    start = time.perf_counter()
    x, length = row["x"], row["length"]
    result = {"x": x, "factor": None, "status": "interval-clear"}
    divisor = math.gcd(row["product"], n)
    if 1 < divisor < n:
        result.update(status="product-factor", factor=divisor)
    elif divisor == n:
        d = math.gcd(row["target_derivative"], n)
        result["derivative_gcd"] = d
        if 1 < d < n:
            result.update(status="derivative-factor", factor=d)
        elif d == n:
            result["status"] = "multiple-local-root"
        else:
            denominator = x*row["target_derivative"] % n
            assert math.gcd(denominator, n) == 1
            index = -row["base_derivative"]*pow(denominator, -1, n) % n
            result["decoded_index"] = index
            if index < length:
                result["status"] = "common-local-index"
            else:
                width = math.isqrt(length)+1
                recovery = RECOVERY(n, list(range(1, width+1)),
                                    [(index+1-j*width) % n for j in range(width)])
                result["index_recovery"] = recovery
                if recovery["factor"] is not None:
                    offset = recovery["point_index"]*width+recovery["root_index"]
                    assert math.gcd(index-offset, n) == recovery["factor"]
                    result.update(status="crt-index-factor", factor=recovery["factor"],
                                  recovered_index=offset)
                else:
                    result["status"] = "no-proper-index-hit"
    result["elapsed_ms"] = 1000*(time.perf_counter()-start)
    return result


def projected_shared_pass(n, base=2, adaptive=True):
    """Public setup and shared padded row groups; no reference factors."""
    start = time.perf_counter()
    b = PREFIX["sixth_width"](n)
    result = {"N": n, "width": b, "base": base, "factor": None,
              "adaptive": adaptive, "groups": [], "examined_rows": []}

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
    result["short_pass"] = RECOVERY(
        n, CENTRE["geometric"](1, alpha, short_width, n),
        CENTRE["geometric"](step, step, short_width, n))
    if result["short_pass"]["factor"] is not None:
        return finish("short-period-factor", result["short_pass"]["factor"])
    axis = pow(alpha, n, n)
    x = axis*pow(alpha, b*b, n) % n
    a, group_size, length = 1, 1 if adaptive else b, 3*b*b+1
    while a <= b:
        count = min(group_size, b-a+1)
        targets = CENTRE["geometric"](x, axis, count, n)
        width = min(b*b, math.isqrt(count*length)+1)
        shared = shared_interval_jets(n, alpha, targets, length, width)
        assert length <= shared["metrics"]["padded_interval"] <= 4*b*b
        result["groups"].append({"first_a": a, "elapsed_ms": shared["elapsed_ms"],
                                 "metrics": shared["metrics"]})
        for i, row in enumerate(shared["rows"]):
            decoded = decode_jet(n, row)
            decoded.update(a=a+i)
            result["examined_rows"].append(decoded)
            if decoded["factor"] is not None:
                return finish("shared-interval-factor", decoded["factor"])
            assert decoded["status"] in ("interval-clear", "common-local-index")
        a += count
        x = x*pow(axis, count, n) % n
        group_size *= 2
    return finish("no-proper-row")


def validate():
    rng = random.Random(SEED)
    checked = 0
    for _ in range(192):
        n = rng.choice((35, 49, 77, 143, 221, 323, 1009, 2803308161))
        while True:
            alpha = rng.randrange(1, n)
            if math.gcd(alpha, n) == 1:
                break
        count, length = rng.randrange(1, 9), rng.randrange(1, 161)
        targets = [rng.randrange(n) for _ in range(count)]
        if checked % 3 == 0:
            targets[-1] = pow(alpha, rng.randrange(length), n)
        actual = shared_interval_jets(n, alpha, targets, length)
        for row in actual["rows"]:
            expected = JET["direct_jet"](n, alpha, row["x"], row["length"])
            assert tuple(row[k] for k in
                         ("product", "target_derivative", "base_derivative")) == expected
            checked += 1
    n, alpha, b = 2803308161, 1823692905, 38
    targets = [pow(alpha, a*n+b*b, n) for a in range(1, b+1)]
    width = math.isqrt(b*(3*b*b+1))+1
    shared = shared_interval_jets(n, alpha, targets, 3*b*b+1, width)
    for a, row in enumerate(shared["rows"], 1):
        expected = JET["direct_jet"](n, alpha, row["x"], row["length"])
        assert tuple(row[k] for k in
                     ("product", "target_derivative", "base_derivative")) == expected
        row["a"] = a
        row["decoder"] = decode_jet(n, row)
        checked += 1
    saturated = [row for row in shared["rows"] if row["product"] == 0]
    assert len(saturated) >= 2
    pooled = (1, 0, 0)
    for row in shared["rows"]:
        pooled = JET["multiply_jets"](pooled, tuple(row[k] for k in
                     ("product", "target_derivative", "base_derivative")), n)
    assert pooled == (0, 0, 0)
    assert any(row["decoder"]["status"] == "crt-index-factor" for row in saturated)
    return {"exact_row_jet_comparisons": checked,
            "shared_control": {"N": n, "alpha": alpha, "metrics": shared["metrics"],
                               "elapsed_ms": shared["elapsed_ms"],
                               "saturated_rows": saturated, "pooled_first_jet": pooled,
                               "all_rows": shared["rows"]}}


def replay():
    validation = validate()
    rng = random.Random(SEED)
    corpus = [(bits, regime, *PREFIX["fresh_pair"](bits, regime, rng))
              for bits in (32, 40, 48) for regime in ("balanced", "small-factor")
              for _ in range(3)]
    corpus += [(32, "prior-long-control", 44963, 62347),
               (40, "prior-long-control", 714107, 1013003),
               (21, "explicit-base-kernel", 829, 1657)]
    cases = []
    for _, regime, p, q in corpus:
        adaptive = projected_shared_pass(p*q)
        all_rows = projected_shared_pass(p*q, adaptive=False)
        rowwise = JET["projected_cover_rows"](p*q)
        baseline = CENTRE["centre_free_pass"](p*q)
        assert len({r["factor"] is not None for r in
                    (adaptive, all_rows, rowwise, baseline)}) == 1
        assert all(r["status"] != "no-proper-row" for r in
                   (adaptive, all_rows, rowwise, baseline))
        adaptive.update(reference_p=p, reference_q=q, input_bits=(p*q).bit_length(),
                        regime=regime, shared_all_rows=all_rows,
                        rowwise_interval=rowwise, standard_reshape=baseline)
        cases.append(adaptive)
    sources = ["RiemannGaussian/SemiprimeSharedIntervalJet.lean",
               "scripts/CheckSemiprimeSharedIntervalJet.lean",
               "scripts/probe_semiprime_shared_interval_jet.py"]
    statuses = sorted({c["status"] for c in cases})
    return {"seed": SEED, "scope": "shared padded interval jets with adaptive row groups",
            "is_complete_semiprime_factorizer": False, "is_bit_complexity_certificate": False,
            "one_sixth_guarantee": "OPEN", "validation": validation,
            "inputs": cases, "input_count": len(cases),
            "summary": {s: sum(c["status"] == s for c in cases) for s in statuses},
            "source_sha256": {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
                              for p in sources},
            "limitations": "Each comparator builds and times its own public setup. Private factors are attached after computation. Row scalars remain separate. Shared polynomial/point inputs retain the B^(3/2) reshape scale, and the GMP engine/bit cost remain unverified. Fixed-base projection kernels remain exposed."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = replay()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"exact_row_jet_comparisons": result["validation"]["exact_row_jet_comparisons"],
                      "input_count": result["input_count"], "summary": result["summary"],
                      "one_sixth_guarantee": result["one_sixth_guarantee"]}, indent=2))


if __name__ == "__main__":
    main()

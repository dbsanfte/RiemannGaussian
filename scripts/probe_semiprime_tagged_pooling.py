#!/usr/bin/env python3
"""Preserve colliding row labels in higher deformation coefficients.

Optional research replay. A scalar diagonal detects unequal local zero-row
counts. Equal counts retain a row-locator polynomial and a marked exponent
polynomial. The source rows and every coefficient update are charged.
The current shared row source is B^(3/2), and a dense prefix for the two
heads may itself be quadratic. This is not a sixth-root factorizer.
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
SHARED = runpy.run_path(str(ROOT / "scripts/probe_semiprime_shared_interval_jet.py"))
JET = SHARED["JET"]
CENTRE = SHARED["CENTRE"]
PREFIX = SHARED["PREFIX"]
RECOVERY = SHARED["RECOVERY"]
MonicBatch = SHARED["MonicBatch"]
SEED = 202610030201


def diagonal(n, rows, batch):
    level = [[r["product"], r["x"]*r["target_derivative"] % n] for r in rows]
    while len(level) > 1:
        nxt = [batch.mul(level[i], level[i+1]) for i in range(0, len(level)-1, 2)]
        if len(level) % 2:
            nxt.append(level[-1])
        level = nxt
    return level[0] if level else [1]


def tagged_heads(n, rows, order):
    """Literal truncated bivariate recurrence; every internal slot is paid."""
    q = [[1]]+[[] for _ in range(order)]
    h = [[] for _ in range(order)]
    updates = 0

    def scaled(a, scalar):
        nonlocal updates
        updates += len(a)
        return [scalar*x % n for x in a]

    def tag(a, slope, label):
        nonlocal updates
        if not a:
            return []
        out = [0]*(len(a)+1)
        for i, value in enumerate(a):
            out[i] = (out[i]-slope*label*value) % n
            out[i+1] = (out[i+1]+slope*value) % n
            updates += 2
        return out

    def added(left, right):
        nonlocal updates
        updates += max(len(left), len(right))
        return JET["add_polynomials"](left, right, n)

    for row in rows:
        r, v, w, a = (row["product"], row["x"]*row["target_derivative"] % n,
                       -row["base_derivative"] % n, row["a"])
        qn, hn = [], []
        for j in range(order+1):
            value = scaled(q[j], r)
            if j:
                value = added(value, tag(q[j-1], v, a))
            qn.append(value)
            if j < order:
                marker = added(scaled(h[j], r), scaled(q[j], w))
                if j:
                    marker = added(marker, tag(h[j-1], v, a))
                hn.append(marker)
        q, h = qn, hn
    return q[order], h[order-1], {
        "coefficient_updates": updates,
        "product_prefix_capacity": (order+1)*(order+2)//2,
        "marker_prefix_capacity": order*(order+1)//2,
        "combined_prefix_capacity": (order+1)**2,
        "head_product_coefficients": len(q[order]),
        "head_marker_coefficients": len(h[order-1])}


def pool_rows(n, rows, length):
    """The constructor receives public row triples and literal labels only."""
    start = time.perf_counter()
    batch = MonicBatch(n)
    diag = diagonal(n, rows, batch)
    result = {"factor": None, "row_count": len(rows), "diagonal_coefficients": diag,
              "coefficient_gcds": 0}

    def finish(status, factor=None):
        if factor is not None:
            assert 1 < factor < n and n % factor == 0
        result.update(status=status, factor=factor, elapsed_ms=1000*(time.perf_counter()-start),
                      polynomial_metrics=batch.stats())
        return result

    order = None
    for i, value in enumerate(diag):
        d = math.gcd(value, n)
        result["coefficient_gcds"] += 1
        if 1 < d < n:
            result["first_order"] = i
            return finish("unequal-count-factor", d)
        if d == 1:
            order = i
            break
    if order is None:
        return finish("no-unit-or-proper-head")
    result["first_order"] = order
    if order == 0:
        return finish("pooled-clear")
    q, h, metrics = tagged_heads(n, rows, order)
    assert q[-1] == diag[order]
    inv = pow(diag[order], -1, n)
    locator, marked = [x*inv % n for x in q], [x*inv % n for x in h]
    result.update(locator=locator, marked=marked, coefficient_metrics=metrics,
                  row_evaluation_gcds=0, index_decodes=[])
    derivative = [i*locator[i] % n for i in range(1, len(locator))]
    labels = [row["a"] % n for row in rows]
    values, slopes, markings = SHARED["evaluate_three"](
        batch, [locator, derivative, marked], labels)
    for row, value, slope, weight in zip(rows, values, slopes, markings):
        d = math.gcd(value, n)
        result["row_evaluation_gcds"] += 1
        if 1 < d < n:
            result["witness_row"] = row["a"]
            return finish("different-row-label-factor", d)
        if d != n:
            continue
        ds = math.gcd(slope, n)
        result["row_evaluation_gcds"] += 1
        if 1 < ds < n:
            return finish("row-derivative-factor", ds)
        if ds != 1:
            return finish("multiple-row-label")
        index = weight*pow(slope, -1, n) % n
        decoded = {"a": row["a"], "index": index}
        result["index_decodes"].append(decoded)
        if index < length:
            decoded["status"] = "common-local-index"
            continue
        width = math.isqrt(length)+1
        recovery = RECOVERY(n, list(range(1, width+1)),
                            [(index+1-j*width) % n for j in range(width)])
        decoded["recovery"] = recovery
        if recovery["factor"] is not None:
            return finish("marked-index-factor", recovery["factor"])
    return finish("no-proper-labelled-hit")


def pooled_public_pass(n, base=2):
    start = time.perf_counter()
    b = PREFIX["sixth_width"](n)
    result = {"N": n, "width": b, "base": base, "factor": None}

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
    axis = pow(alpha, n, n)
    targets = CENTRE["geometric"](axis*pow(alpha, b*b, n) % n, axis, b, n)
    source = SHARED["shared_interval_jets"](
        n, alpha, targets, 3*b*b+1, min(b*b, math.isqrt(b*(3*b*b+1))+1))
    for a, row in enumerate(source["rows"], 1):
        row["a"] = a
    result["source"] = {"metrics": source["metrics"], "elapsed_ms": source["elapsed_ms"]}
    result["pool"] = pool_rows(n, source["rows"], source["metrics"]["padded_interval"])
    return finish(result["pool"]["status"], result["pool"]["factor"])


def validate():
    rng = random.Random(SEED)
    checked = 0
    statuses = {}
    for p, q, length in ((5, 7, 3), (11, 17, 5), (17, 23, 4), (29, 31, 5)):
        n = p*q
        for _ in range(64):
            count = rng.randrange(1, min(p, 8))
            rows = []
            for a in range(1, count+1):
                while True:
                    x = rng.randrange(1, n)
                    if math.gcd(x, n) == 1:
                        break
                values = JET["direct_jet"](n, 2, x, length)
                rows.append(dict(zip(("product", "target_derivative", "base_derivative"), values),
                                 x=x, a=a))
            actual = pool_rows(n, rows, length)
            expected = any(1 < math.gcd((pow(2, k, n)-row["x"]) % n, n) < n
                           for row in rows for k in range(length))
            assert (actual["factor"] is not None) == expected, (p, q, rows, actual)
            checked += 1
            statuses[actual["status"]] = statuses.get(actual["status"], 0)+1
    shared = json.loads((ROOT / "docs/semiprime-shared-interval-jet-audit.json").read_text())
    control = shared["validation"]["shared_control"]
    rows = control["all_rows"]
    n = control["N"]
    controls = []
    for kind, selected in (("unequal-counts", rows),
                            ("equal-counts-different-labels", [r for r in rows if r["a"] in (3, 4)]),
                            ("same-labels-different-indices", [r for r in rows if r["a"] in (9, 13)])):
        result = pool_rows(n, selected, selected[0]["length"])
        result.update(kind=kind, N=n, source_row_labels=[r["a"] for r in selected])
        assert result["factor"] is not None
        controls.append(result)
    assert controls[0]["first_order"] == 7 and controls[0]["status"] == "unequal-count-factor"
    assert controls[1]["first_order"] == 1 and controls[1]["status"] == "different-row-label-factor"
    assert controls[2]["first_order"] == 2 and controls[2]["status"] == "marked-index-factor"
    small_rows = []
    for a, x in ((1, 32), (2, 9)):
        values = JET["direct_jet"](35, 2, x, 3)
        small_rows.append(dict(zip(("product", "target_derivative", "base_derivative"), values),
                               x=x, a=a))
    small = pool_rows(35, small_rows, 3)
    assert small["locator"] == [2, 32, 1] and small["marked"] == [16, 3]
    assert (16+22) % 35 == 3
    small.update(kind="equal-label-sum-control", N=35, source_rows=small_rows,
                 reference_indices=[16, 22], collapsed_index_sum=3)
    controls.append(small)
    return {"independent_small_batches": checked, "small_statuses": statuses,
            "controls": controls, "historical_control_source":
              "docs/semiprime-shared-interval-jet-audit.json"}


def source_inventory():
    """Pin all project proof imports and the frozen source/control chain."""
    parent_path = "docs/semiprime-shared-interval-jet-audit.json"
    parent = json.loads((ROOT/parent_path).read_text())
    for path, expected in parent["source_sha256"].items():
        actual = hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
        assert actual == expected, f"frozen shared-audit input changed: {path}"
    sources = set(parent["source_sha256"])
    sources.update((parent_path, "scripts/CheckSemiprimeTaggedPooling.lean",
                    "scripts/probe_semiprime_tagged_pooling.py",
                    "lake-manifest.json", "lean-toolchain"))
    pending = ["RiemannGaussian/SemiprimeTaggedPooling.lean"]
    seen = set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        sources.add(path)
        for line in (ROOT/path).read_text().splitlines():
            if line.startswith("import RiemannGaussian."):
                pending.append(line.split()[1].replace(".", "/")+".lean")
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
            for path in sorted(sources)}


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
        actual = pooled_public_pass(p*q)
        baseline = SHARED["projected_shared_pass"](p*q)
        assert (actual["factor"] is not None) == (baseline["factor"] is not None)
        actual.update(reference_p=p, reference_q=q, input_bits=(p*q).bit_length(),
                      regime=regime, adaptive_shared=baseline)
        cases.append(actual)
    statuses = sorted({c["status"] for c in cases})
    return {"seed": SEED, "scope": "higher coefficient pooling with row tags and exponent markings",
            "is_complete_semiprime_factorizer": False, "is_bit_complexity_certificate": False,
            "one_sixth_guarantee": "OPEN", "validation": validation,
            "inputs": cases, "input_count": len(cases),
            "summary": {s: sum(c["status"] == s for c in cases) for s in statuses},
            "source_sha256": source_inventory(),
            "limitations": "Source rows and coefficient arithmetic are charged. The source still has B^(3/2) inputs. The dense bivariate recurrence may store quadratic prefixes even though its final two heads have O(B) coefficients. Equal label sums alone lose the factor-bearing index orientation. Fixed-base kernels remain exposed. No every-run bit-cost theorem is certified."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = replay()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"small_batches": result["validation"]["independent_small_batches"],
                      "input_count": result["input_count"], "summary": result["summary"],
                      "one_sixth_guarantee": result["one_sixth_guarantee"]}, indent=2))


if __name__ == "__main__":
    main()

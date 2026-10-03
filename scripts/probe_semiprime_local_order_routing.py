#!/usr/bin/env python3
"""Charged original-unit short extraction after universal seed routing.

Both short batches construct only 2B giant and 2B baby records. Exact
shared roots are deflated by the existing polynomial backend. A nonfactor
outcome retains a large kernel or projected-long certificate. This is not
a complete semiprime factorizer or a proved bit-complexity algorithm.
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
SEEDS = runpy.run_path(str(ROOT/"scripts/probe_semiprime_seed_lcm.py"))
BATCH = runpy.run_path(str(ROOT/"scripts/probe_semiprime_batch_recovery.py"))
PARENT = "docs/semiprime-seed-lcm-audit.json"
REPLAY_ID = 202610031001


def short_batch(n, base, block):
    """Giant roots and baby targets, matching the formal cover orientation."""
    step = pow(base, block, n)
    roots, targets = [], []
    giant, baby = step, 1
    for i in range(block):
        roots.append(giant)
        targets.append(baby)
        if i+1 < block:
            giant = giant*step % n
            baby = baby*base % n
    result = BATCH["recovery"](n, roots, targets)
    result["construction"] = dict(root_records=block, target_records=block,
                                  modular_powers=1,
                                  modular_multiplications=2*max(block-1, 0),
                                  cartesian_pair_candidates=0)
    assert result["metrics"]["gcd_calls"] <= 2*block
    assert result["metrics"]["pair_products"] == 0
    return result


def public_route(n):
    start = time.perf_counter()
    if n < 4:
        raise ValueError("semiprime input N>=4 required")
    width = SEEDS["PREFIX"]["sixth_width"](n)
    block = 2*width
    metrics = dict(outer_sixth_root_queries=1, outer_square_root_queries=1,
                   refinement_unit_gcds=0, raw_power_queries=0,
                   short_batches=0, short_source_powers=0,
                   short_source_multiplications=0, short_gcds=0,
                   projection_stage_powers=0, projection_exponent_queries=0,
                   projection_gcds=0, explicit_grid_candidates=0)
    result = dict(N=n, width=width, block=block, order_cap=block*block,
                  factor=None, base=None, metrics=metrics)

    def finish(status, factor=None):
        if factor is not None:
            assert 1 < factor < n and n % factor == 0
        assert metrics["short_batches"] <= 2
        metrics["refinement_batch_and_projection_gcds"] = (
            metrics["short_gcds"]+metrics["projection_gcds"])
        assert metrics["refinement_batch_and_projection_gcds"] <= 9*width+1
        metrics["all_refinement_gcds"] = (
            metrics["refinement_batch_and_projection_gcds"]+metrics["refinement_unit_gcds"])
        assert metrics["all_refinement_gcds"] <= 9*width+2
        result.update(status=status, factor=factor,
                      elapsed_ms=1000*(time.perf_counter()-start))
        return result

    def run_short(base):
        actual = short_batch(n, base, block)
        metrics["short_batches"] += 1
        metrics["short_source_powers"] += actual["construction"]["modular_powers"]
        metrics["short_source_multiplications"] += actual["construction"]["modular_multiplications"]
        metrics["short_gcds"] += actual["metrics"]["gcd_calls"]
        return actual

    square = math.isqrt(n)
    if square*square == n:
        return finish("square-factor", square)
    seed = SEEDS["public_route"](n)
    result["seed_route"] = seed
    if seed["factor"] is not None:
        return finish("seed-"+seed["status"], seed["factor"])
    if seed["status"] != "certified-large-order":
        return finish("unresolved-seed-route")
    base = seed["large_base"]
    result["base"] = base
    metrics["refinement_unit_gcds"] += 1
    if math.gcd(base, n) != 1:
        return finish("unresolved-nonunit")
    original = run_short(base)
    result["original_short"] = original
    if original["factor"] is not None:
        return finish("original-short-factor", original["factor"])
    metrics["raw_power_queries"] += 1
    raw = pow(base, n-1, n)
    result["raw"] = raw
    if raw == 1:
        return finish("certified-large-kernel")

    # Compute the full retained trace once, then scan its actual residuals.
    # Each stage reuses the preceding power; exponent construction is timed.
    repetitions = n.bit_length()
    alpha, trace = raw, [raw]
    for stage in range(1, width+1):
        exponent = stage**repetitions
        metrics["projection_exponent_queries"] += 1
        alpha = pow(alpha, exponent, n)
        metrics["projection_stage_powers"] += 1
        trace.append(alpha)
    checked = []
    result["projection"] = dict(repetitions=repetitions, retained_values=trace,
                                checked_stages=checked, final_alpha=alpha)
    for stage, value in enumerate(trace):
        metrics["projection_gcds"] += 1
        divisor = math.gcd((value-1) % n, n)
        checked.append(dict(stage=stage, gcd=divisor))
        if 1 < divisor < n:
            return finish("projection-factor", divisor)
    assert len(checked) == width+1 and checked[-1]["gcd"] == 1
    projected = run_short(alpha)
    result["projected_short"] = projected
    if projected["factor"] is not None:
        return finish("projected-short-factor", projected["factor"])
    return finish("certified-projected-long")


def check_route(actual, p, q):
    """Independent local-order validation outside algorithm timing."""
    from sympy import factorint, n_order

    n, width, cap = p*q, actual["width"], actual["order_cap"]
    assert actual["N"] == n and (width-1)**6 < n <= width**6
    assert not actual["status"].startswith("unresolved")
    if actual["factor"] is not None:
        assert actual["factor"] in (p, q)
        return
    assert p != q
    base = actual["base"]
    lp, lq = int(n_order(base, p)), int(n_order(base, q))
    assert lp > cap and lq > cap
    if actual["status"] == "certified-large-kernel":
        assert pow(base, n-1, n) == 1
        order = math.lcm(lp, lq)
        assert (p-1) % order == (q-1) % order == 0
    else:
        assert actual["status"] == "certified-projected-long"
        alpha = actual["projection"]["final_alpha"]
        ap, aq = int(n_order(alpha, p)), int(n_order(alpha, q))
        assert pow(base, n-1, n) != 1 and math.gcd(alpha-1, n) == 1
        assert ap > cap and aq > cap and math.gcd(ap, aq) == 1
        assert all(int(r) > width for r in factorint(ap))
        assert all(int(r) > width for r in factorint(aq))


def validate():
    from sympy import primerange

    primes = list(primerange(2, 200))
    counts, squares = Counter(), 0
    for i, p in enumerate(primes):
        for q in primes[i:]:
            actual = public_route(p*q)
            check_route(actual, p, q)
            counts[actual["status"]] += 1
            squares += int(p == q)
    controls = []
    for p, q in ((13367, 164511353), (59, 233), (2207, 6619), (29, 101),
                 (17, 41), (20543, 61627)):
        actual = public_route(p*q)
        check_route(actual, p, q)
        actual.update(reference_p=p, reference_q=q)
        controls.append(actual)
    assert controls[0]["status"] == "original-short-factor" and controls[0]["factor"] == 13367
    assert controls[0]["seed_route"]["seed_moduli"] == [1, 41]
    assert controls[3]["status"] == "original-short-factor" and controls[3]["factor"] == 29
    assert controls[2]["status"] == "projection-factor" and controls[2]["factor"] == 2207
    assert controls[5]["status"] == "certified-large-kernel"
    return dict(semiprime_cases=sum(counts.values()), prime_squares=squares,
                status_counts=dict(sorted(counts.items())), unresolved_cases=0, controls=controls)


def source_inventory():
    parent = json.loads((ROOT/PARENT).read_text())
    for path, expected in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT, "RiemannGaussian/SemiprimeLocalOrderRouting.lean",
                  "scripts/CheckSemiprimeLocalOrderRouting.lean",
                  "scripts/probe_semiprime_local_order_routing.py"))
    assert "scripts/probe_semiprime_batch_recovery.py" in paths
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources = source_inventory()
    validation = validate()
    inputs = []
    for previous in json.loads((ROOT/PARENT).read_text())["inputs"]:
        actual = public_route(previous["N"])
        check_route(actual, previous["reference_p"], previous["reference_q"])
        actual.update(regime=previous["regime"], reference_p=previous["reference_p"],
                      reference_q=previous["reference_q"])
        inputs.append(actual)
    result = dict(replay_id=REPLAY_ID, scope="universal N-only factor-or-two-large-local-periods routing",
                  is_complete_semiprime_factorizer=False, is_bit_complexity_certificate=False,
                  one_sixth_guarantee="OPEN", validation=validation, inputs=inputs,
                  input_count=len(inputs), factor_count=sum(c["factor"] is not None for c in inputs),
                  summary=dict(sorted(Counter(c["status"] for c in inputs).items())),
                  unresolved_count=sum(c["status"].startswith("unresolved") for c in inputs),
                  source_sha256=sources,
                  timing_protocol="All N-specific sixth roots and square checks (including the repeated seed-wrapper work), the complete seed procedure, both constructed geometric lists, sorting/deduplication/shared-root identification, polynomial/derivative/remainder work, lazy witness recovery, unit check, raw power, every constructed staged exponent/power, the retained trace and its GCDs are timed. Reference primes, orders and validation are outside timing.",
                  limitations="Kernel and projected-long certificates are nonfactor outcomes. Large-order extraction and the complete every-run bit backend remain open. The replay sorts distinct targets while Lean scans the supplied list order; it certifies coverage and resource categories, not equality of first returned factors. No fresh random corpus or full matrix is generated.")
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: result[k] for k in ("input_count", "factor_count", "summary", "unresolved_count", "one_sixth_guarantee")}, indent=2))
    print(json.dumps({k: v for k, v in validation.items() if k != "controls"}, indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Universal signed-multiplier recovery with an explicitly quadratic stream.

The whole public procedure receives N alone. One fixed baby polynomial is
shared by every scaled row. Private factors and local periods enter only
the independent checks after timing. A complete sixth-root bit price is open.
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
PARENT_AUDIT = "docs/semiprime-bit-power-walk-audit.json"
BIT = runpy.run_path(str(ROOT/"scripts/probe_semiprime_bit_power_walk.py"))
PARENT = BIT["PARENT"]
BATCH, WINDOW = PARENT["BATCH"], PARENT["WINDOW"]
REPLAY_ID = 202610032201


class CachedDetector:
    """Build one distinct-root polynomial, then stream complete target rows."""

    def __init__(self, n, roots):
        self.n, self.roots = n, roots
        self.xs, self.root_indices = BATCH["distinct_residues"](n, roots)
        self.batch = BATCH["MonicBatch"](n)
        self.polynomial = self.batch.tree(self.xs)[0]
        self.derivative = None
        self.metrics = Counter(root_polynomials=1, derivative_polynomials=0,
                               derivative_coefficients=0, rows_evaluated=0,
                               input_points=0, distinct_points=0, shared_points=0,
                               column_gcds=0, leaf_gcds=0, witness_remainders=0,
                               recovery_pair_differences=0, whole_modulus_columns=0)

    def row(self, points):
        n = self.n
        ys, point_indices = BATCH["distinct_residues"](n, points)
        shared, ordinary = [], []
        i = 0
        for j, y in enumerate(ys):
            while i < len(self.xs) and self.xs[i] < y:
                i += 1
            (shared if i < len(self.xs) and self.xs[i] == y else ordinary).append(j)
        values = [1]*len(ys)
        for j, value in zip(ordinary,
                            self.batch.evaluate(self.polynomial, [ys[j] for j in ordinary])):
            values[j] = value
        if shared:
            if self.derivative is None:
                self.derivative = [(i*self.polynomial[i]) % n
                                   for i in range(1, len(self.polynomial))]
                self.metrics["derivative_polynomials"] += 1
                self.metrics["derivative_coefficients"] += len(self.derivative)
            for j, value in zip(shared,
                                self.batch.evaluate(self.derivative, [ys[j] for j in shared])):
                values[j] = value
        self.metrics.update(rows_evaluated=1, input_points=len(points),
                            distinct_points=len(ys), shared_points=len(shared))
        result = dict(factor=None)
        before_gcds = self.metrics["column_gcds"]+self.metrics["leaf_gcds"]
        for j, (y, value) in enumerate(zip(ys, values)):
            self.metrics["column_gcds"] += 1
            divisor = math.gcd(value, n)
            if divisor == 1:
                continue
            whole = divisor == n
            if whole:
                self.metrics["whole_modulus_columns"] += 1
            for i, x in enumerate(self.xs):
                if x == y:
                    continue
                self.metrics["recovery_pair_differences"] += 1
                if whole:
                    self.metrics["leaf_gcds"] += 1
                    divisor = math.gcd((y-x) % n, n)
                    if 1 < divisor < n:
                        break
                else:
                    self.metrics["witness_remainders"] += 1
                    if (y-x) % divisor == 0:
                        break
            else:
                raise AssertionError("nonunit deflated product has no proper witness")
            assert 1 < divisor < n and n % divisor == 0
            result = dict(factor=divisor, root_index=self.root_indices[i],
                          point_index=point_indices[j], root=self.xs[i], point=y,
                          column_value=value, stage="leaf" if whole else "column")
            break
        gcds = self.metrics["column_gcds"]+self.metrics["leaf_gcds"]-before_gcds
        assert gcds <= len(self.xs)+len(ys)
        result.update(signals=values, ordered_points=ys, gcd_calls=gcds)
        return result


def build_multiplier_source(window):
    """Public centre/step recurrences; no local order or offset is queried."""
    n, width, beta = window["N"], window["width"], window["target"]
    roots = [record[0] for record in window["babies"]]
    inverse = pow(beta, -1, n)
    max_cache_product_bits = 0
    steps = []
    for value, _ in window["giants"]:
        product = inverse*value
        max_cache_product_bits = max(max_cache_product_bits, product.bit_length())
        steps.append(product % n)
    centres, positive, negative = [], beta, inverse
    for k in range(1, width+1):
        centres.extend((positive, negative))
        if k < width:
            products = positive*beta, negative*inverse
            max_cache_product_bits = max(max_cache_product_bits,
                                         *(v.bit_length() for v in products))
            positive, negative = (v % n for v in products)
    detector = CachedDetector(n, roots)
    summaries, factor, successful = [], None, None
    max_point_product_bits = 0
    for centre_index, centre in enumerate(centres):
        points = []
        for step in steps:
            product = centre*step
            max_point_product_bits = max(max_point_product_bits, product.bit_length())
            points.append(product % n)
        row = detector.row(points)
        summaries.append(dict(multiplier=centre_index//2+1, negative=bool(centre_index % 2),
                              gcd_calls=row["gcd_calls"], distinct_points=len(row["ordered_points"]),
                              signal_sha256=hashlib.sha256(json.dumps(row["signals"]).encode()).hexdigest()))
        if row["factor"] is not None:
            factor = row["factor"]
            successful = {key: value for key, value in row.items()
                          if key not in ("signals", "ordered_points")}
            successful.update(multiplier=centre_index//2+1, negative=bool(centre_index % 2),
                              centre=centre, step=steps[row["point_index"]],
                              baby_label=window["babies"][row["root_index"]][1],
                              block_label=window["giants"][row["point_index"]][1])
            break
    metrics = dict(detector.metrics)
    metrics.update(detector.batch.stats())
    metrics.update(gcd_calls=metrics["column_gcds"]+metrics["leaf_gcds"],
                   gcd_bound=8*width**2, polynomial_degree=len(detector.polynomial)-1,
                   distinct_roots=len(detector.xs), full_expanded_points=len(centres)*len(steps),
                   constructed_point_products=len(summaries)*len(steps),
                   cache_modular_products=4*width-2, cache_modular_reductions=4*width-2,
                   cache_modular_inverses=1, new_centre_powers=0,
                   max_cache_product_bits=max_cache_product_bits,
                   max_point_product_bits=max_point_product_bits,
                   retained_cache_residues=len(roots)+len(steps)+len(centres),
                   represented_full_pairs=len(roots)*len(steps)*len(centres),
                   explicit_pair_grid_products=0, is_complete_bit_certificate=False)
    assert len(roots) == len(steps) == len(centres) == 2*width
    assert metrics["polynomial_degree"] <= 2*width
    assert metrics["gcd_calls"] <= len(summaries)*(len(detector.xs)+len(steps)) <= 8*width**2
    assert metrics["constructed_point_products"] <= 4*width**2
    assert max(max_cache_product_bits, max_point_product_bits) <= 2*n.bit_length()
    return dict(N=n, width=width, roots=roots, steps=steps, centres=centres,
                rows=summaries, factor=factor, successful_row=successful, metrics=metrics)


def public_packet(n):
    """Time all public construction, old stages, new rows and transport."""
    start = time.perf_counter()
    parent = BIT["public_packet"](n)
    factor, source = parent["factor"], None
    metrics = dict(new_multiplier_sources=0, leaf_candidate_gcds=0,
                   transport_order_powers=0, transport_square_roots=0, transport_gcds=0)
    if factor is None:
        window = parent["parent"]["source"]
        assert window is not None and window["factor"] is None
        source = build_multiplier_source(window)
        metrics["new_multiplier_sources"] += 1
        if source["factor"] is not None:
            trace = parent["parent"]["parent"]["source"]["trace"]
            factor = WINDOW["PARENT"]["lift_factor"](trace, source["factor"], metrics)
    if factor is not None:
        assert 1 < factor < n and n % factor == 0
    return dict(N=n, width=parent["width"], parent=parent, source=source, factor=factor,
                status="factor" if factor is not None else "failure",
                metrics=metrics, elapsed_ms=1000*(time.perf_counter()-start))


def check_packet(actual, p, q):
    """Private primality/period/offset acquisition occurs after timing."""
    PARENT["check_packet"](actual["parent"], p, q)
    assert actual["N"] == p*q and actual["factor"] in (p, q)
    source = actual["source"]
    if source is None:
        assert actual["factor"] == actual["parent"]["factor"]
        return
    assert actual["parent"]["factor"] is None
    reference = actual["parent"]["residue_reference"]
    window = actual["parent"]["parent"]["source"]
    lp, lq = reference["local_p"], reference["local_q"]
    assert source["factor"] in (lp, lq)
    assert source["roots"] == [record[0] for record in window["babies"]]
    inverse, n = pow(window["target"], -1, source["N"]), source["N"]
    assert source["steps"] == [inverse*record[0] % n for record in window["giants"]]
    assert source["centres"] == [point for k in range(1, source["width"]+1)
                                 for point in (pow(window["target"], k, n), pow(inverse, k, n))]
    row = source["successful_row"]
    assert row is not None and row["point"] != row["root"]
    assert (row["point"]-row["root"]) % source["factor"] == 0
    assert row["point"] == row["centre"]*row["step"] % n
    h, b, offset = window["active_base"], 2*source["width"], reference["true_offset"]
    assert row["root"] == pow(h, row["baby_label"], n)
    assert row["step"] == pow(pow(h, -1, n), b*row["block_label"], n)
    exponent = (-1 if row["negative"] else 1)*row["multiplier"]*offset
    assert row["centre"] == pow(h, exponent, n)
    assert source["metrics"]["full_expanded_points"] == 4*source["width"]**2
    assert len(source["rows"]) == 2*row["multiplier"]-int(not row["negative"])
    assert source["metrics"]["gcd_calls"] <= 8*actual["width"]**2
    actual["multiplier_reference"] = dict(local_p=lp, local_q=lq,
        left_order=reference["left_order"], right_order=reference["right_order"],
        literal_offset=offset, successful_signed_exponent=exponent,
        retained_short_exponent=row["baby_label"]+b*row["block_label"],
        acquisition="private factors/periods after whole-public-route timing")


def validate_components():
    """Check cache reuse, deflation and lazy recovery against the old backend."""
    rnd = random.Random(REPLAY_ID)
    cases, row_cases = 0, 0
    controls = [(35, [1], [[1, 6]]), (35, [1, 11, 15], [[1]]),
                (35, [1, 1, 6], [[1, 1]]), (77, [1]*32, [[1]*32]),
                (49, [1, 8, 1], [[1]])]
    for _ in range(256):
        n = rnd.choice((4, 6, 9, 15, 21, 25, 35, 49, 77, 143, 323))
        roots = [rnd.randrange(-n, 2*n) for _ in range(rnd.randrange(13))]
        rows = [[rnd.randrange(-n, 2*n) for _ in range(rnd.randrange(13))]
                for _ in range(4)]
        controls.append((n, roots, rows))
    for n, roots, rows in controls:
        detector = CachedDetector(n, roots)
        for points in rows:
            actual = detector.row(points)
            expected = BATCH["recovery"](n, roots, points, include_signals=True)
            for key in ("factor", "signals", "ordered_points"):
                assert actual[key] == expected[key], key
            assert actual["gcd_calls"] == expected["metrics"]["gcd_calls"]
            assert (actual["factor"] is not None) == BATCH["oracle"](n, roots, points)
            row_cases += 1
        assert detector.metrics["root_polynomials"] == 1
        assert detector.metrics["derivative_polynomials"] <= 1
        cases += 1
    signed_cases = 0
    for r in range(1, 65):
        for cap in range(1, 17):
            for d in range(32):
                limit = r//cap+1
                witness = next((k, min(k*d % r, (-k*d) % r))
                               for k in range(1, limit+1)
                               if min(k*d % r, (-k*d) % r) < cap)
                k, short = witness
                assert 0 < k <= limit and k*cap <= r+cap and short < cap
                signed_cases += 1
    return dict(cached_polynomial_cases=cases, evaluated_regression_rows=row_cases,
                short_signed_multiple_cases=signed_cases,
                shared_root_repeated_root_full_modulus_and_prime_square_cases=True)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeTotientMultipliers.lean",
                  "scripts/CheckSemiprimeTotientMultipliers.lean",
                  "scripts/probe_semiprime_totient_multipliers.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import primerange

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources, components = source_inventory(), validate_components()
    prior = json.loads((ROOT/PARENT_AUDIT).read_text())
    counts, squares = Counter(), 0
    primes = list(primerange(2, 200))
    for i, p in enumerate(primes):
        for q in primes[i:]:
            actual = public_packet(p*q)
            check_packet(actual, p, q)
            counts[actual["status"]] += 1
            squares += int(p == q)
    populations, source_rows, inherited_successes = {}, [], 0
    for name in ("inputs", "controls", "positive_controls", "negative_controls", "wrapped_controls"):
        population = []
        for previous in prior[name]:
            p, q = previous["reference_p"], previous["reference_q"]
            actual = public_packet(p*q)
            check_packet(actual, p, q)
            assert actual["parent"]["factor"] == previous["factor"]
            assert actual["parent"]["status"] == previous["status"]
            if previous["factor"] is not None:
                assert actual["factor"] == previous["factor"] and actual["source"] is None
                inherited_successes += 1
            old_window, window = previous["parent"]["source"], actual["parent"]["parent"]["source"]
            if window is not None:
                for key in ("active_base", "centre", "target", "inverse_step", "babies", "giants",
                            "collision", "candidate", "factor", "construction"):
                    assert json.dumps(window[key]) == json.dumps(old_window[key]), key
            if actual["source"] is not None:
                source_rows.append(dict(original_N=p*q, leaf_N=actual["source"]["N"],
                                        factor=actual["factor"], successful_row=actual["source"]["successful_row"],
                                        **actual["source"]["metrics"]))
            actual.update(reference_p=p, reference_q=q)
            if "regime" in previous:
                actual["regime"] = previous["regime"]
            population.append(actual)
        populations[name] = population
    negative = populations["negative_controls"][0]
    assert negative["parent"]["factor"] is None and negative["factor"] is not None
    assert len(source_rows) == 1
    assert source_inventory() == sources, "source changed during replay"
    result = dict(replay_id=REPLAY_ID, source_sha256=sources,
        scope="Universal public signed-multiplier coverage and streamed proper-factor recovery",
        one_sixth_guarantee="OPEN", universal_lean_specification=True,
        is_complete_semiprime_factorizer=True, is_bit_complexity_certificate=False,
        is_formal_machine_refinement=False,
        validation=dict(semiprime_cases=sum(counts.values()), prime_squares=squares,
            status_counts=dict(counts), inherited_control_successes_preserved=inherited_successes,
            previous_negative_controls_recovered=1, multiplier_sources=len(source_rows), **components),
        source_rows=source_rows,
        summary=dict(sorted(Counter(x["status"] for x in populations["inputs"]).items())),
        timing_protocol="The outer timer wraps the entire preceding bit-power/walk public routine, including its public-value diagnostics, then cached-step normalization, both signed centre recurrences, distinct baby roots, one root polynomial, each scaled target row and remainder tree, shared-root derivative evaluation, GCDs and lazy witness recovery, row signal hashing, all scalar-width diagnostics and original-input transport. Only N enters this routine. Private factor/primality/order/offset acquisitions and the exhaustive independent checks occur afterward. The inherited inner timer is retained separately.",
        limitations="Lean proves universal coverage and correctness of the noncomputable ring/list public specification, three linear retained caches, degree at most 2B, exactly 4B² full evaluation points and at most 8B² streamed GCDs. The executable reuses the existing native packed polynomial/remainder backend and newly counted native cache/target products and inverse. Their complete bit price, deterministic ordering refinement and machine correctness remain open. The prototype streams actual quadratic work; no sixth-root time guarantee or software speed claim follows from this selected case or finite regression.",
        **populations)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(dict(validation=result["validation"], source_pins=len(sources), source_rows=source_rows,
                          recovered_previous_negative=negative["N"], one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()

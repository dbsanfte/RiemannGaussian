#!/usr/bin/env python3
"""N-only extraction of both row channels by one guarded trace polynomial.

Original packet buckets remain upstream. Raw plus/minus-one checks retain
self-inversion. Equal whole traces receive an original-difference GCD
before collapse. One derivative tree then extracts all inter-trace hits.
No pair matrix or extra giant powers are constructed by the public source.
Native counters do not certify deterministic bit complexity or coverage.
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
PARENT_AUDIT = "docs/semiprime-folded-row-coverage-audit.json"
REPLAY_ID = 202610033203
RECIPROCAL = runpy.run_path(str(ROOT/"scripts/probe_semiprime_reciprocal_rows.py"))
DERIVATIVE, FAMILY = RECIPROCAL["DERIVATIVE"], RECIPROCAL["FAMILY"]
IntegerLedger, ScalarLedger, BATCH = RECIPROCAL["IntegerLedger"], RECIPROCAL["ScalarLedger"], RECIPROCAL["BATCH"]


def extract_trace_rows(n, roots, integers, ring, batch, metrics, progress=False):
    """Checked endpoints, guarded inverse-orbit collapse and one polynomial."""
    for j, root in enumerate(roots):
        for offset in (-1, 1):
            endpoint = integers.divmod(integers.add(root, offset), n)[1]
            common = integers.gcd(n, endpoint)
            metrics["raw_sign_endpoint_gcd_queries"] += 1
            if 1 < common < n:
                return common, "raw-sign-endpoint", dict(original_root=root,
                    row_index=j, sign_offset=offset, endpoint=endpoint), {}, [], []
    if not roots:
        return None, "exhausted-trace-rows", None, {}, [], []
    inverses = RECIPROCAL["batch_inverse"](n, roots, integers, ring, metrics)
    trace_buckets = {}
    for j, (root, inverse) in enumerate(zip(roots, inverses)):
        trace = integers.divmod(integers.add(root, inverse), n)[1]
        metrics["public_trace_lookup_queries"] += 1
        integers.charge("public_trace_lookup_operands", trace)
        if trace in trace_buckets:
            representative = trace_buckets[trace][0]
            difference = integers.divmod(integers.add(root, -representative), n)[1]
            common = integers.gcd(n, difference)
            metrics["global_trace_guard_gcd_queries"] += 1
            if 1 < common < n:
                return common, "whole-trace-difference-guard", dict(trace=trace,
                    original_root=root, other_original_root=representative,
                    row_index=j, difference=difference), trace_buckets, [], []
            assert root == representative or inverse == representative, \
                "equal traces without a proper guard must share one global orientation"
            metrics["checked_global_inverse_orbit_duplicates"] += 1
        trace_buckets.setdefault(trace, []).append(root)
        metrics["retained_trace_unit_entries"] += 1
    traces = list(trace_buckets)
    metrics["folded_polynomial_degree"] = len(traces)
    metrics["trace_scalar_axis_input_count"] = len(traces)
    if progress:
        print(json.dumps(dict(progress="N-only-trace-polynomial-start",
            N=n, original_roots=len(roots), distinct_traces=len(traces))), flush=True)
    values = DERIVATIVE["derivative_outputs"](n, traces, integers, ring, batch, metrics)
    factor, stage, witness = DERIVATIVE["recover_derivatives"](n, traces, values, integers, metrics)
    if witness is not None:
        witness = dict(witness, trace=witness["root"],
            original_root=trace_buckets[witness["root"]][0])
        del witness["root"]
        if "other_root" in witness:
            witness["other_trace"] = witness["other_root"]
            witness["other_original_root"] = trace_buckets[witness["other_root"]][0]
            del witness["other_root"]
    return factor, "trace-"+stage, witness, trace_buckets, traces, values


def trace_rows_source(n, alpha=2, progress=False):
    """Only N and a public base enter. All setup is inside the timer."""
    if n < 4:
        raise ValueError("composite n>=4 required")
    start = time.perf_counter()
    integers, ring, batch = IntegerLedger(), ScalarLedger(n), BATCH["MonicBatch"](n)
    metrics, buckets, trace_buckets, m, values = Counter(), {}, {}, None, []

    def finish(factor, stage, witness=None):
        if witness is not None and "original_root" in witness:
            witness = dict(witness, original_packet_bucket=buckets[witness["original_root"]])
            if "other_original_root" in witness:
                witness["other_original_packet_bucket"] = buckets[witness["other_original_root"]]
            if witness.get("trace") in trace_buckets:
                witness["trace_original_unit_bucket"] = trace_buckets[witness["trace"]]
        return dict(N=n, factor=factor, stage=stage, modulus=m,
            distinct_public_roots=len(buckets), distinct_trace_roots=len(trace_buckets),
            evaluated_trace_derivatives=len(values), witness=witness,
            milliseconds=1000*(time.perf_counter()-start),
            metrics=dict(metrics, **integers.stats(), **ring.stats(), **batch.stats()),
            constructed_pair_matrix=False, constructed_extra_giant_powers=False,
            retains_original_packet_buckets=True,
            is_complete_semiprime_factorizer=False, is_complete_bit_certificate=False)

    root = integers.sqrt(n)
    if integers.mul(root, root) == n and 1 < root < n:
        return finish(root, "public-square")
    common = integers.gcd(alpha, n)
    if 1 < common < n:
        return finish(common, "public-base-gcd")
    if common != 1:
        return finish(None, "inconclusive-base")
    m = FAMILY["first_public_prime"](n, integers, metrics)
    common = integers.gcd(m, n)
    if 1 < common < n:
        return finish(common, "public-modulus-gcd")
    if common != 1:
        return finish(None, "inconclusive-modulus")
    inverse = integers.divmod(integers.inverse(alpha, n), n)[1]
    for packet in FAMILY["public_packets"](n, m, integers, metrics):
        exponent = packet["exponent"]
        value = ring.power(alpha if exponent >= 0 else inverse, abs(exponent))
        metrics["public_root_lookup_queries"] += 1
        integers.charge("public_root_lookup_operands", value)
        if value in buckets:
            metrics["whole_modulus_duplicate_packets"] += 1
        buckets.setdefault(value, []).append(packet)
        metrics["retained_packet_bucket_entries"] += 1
        if progress and metrics["retained_packet_bucket_entries"] % 250000 == 0:
            print(json.dumps(dict(progress="N-only-original-row-powers", N=n,
                packets=metrics["retained_packet_bucket_entries"], roots=len(buckets))), flush=True)
    factor, stage, witness, trace_buckets, _, values = extract_trace_rows(
        n, list(buckets), integers, ring, batch, metrics, progress)
    return finish(factor, stage, witness)


def validate_native(rnd):
    """Independent finite signed-pair union and direct derivative oracles."""
    cases = [(35, [2, 32]), (35, [2, 18]), (35, [4]), (35, [6]),
        (49, [1, 8, 8]), (35, [1, 34]), (77, [])]
    for _ in range(256):
        n = rnd.randrange(4, 1200)
        units = [v for v in range(n) if math.gcd(n, v) == 1]
        cases.append((n, [rnd.choice(units) for _ in range(rnd.randrange(16))]))
    for _ in range(128):
        n = rnd.randrange(50, 1200)
        safe = [v for v in range(n) if math.gcd(n, v) == 1 and
            math.gcd(n, v-1) == math.gcd(n, v+1) == 1]
        if safe:
            cases.append((n, [rnd.choice(safe) for _ in range(rnd.randrange(3, 16))]))
    stages, saturated, guarded, phase_pairs = Counter(), 0, 0, 0
    for n, original in cases:
        roots = list(dict.fromkeys(v % n for v in original))
        integers, ring, batch, metrics = IntegerLedger(), ScalarLedger(n), BATCH["MonicBatch"](n), Counter()
        factor, stage, _, buckets, traces, values = extract_trace_rows(
            n, roots, integers, ring, batch, metrics)
        stages[stage] += 1
        proper = lambda z: 1 < math.gcd(n, z) < n
        signed = {v for x in roots for v in (x, pow(x, -1, n))}
        expected = any(proper(x-1) or proper(x+1) for x in roots) or any(
            proper(x-y) for x in signed for y in signed if x != y)
        assert (factor is not None) == expected, (n, roots, stage)
        if factor is not None:
            assert 1 < factor < n and n % factor == 0
        if values:
            direct = [math.prod((x-y) % n for y in traces if x != y) % n for x in traces]
            assert values == direct
        for x in roots:
            for y in roots:
                tx, ty = (x+pow(x, -1, n)) % n, (y+pow(y, -1, n)) % n
                assert math.gcd(n, tx-ty) == math.gcd(n, (x-y)*(x*y-1))
                phase_pairs += 1
        assert metrics["raw_sign_endpoint_gcd_queries"] <= 2*len(roots)
        assert metrics["global_trace_guard_gcd_queries"] <= len(roots)
        assert metrics["derivative_gcd_queries"]+metrics["selected_row_gcd_queries"] <= 2*len(buckets)
        saturated += metrics["selected_row_scans"] > 0
        guarded += stage == "whole-trace-difference-guard"
    assert guarded > 0 and saturated > 0
    return dict(cases=len(cases), exact_phase_pair_checks=phase_pairs,
        stages=dict(stages), saturated_trace_recoveries=saturated,
        whole_trace_guard_recoveries=guarded)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeTraceRows.lean",
        "scripts/CheckSemiprimeTraceRows.lean", "scripts/probe_semiprime_trace_rows.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import nextprime
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--stress", action="store_true", help="Also replay the 4.9-million-packet reference miss")
    args = parser.parse_args()
    sources, rnd = source_inventory(), random.Random(REPLAY_ID)
    validation = validate_native(rnd)
    print(json.dumps(dict(progress="native-trace-oracles-passed", **validation)), flush=True)
    small = []
    for _ in range(32):
        p = int(nextprime(rnd.randrange(100, 3000)))
        q = int(nextprime(rnd.randrange(11*p//10, 19*p//10)))
        small.append(trace_rows_source(p*q))
    control = trace_rows_source(2518766418595894637609, progress=True)
    assert control["factor"] in (39167077933, 64308254573)
    stress = None
    if args.stress:
        miss = json.loads((ROOT/PARENT_AUDIT).read_text())["cases"][-1]
        assert miss["combined_and_sign_prefix_exhausted"]
        stress = trace_rows_source(miss["N"], progress=True)
        assert stress["factor"] is None
    assert source_inventory() == sources, "source changed during replay"
    report = dict(replay_id=REPLAY_ID, source_sha256=sources,
        scope="One guarded trace polynomial extracts ordinary and reciprocal row correlations",
        exact_trace_unit_phase_lean=True, mixed_trace_guard_lean=True,
        self_product_endpoint_guard_lean=True, public_folded_control_recovers_lean=True,
        validation=validation, small_N_only_sources=small, control=control,
        optional_paid_stress_source=stress, stress_requested=args.stress,
        one_sixth_guarantee="OPEN", is_complete_semiprime_factorizer=False,
        is_bit_complexity_certificate=False, is_formal_machine_refinement=False,
        limitations="Lean proves exact two-channel unit/GCD transport over arbitrary composite rings, proper recovery from mixed global trace collisions, raw endpoint recovery of proper self-product hits, and the folded polynomial detector on distinct global traces. It also proves the complete public folded detector succeeds on the earlier ordinary-row stress input. Native guards, inverse batching, trace bucket lookup and source/polynomial construction are timed and validated against independent signed-pair and endpoint oracles. The native table implementation and full guarded procedure do not yet have a formal machine/bit-cost refinement. Hash-table operation counts are not deterministic bit bounds. Compression preserves covered information; it does not create universal local collisions, certify the wider private-order reference classification, price the full row count or prove arbitrary-ratio every-run sixth-root factorization.")
    if args.output:
        args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources), validation=validation,
        small_cases=len(small), small_factors=sum(s["factor"] is not None for s in small),
        control_factor=control["factor"], control_roots=control["distinct_public_roots"],
        control_traces=control["distinct_trace_roots"], control_milliseconds=control["milliseconds"],
        stress_replayed=stress is not None, one_sixth_guarantee="OPEN")), flush=True)


if __name__ == "__main__":
    main()

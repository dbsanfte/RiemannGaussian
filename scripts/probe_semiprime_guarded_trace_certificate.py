#!/usr/bin/env python3
"""Pin the complete Lean guarded procedure and inherited public replay.

This is a source/query audit, not a new factorizer run or a bit certificate.
Strict Lean builds, root imports, namespace lint and all-declaration axiom
checks are separate gates. The stress failure, when present, is native-only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-trace-rows-audit.json"
REPLAY_ID = 202610033204


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeGuardedTrace.lean",
        "scripts/CheckSemiprimeGuardedTrace.lean",
        "scripts/probe_semiprime_guarded_trace_certificate.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def counted_queries(sample):
    metrics = sample["metrics"]
    return sum(metrics.get(name, 0) for name in (
        "raw_sign_endpoint_gcd_queries", "global_trace_guard_gcd_queries",
        "derivative_gcd_queries", "selected_row_gcd_queries"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources = source_inventory()
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    samples = parent["small_N_only_sources"]+[parent["control"]]
    stress = parent["optional_paid_stress_source"]
    if stress is not None:
        samples.append(stress)
    queries = []
    for sample in samples:
        rows = sample["metrics"].get("retained_packet_bucket_entries", 0)
        count = counted_queries(sample)
        assert count <= 5*rows, sample["N"]
        if sample["factor"] is not None:
            assert 1 < sample["factor"] < sample["N"] and sample["N"] % sample["factor"] == 0
        queries.append(dict(N=sample["N"], retained_original_packets=rows,
            guarded_stage_gcd_queries=count, five_query_envelope=5*rows))
    assert source_inventory() == sources
    report = dict(replay_id=REPLAY_ID, source_sha256=sources,
        scope="Complete guarded inverse-orbit extraction and a linear GCD-query theorem",
        same_parent_runs_reused=True, new_source_runtime_runs=0,
        stage_query_counts=queries, inherited_native_stress_replayed=stress is not None,
        inherited_native_stress_exhausted=stress is not None and stress["factor"] is None,
        kernel_checked_failure_control=False, is_bit_complexity_certificate=False,
        is_formal_native_machine_refinement=False, one_sixth_guarantee="OPEN",
        lean_components=dict(whole_trace_guard_orientation=True,
            retained_representatives_separated=True, original_trace_carrier_preserved=True,
            proper_original_pair_hit_preserved_in_both_channels=True,
            exact_original_pair_and_endpoint_hit_union=True,
            raw_endpoint_hit_preserved=True, complete_guarded_return_sound=True,
            five_gcd_queries_per_original_unit=True,
            complete_public_guarded_positive_control=True),
        validation=dict(strict_leaf_build=True, strict_root_import=True,
            namespace_linters=14, linter_errors=0,
            explicit_declarations=39, generated_declarations=35,
            all_module_declarations=74, theorem_and_helper_declarations=52,
            permitted_transitive_axioms=["propext", "Classical.choice", "Quot.sound"]),
        limitations="Compiled Lean theorems certify the full association-list guarded specification, including each original unit's global orientation, retained trace separation, endpoint/self-product transport, the exact original pair/endpoint hit union, sound returned divisors and the five-per-row GCD query bound. They do not prove every public family has a hit. The association-list lookup is not a fast deterministic table or a bit-machine implementation; the native source uses dictionaries and a separate polynomial engine. The inherited full source replay is not rerun by this audit. Its counters are checked against the proved scalar envelope, not promoted to bit costs or Lean failure proofs. Inherited stress exhaustion remains native-only. Full arbitrary-ratio, construction-inclusive, every-run N-only sixth-root factorization remains open.")
    if args.output:
        args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources), inherited_sources=len(samples),
        inherited_stress_exhausted=report["inherited_native_stress_exhausted"],
        proved_gcd_query_coefficient=5, one_sixth_guarantee="OPEN")), flush=True)


if __name__ == "__main__":
    main()

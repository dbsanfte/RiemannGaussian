#!/usr/bin/env python3
"""One ordinary companion polynomial retains the complete signed hit union.

The native source builds the full original family and integer companions,
then reuses one ordinary tree for derivative and coefficient-reflected
evaluation. Global negative matches use cached original derivatives.
These ledgers and finite oracles are not a formal bit-machine refinement.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import combinations
import json
import math
from pathlib import Path
import random
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-euclid-row-budget-audit.json"
REPLAY_ID = 202610033216
COVERAGE = runpy.run_path(str(ROOT/"scripts/probe_semiprime_companion_coverage.py"))
COMPANION, FAMILY = COVERAGE["COMPANION"], COVERAGE["FAMILY"]
IntegerLedger, ScalarLedger, BATCH = (COVERAGE[k] for k in
    ("IntegerLedger", "ScalarLedger", "BATCH"))


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeReflectedCompanions.lean",
        "scripts/CheckSemiprimeReflectedCompanions.lean",
        "scripts/probe_semiprime_reflected_companions.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def reflected_outputs(n, roots, integers, ring, batch, metrics):
    """One original root tree, reused for two full evaluation streams."""
    tree = batch.tree(roots)
    polynomial = tree[0]
    derivative = [ring.mul(k, polynomial[k]) for k in range(1, len(polynomial))]
    reflection = []
    for k, coefficient in enumerate(polynomial):
        integers.charge("reflected_coefficient_reads", k, coefficient)
        reflection.append(coefficient if k % 2 == 0 else
            integers.divmod(integers.add(0, -coefficient), n)[1])
    metrics["ordinary_root_polynomials"] += 1
    metrics["ordinary_root_polynomial_degree"] += len(polynomial)-1
    metrics["derivative_coefficient_products"] += len(derivative)
    metrics["coefficient_reflections"] += 1

    def evaluate_on_cached_tree(coefficients):
        out = []

        def visit(node, remainder):
            remainder = batch.mod(remainder, node[0])
            metrics["visited_evaluation_nodes"] += 1
            if node[1] is None:
                out.append(remainder[0] if remainder else 0)
            else:
                visit(node[1], remainder)
                visit(node[2], remainder)

        if roots:
            visit(tree, coefficients)
        metrics["reused_ordinary_root_tree_streams"] += 1
        return out

    ordinary = evaluate_on_cached_tree(derivative)
    reflected = evaluate_on_cached_tree(reflection)
    indices = {}
    for j, root in enumerate(roots):
        metrics["ordinary_derivative_cache_inserts"] += 1
        integers.charge("ordinary_derivative_cache_insert_operands", root, j)
        indices[root] = j
    values, cross = [], []
    for j, root in enumerate(roots):
        negative = integers.divmod(integers.add(0, -root), n)[1]
        integers.charge("negative_derivative_lookup_operands", negative)
        metrics["negative_derivative_lookup_queries"] += 1
        if negative in indices:
            value = ordinary[indices[negative]]
            metrics["global_negative_derivative_cache_hits"] += 1
        else:
            value = reflected[j]
        integers.charge("endpoint_zero_guard_operands", root)
        endpoint = 1 if root == 0 else root
        metrics["endpoint_zero_guards"] += root == 0
        cross.append(value)
        values.append(ring.mul(ring.mul(endpoint, ordinary[j]), value))
    assert len(polynomial)-1 == len(roots)
    return dict(values=values,ordinary_derivatives=ordinary,
        reflected_polynomial_values=reflected,deflated_reflected_values=cross)


def selected_channel_leaves(n, roots, index, integers, metrics):
    """Construct only one saturated row, keeping its three channels."""
    root = roots[index]
    if root:
        yield "endpoint", None, root
    for k, other in enumerate(roots):
        metrics["selected_channel_positions"] += 1
        if other != root:
            value = integers.divmod(integers.add(root, -other), n)[1]
            assert 0 < value < n
            yield "ordinary-difference", k, value
    negative = integers.divmod(integers.add(0, -root), n)[1]
    for k, other in enumerate(roots):
        metrics["selected_channel_positions"] += 1
        if other != negative:
            value = integers.divmod(integers.add(negative, -other), n)[1]
            assert 0 < value < n
            yield "reflected-difference", k, value


def recover_reflected(n, roots, outputs, integers, metrics):
    for j, value in enumerate(outputs["values"]):
        common = integers.gcd(n, value)
        metrics["reflected_column_gcd_queries"] += 1
        witness = dict(row_index=j,root=roots[j],column_value=value,
            ordinary_derivative=outputs["ordinary_derivatives"][j],
            reflected_polynomial_value=outputs["reflected_polynomial_values"][j],
            deflated_reflected_value=outputs["deflated_reflected_values"][j])
        if common == 1:
            continue
        if 1 < common < n:
            return common, "reflected-column", witness
        metrics["selected_reflected_row_scans"] += 1
        for channel, k, leaf in selected_channel_leaves(n, roots, j, integers, metrics):
            common = integers.gcd(n, leaf)
            metrics["selected_channel_gcd_queries"] += 1
            if 1 < common < n:
                return common, "selected-reflected-row", dict(witness,channel=channel,
                    other_row_index=k,other_root=roots[k] if k is not None else None,leaf=leaf)
        raise AssertionError("nonunit deflated channels lack a proper nonzero leaf")
    return None, "exhausted-reflected-columns", None


def reflected_companion_source(n):
    """Only N enters; every setup, retained row and recovery is timed."""
    if n < 4:
        raise ValueError("composite n>=4 required")
    start = time.perf_counter()
    integers, ring, batch = IntegerLedger(), ScalarLedger(n), BATCH["MonicBatch"](n)
    metrics, originals, buckets, outputs, m = Counter(), [], {}, {}, None

    def finish(factor, stage, witness=None):
        if witness is not None:
            witness = dict(witness,root_packet_bucket=buckets[witness["root"]])
            other = witness.get("other_root")
            if other is not None:
                witness["other_root_packet_bucket"] = buckets[other]
        queries = metrics["reflected_column_gcd_queries"]+metrics["selected_channel_gcd_queries"]
        assert queries <= 3*len(buckets)+1
        assert queries <= 6*len(originals)+1
        return dict(N=n,input_bits=n.bit_length(),modulus=m,factor=factor,stage=stage,witness=witness,
            original_packet_count=len(originals),companion_packet_count=metrics["retained_companion_packets"],
            distinct_ordinary_roots=len(buckets),evaluated_combined_columns=len(outputs.get("values",[])),
            recovery_GCD_queries=queries,milliseconds=1000*(time.perf_counter()-start),
            metrics=dict(metrics,**integers.stats(),**ring.stats(),**batch.stats()),
            all_original_and_integer_companion_packets_retained=True,
            one_ordinary_polynomial_and_one_reused_tree=metrics["ordinary_root_polynomials"] == 1,
            constructed_signed_root_union=False,constructed_pair_matrix=False,
            constructed_modular_giant_powers=False,group_base_input=False,
            private_factors_or_orders_used=False,is_complete_factorizer=False,
            is_bit_complexity_certificate=False,is_formal_native_machine_refinement=False)

    root = integers.sqrt(n)
    if integers.mul(root, root) == n and 1 < root < n:
        return finish(root, "public-square")
    m = FAMILY["first_public_prime"](n, integers, metrics)
    common = integers.gcd(n, m)
    if 1 < common < n:
        return finish(common, "public-modulus-gcd")
    if common != 1:
        return finish(None, "inconclusive-modulus")
    originals = list(FAMILY["public_packets"](n, m, integers, metrics))
    for packet in COMPANION["companion_packets"](originals, m, integers, metrics):
        value = integers.divmod(packet["candidate"], n)[1]
        metrics["ordinary_companion_lookup_queries"] += 1
        integers.charge("ordinary_companion_lookup_operands", value)
        buckets.setdefault(value, []).append(packet)
    assert len(buckets) <= metrics["retained_companion_packets"] <= 2*len(originals)
    roots = list(buckets)
    outputs = reflected_outputs(n, roots, integers, ring, batch, metrics)
    factor, stage, witness = recover_reflected(n, roots, outputs, integers, metrics)
    assert ring.powers == 0 and ring.inverses == 0
    return finish(factor, stage, witness)


def finite_oracles():
    rnd = random.Random(REPLAY_ID)
    cases, global_negatives, zero_axes, saturated, exhausted = 0, 0, 0, 0, 0
    inputs = [(35,[1,34]),(49,[0,7]),(49,[0]),(4,[1,3]),(9,[])]
    for n in (4, 6, 9):
        inputs.extend((n,list(s)) for width in range(n+1) for s in combinations(range(n),width))
    for _ in range(256):
        n = rnd.choice((4,9,15,21,25,35,49,77,143,221,323))
        values = [rnd.randrange(-2*n,2*n) for _ in range(rnd.randrange(16))]
        if values and rnd.randrange(2):
            values.append(-values[0])
        inputs.append((n,values))
    for n, candidates in inputs:
        roots = list(dict.fromkeys(c % n for c in candidates))
        integers, ring, batch, metrics = IntegerLedger(), ScalarLedger(n), BATCH["MonicBatch"](n), Counter()
        outputs = reflected_outputs(n, roots, integers, ring, batch, metrics)
        for j, root in enumerate(roots):
            ordinary = math.prod(root-x for x in roots if x != root) % n
            reflection = math.prod((-root)-x for x in roots) % n
            deflated = math.prod((-root)-x for x in roots if x != (-root) % n) % n
            endpoint = root if root else 1
            assert outputs["ordinary_derivatives"][j] == ordinary
            assert outputs["reflected_polynomial_values"][j] == reflection
            assert outputs["deflated_reflected_values"][j] == deflated
            assert outputs["values"][j] == endpoint*ordinary*deflated % n
            leaf_metrics = Counter()
            leaves = list(selected_channel_leaves(n, roots, j, integers, leaf_metrics))
            assert len(leaves) <= 2*len(roots)+1
            assert math.prod(leaf for _,_,leaf in leaves) % n == outputs["values"][j]
        signed = {0}|set(roots)|{(-c) % n for c in roots}
        hit = any(1 < math.gcd(n,t-x) < n for t in signed for x in signed if t != x)
        factor, stage, _ = recover_reflected(n, roots, outputs, integers, metrics)
        assert (factor is not None) == hit
        if factor is not None:
            assert 1 < factor < n and n % factor == 0
        assert metrics["reflected_column_gcd_queries"]+metrics["selected_channel_gcd_queries"] <= 3*len(roots)+1
        global_negatives += any((-c) % n in roots for c in roots)
        zero_axes += 0 in roots
        saturated += stage == "selected-reflected-row"
        exhausted += factor is None
        cases += 1
    return dict(cases=cases,axes_with_global_negative_matches=global_negatives,
        axes_containing_zero=zero_axes,selected_row_saturation_recoveries=saturated,
        exhausted_axes=exhausted,complete_subset_moduli=[4,6,9],
        exact_columns_match_separate_endpoint_difference_reflection_products=True,
        hit_union_matches_full_signed_family=True,is_Lean_proof=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--checked-declarations", type=int, default=0)
    parser.add_argument("--checked-theorems", type=int, default=0)
    parser.add_argument("--checked-explicit", type=int, default=0)
    args = parser.parse_args()
    sources, oracles = source_inventory(), finite_oracles()
    print(json.dumps(dict(progress="shared-reflected-polynomial-oracles-completed",
        oracle_cases=oracles["cases"],source_pins=len(sources))), flush=True)
    signed = json.loads((ROOT/"docs/semiprime-companion-coverage-audit.json").read_text())
    baseline = signed["signed_N_only_sources"]+signed["signed_larger_sources"]
    profiles, comparisons = [], []
    for old in baseline:
        n = old["N"]
        print(json.dumps(dict(progress="N-only-reflected-source-start",N=n)), flush=True)
        r = reflected_companion_source(n)
        f = r["factor"]
        assert f is not None and 1 < f < n and n % f == 0
        assert r["original_packet_count"] == old["original_packet_count"]
        assert r["companion_packet_count"] == old["companion_packet_count"]
        profiles.append(r)
        comparisons.append(dict(N=n,saved_baseline_signed_roots=old["distinct_signed_roots"],
            new_ordinary_roots=r["distinct_ordinary_roots"],
            saved_baseline_milliseconds=old["milliseconds"],new_milliseconds=r["milliseconds"],
            is_paired_benchmark=False))
        print(json.dumps(dict(progress="N-only-reflected-source-completed",N=n,
            factor=f,stage=r["stage"],ordinary_roots=r["distinct_ordinary_roots"],
            recovery_GCDs=r["recovery_GCD_queries"],milliseconds=r["milliseconds"])), flush=True)
    assert source_inventory() == sources, "source changed during replay"
    checked = args.checked_declarations > 0 and args.checked_theorems > 0
    report = dict(replay_id=REPLAY_ID,source_sha256=sources,parent_audit=PARENT_AUDIT,
        scope="Shared ordinary companion polynomial with complete signed hit-union recovery",
        exact_finite_oracles=oracles,N_only_reflected_companion_sources=profiles,
        saved_signed_baseline_comparisons=comparisons,full_native_90bit_source_replayed=False,
        lean_validation=dict(separately_completed_scoped_gates=checked,
            strict_leaf_and_root=checked,namespace_linters=14 if checked else 0,
            linter_errors=0 if checked else None,all_module_declarations=args.checked_declarations,
            explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        kernel_components=dict(coefficient_sign_reflection_equals_evaluation_at_negative=True,
            shared_polynomial_degree_equals_ordinary_distinct_root_count=True,
            global_negative_matches_reuse_original_cached_derivatives=True,
            endpoint_zero_guard_and_separate_signed_leaf_channels=True,
            exact_polynomial_value_to_lazy_leaf_product_commuting_identity=True,
            complete_exhaustion_equivalent_to_full_signed_program=True,
            original_signed_successes_preserved=True,
            recovery_GCD_queries_at_most_3S_plus_1_and_6R_plus_1=True,
            prime_modulus_recovery_GCD_queries_at_most_48m_log_squared_plus_1=True,
            global_negative_pair_false_hit_excluded_in_kernel=True,
            prime_square_saturated_recovery_checked_in_kernel=True,
            actual_public_7303_72bit_and_90bit_recovery_checked_in_kernel=True),
        is_complete_factorizer=False,is_bit_complexity_certificate=False,
        is_formal_native_machine_refinement=False,one_sixth_guarantee="OPEN",
        limitations="The compiled shared-polynomial program preserves the complete hit union of the full signed companion source for every positive modulus, including squares and saturated recovery. It combines a guarded endpoint, original derivative and globally deflated reflected product. Repeated product factors can change column GCD valuations or the first factor, so only hit-union equivalence is claimed. One original degree-S polynomial/tree supplies two evaluation streams; coefficient reflection and cached ordinary derivatives remove the doubled signed root polynomial. All original construction, integer companions, dictionary work, polynomial operations and recovery are included in the new native source timer. The dictionaries, packed polynomial backend and setup ledgers have no complete Lean bit-machine refinement. Saved older timings are separate runs rather than paired benchmarks. The kernel success transport covers the literal 90-bit public source, but its full native source is not rerun here. Universal useful signed companion coverage, efficient priced prime acquisition, all construction/recovery bit costs and every-run deterministic N-only sixth-root bit factorization remain open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),native_sources=len(profiles),
        proper_native_factors=sum(r["factor"] is not None for r in profiles),
        stages=dict(Counter(r["stage"] for r in profiles)),
        larger_milliseconds=[r["milliseconds"] for r in profiles if r["input_bits"] >= 40],
        one_sixth_guarantee="OPEN")), flush=True)


if __name__ == "__main__":
    main()

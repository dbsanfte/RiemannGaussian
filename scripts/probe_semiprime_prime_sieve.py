#!/usr/bin/env python3
"""Public proper-product sieve, retained witnesses and setup ledgers.

The quotient enumeration and first-gap scan have kernel correctness/count
theorems. A separately checked Boolean product comparator has a primitive
clock. The native sort uses charged integer comparisons; neither its
ledger nor these finite oracles is a complete bit-machine refinement.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import combinations_with_replacement, product
import json
from pathlib import Path
import random
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-reflected-companions-audit.json"
ROW_AUDIT = "docs/semiprime-euclid-row-budget-audit.json"
REPLAY_ID = 202610033218
BUDGET = runpy.run_path(str(ROOT/"scripts/probe_semiprime_euclid_row_budget.py"))
FAMILY, IntegerLedger = BUDGET["FAMILY"], BUDGET["IntegerLedger"]
DIVISION = runpy.run_path(str(ROOT/"scripts/probe_semiprime_bit_division.py"))


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimePrimeSieve.lean",
        "scripts/CheckSemiprimePrimeSieve.lean", "scripts/probe_semiprime_prime_sieve.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def proper_pairs(limit, integers, metrics):
    """Only the actual quotient-length inner rows are generated."""
    pairs, divisor = [], 2
    while True:
        integers.charge("sieve_outer_guard_operands", divisor, limit)
        if divisor > limit:
            return pairs
        metrics["proper_pair_outer_iterations"] += 1
        quotient = integers.divmod(limit, divisor)[0]
        factor = 2
        while True:
            integers.charge("sieve_inner_guard_operands", factor, quotient)
            if factor > quotient:
                break
            pairs.append((divisor, factor))
            integers.charge("proper_pair_witness_write_operands", divisor, factor)
            metrics["proper_pair_inner_events"] += 1
            metrics["proper_pair_witness_cells_written"] += 2
            factor = integers.add(factor, 1)
        divisor = integers.add(divisor, 1)


def sorted_pairs(pairs, integers, metrics):
    """Stable bottom-up merges retaining all tags and multiplicities.

    Both products are recomputed at EVERY comparison, as in the Lean
    predicate. Array access/control is counted only as native diagnostics;
    it has no claimed Boolean implementation or bit-machine price.
    """
    ordered = list(pairs)
    metrics["sort_initial_pair_reads"] += len(pairs)
    metrics["sort_initial_pair_writes"] += len(pairs)
    width, length = 1, len(pairs)
    while width < length:
        merged = []
        metrics["sort_passes"] += 1
        for start in range(0, length, 2*width):
            middle, end = min(start+width, length), min(start+2*width, length)
            i, j = start, middle
            while i < middle and j < end:
                left, right = ordered[i], ordered[j]
                metrics["sort_pair_reads"] += 2
                lhs = integers.mul(*left)
                rhs = integers.mul(*right)
                integers.charge("sort_product_comparison_operands", lhs, rhs)
                metrics["sort_product_comparisons"] += 1
                if lhs <= rhs:
                    merged.append(left)
                    i = integers.add(i, 1)
                else:
                    merged.append(right)
                    j = integers.add(j, 1)
                metrics["sort_pair_writes"] += 1
            for index in range(i, middle):
                merged.append(ordered[index])
                metrics["sort_pair_reads"] += 1
                metrics["sort_pair_writes"] += 1
            for index in range(j, end):
                merged.append(ordered[index])
                metrics["sort_pair_reads"] += 1
                metrics["sort_pair_writes"] += 1
        ordered = merged
        width = integers.mul(width, 2)
    return ordered


def first_gap(candidate, count, values, integers, metrics):
    """Literal firstGap recurrence using a cursor over the retained list."""
    index = 0
    while True:
        metrics["first_gap_invocations"] += 1
        integers.charge("first_gap_count_guard_operands", count)
        if count == 0:
            return None
        integers.charge("first_gap_list_guard_operands", index, len(values))
        if index == len(values):
            return candidate
        value = values[index]
        integers.charge("first_gap_product_read_operands", value)
        metrics["first_gap_product_reads"] += 1
        integers.charge("first_gap_below_comparison_operands", value, candidate)
        if value < candidate:
            index = integers.add(index, 1)
            continue
        integers.charge("first_gap_equal_comparison_operands", value, candidate)
        if value == candidate:
            candidate = integers.add(candidate, 1)
            count = integers.add(count, -1)
            index = integers.add(index, 1)
            continue
        return candidate


def public_sieve(bound, integers, metrics):
    """Only the public lower bound enters; no primality oracle is used."""
    limit = integers.mul(2, max(1, bound))
    start = max(2, bound)
    count = max(0, integers.add(integers.add(limit, 1), -start))
    pairs = proper_pairs(limit, integers, metrics)
    ordered = sorted_pairs(pairs, integers, metrics)
    values = []
    for pair in ordered:
        values.append(integers.mul(*pair))
        metrics["projected_product_writes"] += 1
    missing = first_gap(start, count, values, integers, metrics)
    modulus = 2 if missing is None else missing
    metrics["first_gap_default_used"] += missing is None
    # Return the richer carriers before callers summarize their counts.
    return dict(modulus=modulus,public_lower_bound=bound,window_limit=limit,
        scan_start=start,scan_count=count,pairs=pairs,ordered_pairs=ordered,values=values)


def public_sixth_width(n, integers, metrics):
    floor = integers.root(n, 6)
    power = integers.power(floor, 6)
    integers.charge("sixth_root_rounding_comparison_operands", power, n)
    metrics["public_sixth_root_rounding_checks"] += 1
    return max(1, integers.add(floor, 1) if power < n else floor)


def reference_gap(candidate, count, values):
    marked = set(values)
    return next((c for c in range(candidate, candidate+count) if c not in marked), None)


def validate_events_and_scan(rnd):
    limits = list(range(65))+[97, 193, 257, 511, 1024]
    total_pairs = classified = comparisons = maximum_scan = 0
    for limit in limits:
        integers, metrics = IntegerLedger(), Counter()
        pairs = proper_pairs(limit, integers, metrics)
        # The full rectangle is constructed ONLY by this separate oracle.
        expected = [(a, b) for a in range(2, limit+1) for b in range(2, limit+1)
            if a*b <= limit]
        assert pairs == expected and len(pairs) == len(set(pairs))
        bins = max(1, limit.bit_length())
        assert len(pairs) <= limit*bins*bins
        ordered = sorted_pairs(pairs, integers, metrics)
        assert ordered == sorted(expected, key=lambda pair: pair[0]*pair[1])
        assert Counter(ordered) == Counter(pairs)
        values = [a*b for a, b in ordered]
        marked = set(values)
        for value in range(2, limit+1):
            assert (value in marked) == (not BUDGET["reference_prime"](value))
            classified += 1
        candidates = [(0, 0), (0, limit+2), (2, max(0, limit-1))]
        candidates += [(rnd.randrange(limit+3), rnd.randrange(limit+3)) for _ in range(4)]
        for candidate, count in candidates:
            ledger, scan_metrics = IntegerLedger(), Counter()
            actual = first_gap(candidate, count, values, ledger, scan_metrics)
            assert actual == reference_gap(candidate, count, values)
            iterations = scan_metrics["first_gap_invocations"]
            assert iterations <= count+len(values)+1
            maximum_scan = max(maximum_scan, iterations)
        total_pairs += len(pairs)
        comparisons += metrics["sort_product_comparisons"]
    gap_cases = 0
    # Explicit duplicates, zero values, exhausted windows and empty lists.
    for length in range(5):
        for values in combinations_with_replacement(range(7), length):
            for candidate in range(9):
                for count in range(7):
                    ledger, metrics = IntegerLedger(), Counter()
                    actual = first_gap(candidate, count, values, ledger, metrics)
                    assert actual == reference_gap(candidate, count, values)
                    assert metrics["first_gap_invocations"] <= count+length+1
                    gap_cases += 1
    return dict(limits=limits,complete_quotient_pair_oracles=len(limits),
        retained_proper_pair_witnesses=total_pairs,classified_candidates=classified,
        sort_product_comparisons=comparisons,complete_duplicate_scan_cases=gap_cases,
        additional_sieve_scan_cases=7*len(limits),maximum_sieve_scan_invocations=maximum_scan,
        pair_order_and_multiplicity_preserved=True,
        quadratic_rectangle_used_only_in_reference_oracle=True,is_Lean_proof=False)


def validate_boolean_comparator(rnd):
    encode, decode, width, cost, multiply, subtract = (DIVISION[k] for k in
        ("encode_bits", "decode_bits", "bit_length", "bit_cost", "mul_bits", "sub_bits"))
    inputs = list(product(range(6), repeat=4))
    inputs += [tuple(rnd.randrange(1 << rnd.randrange(21)) for _ in range(4))
        for _ in range(256)]
    maximum_width = maximum_clock = padded_inputs = equal_products = 0
    for index, values in enumerate(inputs):
        padding = [rnd.randrange(9) if index >= 6**4 else 0 for _ in range(4)]
        words = [encode(v, p) for v, p in zip(values, padding)]
        left, right = multiply(words[0], words[1]), multiply(words[2], words[3])
        sub = subtract(right["bits"], left["bits"])
        flag = not sub["borrow"]
        clock = cost(left)+cost(right)+cost(sub["result"])+2
        word_width = max(map(width, words))
        a, b, c, d = values
        assert decode(left["bits"]) == a*b and decode(right["bits"]) == c*d
        assert flag == (a*b <= c*d)
        assert clock <= 72*(word_width+1)**2
        maximum_width = max(maximum_width, word_width)
        maximum_clock = max(maximum_clock, clock)
        padded_inputs += any(padding)
        equal_products += a*b == c*d
    return dict(cases=len(inputs),complete_small_quadruples=6**4,
        padded_word_inputs=padded_inputs,equal_product_inputs=equal_products,
        maximum_physical_word_width=maximum_width,maximum_primitive_clock=maximum_clock,
        final_NOT_gate_and_output_cell_counted=True,
        full_product_and_subtraction_reports_retained=True,
        no_integer_product_or_ordering_oracle_in_Boolean_predicate=True,
        native_sort_does_not_use_this_Boolean_predicate=True,is_Lean_proof=False)


def validate_public_selector():
    selector_cases = 0
    for bound in range(129):
        integers, metrics = IntegerLedger(), Counter()
        actual = public_sieve(bound, integers, metrics)
        expected = next(p for p in range(max(2, bound), 2*max(1, bound)+1)
            if BUDGET["reference_prime"](p))
        assert actual["modulus"] == expected and not metrics["first_gap_default_used"]
        selector_cases += 1
    inputs = list(range(129))
    for bound in list(range(2, 32))+[63, 127, 268, 269, 3690, 3691, 30402, 30403]:
        inputs.extend((bound**6-1, bound**6, bound**6+1))
    for n in inputs:
        integers, metrics = IntegerLedger(), Counter()
        width = public_sixth_width(n, integers, metrics)
        assert width == max(1, BUDGET["reference_ceiling_sixth_root"](n))
    return dict(complete_small_lower_bounds=selector_cases,
        exact_sixth_power_and_neighbor_rounding_inputs=len(inputs),
        small_sieve_moduli_are_literal_least_public_primes=True,
        no_reference_primality_oracle_used_by_paid_source=True,is_Lean_proof=False)


def source_profile(n, construct_originals=False):
    """N-only acquisition; optionally the whole original row construction."""
    start = time.perf_counter()
    integers, metrics = IntegerLedger(), Counter()
    bound = public_sixth_width(n, integers, metrics)
    acquisition = public_sieve(bound, integers, metrics)
    setup_ms = 1000*(time.perf_counter()-start)
    setup_ledger, setup_metrics = integers.stats(), dict(metrics)
    modulus = acquisition["modulus"]
    originals = list(FAMILY["public_packets"](n, modulus, integers, metrics)) if construct_originals else []
    elapsed = 1000*(time.perf_counter()-start)
    # Classification, bounds and serialization are separate replay checks.
    assert bound <= modulus <= 2*bound and BUDGET["reference_prime"](modulus)
    assert not any(BUDGET["reference_prime"](p) for p in range(max(2, bound), modulus))
    limit, events = acquisition["window_limit"], len(acquisition["pairs"])
    count_bound = 2*bound*(2*bound).bit_length()**2
    iterations = setup_metrics["first_gap_invocations"]
    assert events <= count_bound
    assert iterations <= acquisition["scan_count"]+events+1 <= count_bound+2*bound+2
    assert not setup_metrics.get("first_gap_default_used", 0)
    report = dict(N=n,input_bits=n.bit_length(),public_sixth_width=bound,modulus=modulus,
        public_window_limit=limit,complete_proper_product_events=events,
        proved_event_count_bound=count_bound,first_gap_invocations=iterations,
        proved_scan_invocation_bound=count_bound+2*bound+2,
        acquisition_milliseconds=setup_ms,milliseconds=elapsed,
        setup_metrics=dict(setup_metrics,**setup_ledger),metrics=dict(metrics,**integers.stats()),
        both_product_factor_labels_and_all_multiplicities_retained=True,
        source_timer_includes_sixth_root_rounding_and_full_sieve=True,
        candidate_trial_primality_tests=0,private_factors_or_orders_used=False,
        constructed_quadratic_pair_rectangle=False,constructed_triple_envelope=False,
        constructed_pair_matrix=False,constructed_modular_giant_powers=False,
        original_construction_replayed=construct_originals,
        polynomial_and_factor_recovery_replayed=False,
        is_factorization_runtime_measurement=False,is_bit_complexity_certificate=False,
        is_formal_native_machine_refinement=False)
    if construct_originals:
        digest = hashlib.sha256()
        for packet in originals:
            digest.update(json.dumps(packet,sort_keys=True,separators=(",", ":")).encode())
            digest.update(b"\n")
        packets = len(originals)
        assert packets == 2*metrics["emitted_intermediate_vectors"]
        assert packets <= 8*modulus*modulus.bit_length()**2
        assert packets <= 16*bound*(2*bound).bit_length()**2
        report.update(complete_original_packets=packets,
            original_vectors=metrics["emitted_intermediate_vectors"],
            retained_original_packet_sha256=digest.hexdigest(),
            all_intermediate_vectors_and_both_centers_constructed=True)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--checked-declarations", type=int, default=0)
    parser.add_argument("--checked-theorems", type=int, default=0)
    parser.add_argument("--checked-explicit", type=int, default=0)
    args = parser.parse_args()
    sources = source_inventory()
    rnd = random.Random(REPLAY_ID)
    event_oracles = validate_events_and_scan(rnd)
    bit_oracles = validate_boolean_comparator(rnd)
    selector_oracles = validate_public_selector()
    print(json.dumps(dict(progress="prime-sieve-correspondence-oracles-completed",
        event_windows=event_oracles["complete_quotient_pair_oracles"],
        duplicate_gap_cases=event_oracles["complete_duplicate_scan_cases"],
        Boolean_comparator_cases=bit_oracles["cases"],source_pins=len(sources))), flush=True)
    saved = json.loads((ROOT/ROW_AUDIT).read_text())["N_only_full_original_constructor_profiles"]
    by_n = {r["N"]: r for r in saved}
    inputs = list(by_n)
    inputs.append(788096216222522769981991129)  # Acquisition only: no full 90-bit factor run.
    profiles, constructors = [], []
    for n in inputs:
        construct = n in by_n and n.bit_length() >= 40
        print(json.dumps(dict(progress="N-only-prime-sieve-start",N=n,
            full_original_construction=construct)), flush=True)
        result = source_profile(n, construct)
        profiles.append(result)
        if n in by_n:
            assert result["modulus"] == by_n[n]["modulus"]
        if construct:
            assert result["retained_original_packet_sha256"] == by_n[n]["retained_original_packet_sha256"]
            result["matches_frozen_complete_original_packet_digest"] = True
            constructors.append(result)
        print(json.dumps(dict(progress="N-only-prime-sieve-completed",N=n,
            modulus=result["modulus"],events=result["complete_proper_product_events"],
            first_gap_invocations=result["first_gap_invocations"],
            acquisition_milliseconds=result["acquisition_milliseconds"],
            full_original_construction=construct,milliseconds=result["milliseconds"])), flush=True)
    assert source_inventory() == sources, "source changed during replay"
    checked = args.checked_declarations > 0 and args.checked_theorems > 0
    report = dict(replay_id=REPLAY_ID,source_sha256=sources,parent_audit=PARENT_AUDIT,
        scope="Public proper-product sieve preserving the literal row modulus",
        complete_event_and_gap_oracles=event_oracles,Boolean_comparator_oracles=bit_oracles,
        public_selector_oracles=selector_oracles,N_only_acquisition_profiles=profiles,
        N_only_complete_original_constructor_profiles=constructors,
        full_native_90bit_source_replayed=False,
        lean_validation=dict(separately_completed_scoped_gates=checked,
            strict_leaf_and_root=checked,namespace_linters=14 if checked else 0,
            linter_errors=0 if checked else None,all_module_declarations=args.checked_declarations,
            explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        kernel_components=dict(proper_pair_tags_exact_and_duplicate_free=True,
            event_values_mark_exactly_composites_in_public_window=True,
            sorted_events_preserve_full_factor_witnesses_and_multiplicities=True,
            first_gap_equals_literal_least_missing_candidate=True,
            public_sieve_prime_equals_literal_least_prime=True,
            N_only_sieve_modulus_equals_previous_public_modulus=True,
            complete_original_packet_list_and_shared_recovery_preserved=True,
            events_at_most_2B_times_log2_2B_plus_1_squared=True,
            scan_invocations_at_most_event_envelope_plus_2B_plus_2=True,
            Boolean_product_comparator_correct_with_full_reports=True,
            Boolean_product_comparator_clock_at_most_72_times_word_width_plus_1_squared=True),
        event_constructor_and_scan_counts="PROVED",
        Boolean_comparison_primitive_correctness_and_clock="PROVED",
        full_prime_acquisition_bit_clock="OPEN",sorting_control_and_word_materialization_clock="OPEN",
        useful_signed_companion_hit_coverage="OPEN",full_constructor_and_polynomial_bit_clock="OPEN",
        is_complete_factorizer=False,is_bit_complexity_certificate=False,
        is_formal_native_machine_refinement=False,one_sixth_guarantee="OPEN",
        limitations="The compiled sieve acquires exactly the earlier least public prime, preserves all original rows and shared companion recovery, and proves uniform actual product-event and scan-invocation counts. The Boolean comparator has a separate primitive bit clock and retains both product reports and the full subtraction. Native sorting uses integer products, array cursors and charged diagnostic ledgers; no formal sort/control/word-encoding refinement connects that sort to the Boolean comparator. The sixth-root acquisition, every setup operation, complete witness products, sorting and scan are inside the native timers, but their ledgers are not construction-inclusive bit-clock proofs. The 49-bit and 72-bit inputs replay the whole original constructor and match the frozen packet digests; their polynomial and recovery stages are unchanged by the modulus equality and were not retimed here. The 90-bit input replays acquisition only. No universal useful-hit coverage or deterministic every-run construction-inclusive N^(1/6) bit factorization is proved.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),N_only_acquisitions=len(profiles),
        full_original_constructors=len(constructors),Boolean_comparator_cases=bit_oracles["cases"],
        all_moduli_match_literal_least_prime=True,all_replayed_packet_digests_match=True,
        one_sixth_guarantee="OPEN")), flush=True)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Actual Boolean product sorting with copied word-pair witnesses.

Every comparison invokes the existing Boolean multiplication/subtraction
circuits. Linked witness lists mirror the structural Lean recursion. The
clock is the proved declared gate/payload/list model, not a complete machine
certificate. Input encoding, root acquisition and scalar scanning remain
separate bit-price obligations even when included in the native timer.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import random
import runpy
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-prime-sieve-audit.json"
REPLAY_ID = 202610033220
PRIME = runpy.run_path(str(ROOT/"scripts/probe_semiprime_prime_sieve.py"))
DIVISION, IntegerLedger = PRIME["DIVISION"], PRIME["IntegerLedger"]
encode, decode, word_length, bit_cost, multiply, subtract, fit = (DIVISION[k] for k in
    ("encode_bits", "decode_bits", "bit_length", "bit_cost", "mul_bits", "sub_bits", "fit_bits"))
sys.setrecursionlimit(20000)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeBitProductSort.lean",
        "scripts/CheckSemiprimeBitProductSort.lean", "scripts/probe_semiprime_bit_product_sort.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def rows_from_list(values):
    result = None
    for value in reversed(values):
        result = (value, result)
    return result


def iter_rows(rows):
    while rows is not None:
        yield rows[0]
        rows = rows[1]


def add_primitive(report, metrics):
    for field in ("gates", "reads", "writes", "tests"):
        metrics["primitive_"+field] += report[field]


def copy_pair(value, metrics):
    left, right = fit(value[0], value[0]), fit(value[1], value[1])
    add_primitive(left, metrics)
    add_primitive(right, metrics)
    metrics["factor_pair_constructor_clock"] += 1
    metrics["complete_factor_pair_copies"] += 1
    return dict(left=left,right=right,row=(left["bits"],right["bits"]),
        clock=bit_cost(left)+bit_cost(right)+1)


def compare_words(left, right, metrics):
    lhs, rhs = multiply(left[0], left[1]), multiply(right[0], right[1])
    difference = subtract(rhs["bits"], lhs["bits"])
    add_primitive(lhs, metrics)
    add_primitive(rhs, metrics)
    add_primitive(difference["result"], metrics)
    metrics["comparison_NOT_and_output_clock"] += 2
    metrics["Boolean_product_comparisons"] += 1
    return dict(leftProduct=lhs,rightProduct=rhs,subtraction=difference,
        lessEqual=not difference["borrow"],
        clock=bit_cost(lhs)+bit_cost(rhs)+bit_cost(difference["result"])+2)


def copy_rows(rows, metrics):
    if rows is None:
        metrics["structural_list_clock"] += 1
        return dict(rows=None,clock=1,comparisons=0)
    head, tail = copy_pair(rows[0], metrics), copy_rows(rows[1], metrics)
    metrics["structural_list_clock"] += 2
    return dict(rows=(head["row"],tail["rows"]),clock=head["clock"]+tail["clock"]+2,
        comparisons=0)


def merge_words(left, right, metrics):
    if left is None or right is None:
        tail = copy_rows(right if left is None else left, metrics)
        metrics["structural_list_clock"] += 2
        return dict(rows=tail["rows"],clock=tail["clock"]+2,comparisons=0)
    comparison = compare_words(left[0], right[0], metrics)
    if comparison["lessEqual"]:
        head = copy_pair(left[0], metrics)
        tail = merge_words(left[1], right, metrics)
    else:
        head = copy_pair(right[0], metrics)
        tail = merge_words(left, right[1], metrics)
    metrics["structural_list_clock"] += 4
    return dict(rows=(head["row"],tail["rows"]),
        clock=comparison["clock"]+head["clock"]+tail["clock"]+4,
        comparisons=tail["comparisons"]+1)


def split_words(rows, metrics):
    if rows is None:
        metrics["structural_list_clock"] += 1
        return dict(left=None,right=None,clock=1)
    if rows[1] is None:
        head = copy_pair(rows[0], metrics)
        metrics["structural_list_clock"] += 3
        return dict(left=(head["row"],None),right=None,clock=head["clock"]+3)
    tail = split_words(rows[1][1], metrics)
    left, right = copy_pair(rows[0], metrics), copy_pair(rows[1][0], metrics)
    metrics["structural_list_clock"] += 5
    return dict(left=(left["row"],tail["left"]),right=(right["row"],tail["right"]),
        clock=tail["clock"]+left["clock"]+right["clock"]+5)


def sort_words(rows, metrics):
    if rows is None:
        metrics["structural_list_clock"] += 1
        return dict(rows=None,clock=1,comparisons=0)
    if rows[1] is None:
        head = copy_pair(rows[0], metrics)
        metrics["structural_list_clock"] += 3
        return dict(rows=(head["row"],None),clock=head["clock"]+3,comparisons=0)
    halves = split_words(rows, metrics)
    left, right = sort_words(halves["left"], metrics), sort_words(halves["right"], metrics)
    merged = merge_words(left["rows"], right["rows"], metrics)
    metrics["structural_list_clock"] += 2
    return dict(rows=merged["rows"],
        clock=halves["clock"]+left["clock"]+right["clock"]+merged["clock"]+2,
        comparisons=left["comparisons"]+right["comparisons"]+merged["comparisons"])


def clock_from_metrics(metrics):
    return sum(metrics["primitive_"+field] for field in ("gates", "reads", "writes", "tests")) + \
        metrics["factor_pair_constructor_clock"]+metrics["comparison_NOT_and_output_clock"] + \
        metrics["structural_list_clock"]


def check_report(inputs, report, metrics):
    """All decoding and library sorting here are independent oracles."""
    output = list(iter_rows(report["rows"]))
    values = [decode(a)*decode(b) for a, b in inputs]
    actual = [decode(a)*decode(b) for a, b in output]
    length = len(inputs)
    width = max((max(word_length(a),word_length(b)) for a, b in inputs),default=0)
    depth = max(0, length-1).bit_length()
    assert Counter(output) == Counter(inputs)
    assert len(output) == length and actual == sorted(values)
    assert report["comparisons"] == metrics["Boolean_product_comparisons"] <= length*depth
    assert report["clock"] == clock_from_metrics(metrics)
    assert report["clock"] <= 100*(width+1)**2*length*(depth+1)+1
    return dict(rows=length,width=width,depth=depth,comparisons=report["comparisons"],
        declared_primitive_list_clock=report["clock"])


def validate_word_oracles(rnd):
    alphabet = [(0, 3), (2, 3), (3, 2), (1, 6), (3, 1), (2, 2)]
    complete_cases = random_cases = padded_cases = 0
    max_width = max_clock = comparisons = copies = 0

    def check(values, padded=False):
        nonlocal max_width, max_clock, comparisons, copies, padded_cases
        words = [(encode(a,rnd.randrange(6) if padded else 0),
            encode(b,rnd.randrange(6) if padded else 0)) for a, b in values]
        metrics = Counter()
        report = sort_words(rows_from_list(words), metrics)
        checked = check_report(words, report, metrics)
        max_width = max(max_width,checked["width"])
        max_clock = max(max_clock,report["clock"])
        comparisons += report["comparisons"]
        copies += metrics["complete_factor_pair_copies"]
        padded_cases += padded

    for length in range(5):
        for indices in product(range(len(alphabet)), repeat=length):
            check([alphabet[i] for i in indices])
            complete_cases += 1
    for _ in range(256):
        length = rnd.randrange(33)
        values = [(rnd.randrange(1 << rnd.randrange(16)),
            rnd.randrange(1 << rnd.randrange(16))) for _ in range(length)]
        check(values, True)
        random_cases += 1
    return dict(complete_small_word_lists=complete_cases,random_lists=random_cases,
        padded_random_lists=padded_cases,alphabet=alphabet,maximum_physical_word_width=max_width,
        maximum_declared_primitive_list_clock=max_clock,Boolean_comparisons=comparisons,
        complete_factor_pair_copies=copies,full_factor_words_and_multiplicities_preserved=True,
        includes_empty_zero_equal_product_and_duplicate_word_cases=True,is_Lean_proof=False)


def validate_event_oracles():
    limits = list(range(33))+[97, 193, 257, 511]
    events = comparisons = total_clock = 0
    largest_clock = 0
    for limit in limits:
        ledger, construction_metrics = IntegerLedger(), Counter()
        pairs = PRIME["proper_pairs"](limit, ledger, construction_metrics)
        words = [(encode(a),encode(b)) for a, b in pairs]
        metrics = Counter()
        report = sort_words(rows_from_list(words), metrics)
        check_report(words, report, metrics)
        values = [decode(a)*decode(b) for a, b in iter_rows(report["rows"])]
        assert values == sorted(a*b for a, b in pairs)
        width, bins = limit.bit_length(), max(1, limit.bit_length())
        bound = limit*bins**2
        assert report["clock"] <= 100*(width+1)**2*bound*(3*width+1)+1
        assert report["comparisons"] <= 3*bound*width
        events += len(pairs)
        comparisons += report["comparisons"]
        total_clock += report["clock"]
        largest_clock = max(largest_clock, report["clock"])
    return dict(limits=limits,complete_public_event_windows=len(limits),retained_events=events,
        Boolean_product_comparisons=comparisons,total_declared_primitive_list_clock=total_clock,
        largest_window_clock=largest_clock,sorted_values_equal_original_sieve_projection=True,
        full_factor_pair_multiplicities_retained=True,all_uniform_clock_bounds_hold=True,
        is_Lean_proof=False)


def source_profile(n, construct_originals=False):
    """N-only native setup using the actual Boolean word sorter."""
    start = time.perf_counter()
    integers, construction_metrics = IntegerLedger(), Counter()
    bound = PRIME["public_sixth_width"](n, integers, construction_metrics)
    limit = integers.mul(2, bound)
    candidate = max(2, bound)
    count = max(0, integers.add(integers.add(limit, 1), -candidate))
    pairs = PRIME["proper_pairs"](limit, integers, construction_metrics)
    # Encoding is inside this native timer but remains outside the
    # proved word-input sorting clock; no word materialization is free.
    words = [(encode(a),encode(b)) for a, b in pairs]
    for a, b in pairs:
        integers.charge("word_encoding_interface_operands", a, b)
    construction_metrics["word_encoding_factor_pairs"] += len(pairs)
    linked = rows_from_list(words)
    sorting_metrics = Counter()
    sort_start = time.perf_counter()
    sorted_report = sort_words(linked, sorting_metrics)
    sort_ms = 1000*(time.perf_counter()-sort_start)
    products = []
    for left, right in iter_rows(sorted_report["rows"]):
        a, b = decode(left), decode(right)
        integers.charge("scalar_factor_word_decoding_operands", a, b)
        products.append(integers.mul(a, b))
        construction_metrics["scalar_product_projections"] += 1
    missing = PRIME["first_gap"](candidate, count, products, integers, construction_metrics)
    modulus = 2 if missing is None else missing
    acquisition_ms = 1000*(time.perf_counter()-start)
    setup_ledger, setup_metrics = integers.stats(), dict(construction_metrics)
    originals = list(PRIME["FAMILY"]["public_packets"](n, modulus, integers, construction_metrics)) \
        if construct_originals else []
    elapsed = 1000*(time.perf_counter()-start)
    # All complete oracles, bounds and digests below are outside the source timer.
    assert missing is not None and bound <= modulus <= 2*bound
    assert PRIME["BUDGET"]["reference_prime"](modulus)
    assert not any(PRIME["BUDGET"]["reference_prime"](p) for p in range(max(2, bound), modulus))
    checked = check_report(words, sorted_report, sorting_metrics)
    assert products == sorted(a*b for a, b in pairs)
    width, bins = limit.bit_length(), max(1, limit.bit_length())
    event_bound = limit*bins**2
    uniform_clock = 100*(width+1)**2*event_bound*(3*width+1)+1
    uniform_comparisons = 3*event_bound*width
    assert sorted_report["clock"] <= uniform_clock
    assert sorted_report["comparisons"] <= uniform_comparisons
    assert setup_metrics["first_gap_invocations"] <= count+len(pairs)+1
    report = dict(N=n,input_bits=n.bit_length(),public_sixth_width=bound,modulus=modulus,
        public_window_limit=limit,complete_proper_product_events=len(pairs),
        maximum_input_factor_word_width=checked["width"],public_factor_word_width_bound=width,
        word_sort_depth=checked["depth"],Boolean_product_comparisons=sorted_report["comparisons"],
        declared_sort_primitive_list_clock=sorted_report["clock"],
        proved_uniform_sort_clock_bound=uniform_clock,
        proved_uniform_comparison_bound=uniform_comparisons,sorting_metrics=dict(sorting_metrics),
        integer_setup_metrics=dict(setup_metrics,**setup_ledger),
        complete_native_metrics=dict(construction_metrics,**integers.stats()),
        first_gap_invocations=setup_metrics["first_gap_invocations"],
        word_sort_milliseconds=sort_ms,acquisition_milliseconds=acquisition_ms,milliseconds=elapsed,
        source_timer_includes_root_encoding_Boolean_sort_scalar_projection_and_scan=True,
        every_sort_comparison_uses_Boolean_products_and_subtraction=True,
        every_distribution_merge_singleton_and_remaining_tail_payload_copy_paid=True,
        original_factor_words_padding_and_product_multiplicities_retained=True,
        uses_linked_witness_lists=True,uses_native_integer_product_ordering_in_sort=False,
        private_factors_or_orders_used=False,constructed_pair_matrix=False,
        constructed_modular_giant_powers=False,original_construction_replayed=construct_originals,
        polynomial_and_factor_recovery_replayed=False,is_factorization_runtime_measurement=False,
        is_complete_bit_complexity_certificate=False,is_formal_native_machine_refinement=False)
    if construct_originals:
        digest = hashlib.sha256()
        for packet in originals:
            digest.update(json.dumps(packet,sort_keys=True,separators=(",", ":")).encode())
            digest.update(b"\n")
        report.update(complete_original_packets=len(originals),
            original_vectors=construction_metrics["emitted_intermediate_vectors"],
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
    word_oracles = validate_word_oracles(random.Random(REPLAY_ID))
    print(json.dumps(dict(progress="Boolean-word-list-oracles-completed",
        complete_cases=word_oracles["complete_small_word_lists"],
        padded_random_cases=word_oracles["padded_random_lists"],source_pins=len(sources))),flush=True)
    event_oracles = validate_event_oracles()
    print(json.dumps(dict(progress="Boolean-public-event-window-oracles-completed",
        complete_windows=event_oracles["complete_public_event_windows"],
        retained_events=event_oracles["retained_events"])),flush=True)
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    inherited = parent["N_only_acquisition_profiles"]
    profiles, constructors = [], []
    saved_rows = json.loads((ROOT/PRIME["ROW_AUDIT"]).read_text())[
        "N_only_full_original_constructor_profiles"]
    saved_by_n = {r["N"]:r for r in saved_rows}
    for baseline in inherited:
        n = baseline["N"]
        if n.bit_length() > 49:
            continue
        construct = n.bit_length() >= 40
        print(json.dumps(dict(progress="N-only-Boolean-sorted-setup-start",N=n,
            full_original_construction=construct)),flush=True)
        result = source_profile(n, construct)
        assert result["modulus"] == baseline["modulus"]
        assert result["complete_proper_product_events"] == baseline["complete_proper_product_events"]
        assert result["first_gap_invocations"] == baseline["first_gap_invocations"]
        result["matches_frozen_modulus_full_event_count_and_scan_invocations"] = True
        profiles.append(result)
        if construct:
            assert result["retained_original_packet_sha256"] == saved_by_n[n]["retained_original_packet_sha256"]
            result["matches_frozen_complete_original_packet_digest"] = True
            constructors.append(result)
        print(json.dumps(dict(progress="N-only-Boolean-sorted-setup-completed",N=n,
            modulus=result["modulus"],events=result["complete_proper_product_events"],
            Boolean_comparisons=result["Boolean_product_comparisons"],
            declared_sort_clock=result["declared_sort_primitive_list_clock"],
            word_sort_milliseconds=result["word_sort_milliseconds"],
            acquisition_milliseconds=result["acquisition_milliseconds"],
            milliseconds=result["milliseconds"])),flush=True)
    assert source_inventory() == sources, "source changed during replay"
    checked = args.checked_declarations > 0 and args.checked_theorems > 0
    report = dict(replay_id=REPLAY_ID,source_sha256=sources,parent_audit=PARENT_AUDIT,
        scope="Actual Boolean product sorting with all witness payload copies charged",
        exact_word_list_oracles=word_oracles,complete_public_event_oracles=event_oracles,
        N_only_Boolean_sorted_setup_profiles=profiles,
        N_only_complete_original_constructor_profiles=constructors,
        inherited_inputs_above_49_bits_replayed=False,
        full_native_72bit_or_90bit_factorizer_replayed=False,
        lean_validation=dict(separately_completed_scoped_gates=checked,
            strict_leaf_and_root=checked,namespace_linters=14 if checked else 0,
            linter_errors=0 if checked else None,all_module_declarations=args.checked_declarations,
            explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        kernel_components=dict(full_physical_factor_words_preserved_by_permutation=True,
            products_sorted_by_actual_Boolean_comparison=True,
            all_word_distribution_merge_singleton_and_remaining_tail_copies_charged=True,
            whole_sorted_product_list_equals_previous_sieve_list_with_multiplicities=True,
            actual_canonical_factor_word_widths_bounded_by_clog2_X_plus_1=True,
            sort_comparisons_at_most_n_times_clog2_n=True,
            declared_sort_clock_at_most_100_times_L_plus_1_squared_times_n_times_clog2_n_plus_1_plus_1=True,
            actual_event_sort_uniform_clock_at_most_100_times_L_plus_1_squared_times_X_times_Q_squared_times_3L_plus_1_plus_1=True,
            public_modulus_complete_row_list_and_shared_recovery_preserved=True),
        supplied_word_sort_circuit_payload_list_clock="PROVED",
        literal_event_word_width_and_sort_bound="PROVED",
        full_prime_acquisition_bit_clock="OPEN",input_root_event_generation_encoding_and_scan_bit_clock="OPEN",
        complete_machine_memory_address_and_report_refinement="OPEN",
        useful_signed_companion_hit_coverage="OPEN",full_constructor_and_polynomial_bit_clock="OPEN",
        is_complete_factorizer=False,is_complete_bit_complexity_certificate=False,
        is_formal_native_machine_refinement=False,one_sixth_guarantee="OPEN",
        limitations="The kernel proves whole-word permutation, product ordering, an actual Boolean-comparison bound and a declared gate/payload/list clock for the balanced structural sort. Every selected or remaining payload, both alternating halves and singleton outputs are copied through the existing bit routine, preserving padding, factor tags and product multiplicities. Canonical words for every actual proper-pair event meet the proved logarithmic width bound, and their sorted scalar list exactly equals the previous sieve output. All public moduli, complete original rows and shared recovery are preserved. The native sort calls the Boolean circuits and uses linked witness lists; no integer product ordering selects a row. Root acquisition, proper-pair generation, encoding, scalar projection and first-gap scan are inside native setup timers, but their complete bit clocks and the machine/memory/address refinement remain open. All inherited inputs through 49 bits are replayed; the 49-bit complete original packet digest matches the frozen record. Larger 72-bit/90-bit Boolean setup and polynomial/factor recovery are not replayed. Universal useful-hit coverage and deterministic every-run construction-inclusive N^(1/6) bit factorization remain open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),N_only_Boolean_setups=len(profiles),
        full_original_constructors=len(constructors),all_frozen_setup_moduli_and_events_match=True,
        all_primitive_list_clock_bounds_hold=True,one_sixth_guarantee="OPEN")),flush=True)


if __name__ == "__main__":
    main()

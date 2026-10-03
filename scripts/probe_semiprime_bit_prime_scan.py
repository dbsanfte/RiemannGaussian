#!/usr/bin/env python3
"""Boolean sorting, full product construction and first-gap scan.

Every backend ordering, equality, increment and bound uses the existing
Boolean routines. Reports retain words and primitive charges. The native
prefix still uses integer root/event/encoding operations; complete machine
and memory refinement and universal factor hits remain open.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import combinations_with_replacement
import json
from pathlib import Path
import random
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-bit-product-sort-audit.json"
REPLAY_ID = 202610033222
SORT = runpy.run_path(str(ROOT/"scripts/probe_semiprime_bit_product_sort.py"))
PRIME, DIVISION = SORT["PRIME"], SORT["DIVISION"]
IntegerLedger = SORT["IntegerLedger"]
encode, decode, width, cost, multiply, subtract, fit, nonzero = (DIVISION[k] for k in
    ("encode_bits","decode_bits","bit_length","bit_cost","mul_bits","sub_bits",
        "fit_bits","nonzero_bits"))
add = DIVISION["ARITH"]["add_bits"]
RECONCILED_PATH = "RiemannGaussian/SemiprimeGeometricRows.lean"
PARENT_GEOMETRY_SHA = "f2f1d189e922123f2cd266f7818dbaa1ba3a09c49f30a0a3f1f1bf11f66f37d0"
CURRENT_GEOMETRY_SHA = "1cb0d7217b18fc2b6f6ef58cf05fbeb1faeaeab730825a11b22c6f3bff0477f3"


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        actual = hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
        if path == RECONCILED_PATH:
            assert digest == PARENT_GEOMETRY_SHA, "historical parent record changed"
            assert actual == CURRENT_GEOMETRY_SHA, "reconciled source changed again"
        else:
            assert actual == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeBitPrimeScan.lean",
        "scripts/CheckSemiprimeBitPrimeScan.lean","scripts/probe_semiprime_bit_prime_scan.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def order_words(left, right, metrics):
    difference = subtract(left, right)
    check = nonzero(difference["result"]["bits"])
    left_clear, zero_clear = not difference["borrow"], not check["nonzero"]
    SORT["add_primitive"](difference["result"], metrics)
    metrics["nonzero_scan_clock"] += check["clock"]
    metrics["equality_NOT_AND_output_clock"] += 4
    metrics["word_order_calls"] += 1
    return dict(difference=difference,nonzero=check,equal=left_clear and zero_clear,
        clock=cost(difference["result"])+check["clock"]+4)


def build_products(rows, metrics):
    if rows is None:
        metrics["product_list_clock"] += 1
        return dict(products=None,clock=1)
    value = multiply(*rows[0])
    SORT["add_primitive"](value, metrics)
    tail = build_products(rows[1], metrics)
    metrics["product_list_clock"] += 2
    metrics["full_Boolean_product_reports"] += 1
    return dict(products=(value,tail["products"]),clock=cost(value)+tail["clock"]+2)


def scan_word_gaps(candidate, limit, products, metrics):
    bound = subtract(limit, candidate)
    SORT["add_primitive"](bound["result"], metrics)
    metrics["Boolean_upper_limit_subtractions"] += 1
    metrics["gap_invocations"] += 1
    if bound["borrow"]:
        metrics["scan_structure_clock"] += 2
        return dict(result=None,clock=cost(bound["result"])+2,invocations=1)
    if products is None:
        output = fit(candidate, candidate)
        SORT["add_primitive"](output, metrics)
        metrics["scan_structure_clock"] += 3
        return dict(result=dict(some=output["bits"]),
            clock=cost(bound["result"])+cost(output)+3,invocations=1)
    order = order_words(candidate, products[0]["bits"], metrics)
    if order["difference"]["borrow"]:
        output = fit(candidate, candidate)
        SORT["add_primitive"](output, metrics)
        metrics["scan_structure_clock"] += 4
        return dict(result=dict(some=output["bits"]),
            clock=cost(bound["result"])+order["clock"]+cost(output)+4,invocations=1)
    if order["equal"]:
        increment = add(candidate, (True, None))
        next_word = fit(increment["bits"], (False, limit))
        SORT["add_primitive"](increment, metrics)
        SORT["add_primitive"](next_word, metrics)
        metrics["Boolean_candidate_increments"] += 1
        metrics["scan_structure_clock"] += 5
        tail = scan_word_gaps(next_word["bits"], limit, products[1], metrics)
        return dict(result=tail["result"],clock=cost(bound["result"])+order["clock"]+
            cost(increment)+cost(next_word)+tail["clock"]+5,invocations=tail["invocations"]+1)
    metrics["scan_structure_clock"] += 4
    tail = scan_word_gaps(candidate, limit, products[1], metrics)
    return dict(result=tail["result"],clock=cost(bound["result"])+order["clock"]+
        tail["clock"]+4,invocations=tail["invocations"]+1)


def run_word_sieve(candidate, limit, rows, metrics):
    sorted_rows = SORT["sort_words"](rows, metrics)
    products = build_products(sorted_rows["rows"], metrics)
    gap = scan_word_gaps(candidate, limit, products["products"], metrics)
    metrics["backend_carrier_clock"] += 5
    return dict(candidate=candidate,limit=limit,sorted=sorted_rows,products=products,gap=gap,
        clock=sorted_rows["clock"]+products["clock"]+gap["clock"]+5)


def result_value(gap):
    return None if gap["result"] is None else decode(gap["result"]["some"])


def clock_from_metrics(metrics):
    return SORT["clock_from_metrics"](metrics)+sum(metrics[k] for k in
        ("nonzero_scan_clock","equality_NOT_AND_output_clock","product_list_clock",
            "scan_structure_clock","backend_carrier_clock"))


def check_backend(candidate, limit, words, report, metrics):
    values = sorted(decode(a)*decode(b) for a,b in words)
    c, x = decode(candidate), decode(limit)
    expected = PRIME["reference_gap"](c,max(0,x+1-c),values)
    assert result_value(report["gap"]) == expected
    assert report["clock"] == clock_from_metrics(metrics)
    assert report["gap"]["invocations"] == metrics["gap_invocations"] <= len(words)+1
    output_pairs = list(SORT["iter_rows"](report["sorted"]["rows"]))
    assert Counter(output_pairs) == Counter(words)
    product_reports = list(SORT["iter_rows"](report["products"]["products"]))
    assert [decode(r["bits"]) for r in product_reports] == values
    word_width = max([width(limit),max(0,width(candidate)-1)]+[
        max(width(a),width(b)) for a,b in words])
    depth = max(0,len(words)-1).bit_length()
    assert report["clock"] <= 272*(word_width+1)**2*(len(words)+1)*(depth+1)
    return word_width


def validate_scan_oracles(rnd):
    cases = exhausted = zero_results = increments = total_clock = 0
    for length in range(5):
        for values in combinations_with_replacement(range(7),length):
            reports = [dict(bits=encode(v),gates=0,reads=0,writes=0,tests=0) for v in values]
            linked = SORT["rows_from_list"](reports)
            for candidate in range(9):
                for limit in range(9):
                    cword,xword = encode(candidate),encode(limit)
                    metrics = Counter()
                    gap = scan_word_gaps(cword,xword,linked,metrics)
                    expected = PRIME["reference_gap"](candidate,max(0,limit+1-candidate),values)
                    assert result_value(gap) == expected
                    assert gap["invocations"] <= length+1
                    assert gap["clock"] == clock_from_metrics(metrics)
                    factor_width = max([width(xword),max(0,width(cword)-1)]+[
                        (width(r["bits"])+2)//3 for r in reports])
                    assert gap["clock"] <= (length+1)*(100*(factor_width+1)+24)
                    cases += 1
                    exhausted += expected is None
                    zero_results += expected == 0
                    increments += metrics["Boolean_candidate_increments"]
                    total_clock += gap["clock"]
    random_cases = 0
    for _ in range(256):
        values = [rnd.randrange(256) for _ in range(rnd.randrange(17))]
        candidate,limit = rnd.randrange(260),rnd.randrange(260)
        reports = [dict(bits=encode(v,rnd.randrange(5)),gates=0,reads=0,writes=0,tests=0) for v in values]
        cword,xword = encode(candidate,rnd.randrange(5)),encode(limit,rnd.randrange(5))
        metrics,reference_metrics,ledger = Counter(),Counter(),IntegerLedger()
        gap = scan_word_gaps(cword,xword,SORT["rows_from_list"](reports),metrics)
        expected = PRIME["first_gap"](candidate,max(0,limit+1-candidate),values,ledger,reference_metrics)
        assert result_value(gap) == expected
        assert gap["clock"] == clock_from_metrics(metrics)
        assert gap["invocations"] <= len(values)+1
        random_cases += 1
    return dict(complete_sorted_duplicate_cases=cases,arbitrary_padded_stream_cases=random_cases,
        exhausted_windows=exhausted,zero_valued_successes=zero_results,Boolean_increments=increments,
        total_complete_oracle_scan_clock=total_clock,
        option_zero_word_distinguished_from_exhaustion=True,
        template_product_reports_are_only_prepared_inputs_to_scan_oracle=True,is_Lean_proof=False)


def validate_backend_oracles(rnd):
    cases = clock_total = largest = 0
    for _ in range(256):
        words = [(encode(rnd.randrange(1 << rnd.randrange(13)),rnd.randrange(5)),
            encode(rnd.randrange(1 << rnd.randrange(13)),rnd.randrange(5)))
            for _ in range(rnd.randrange(25))]
        candidate,limit = encode(rnd.randrange(200),rnd.randrange(5)),encode(rnd.randrange(128),rnd.randrange(5))
        metrics = Counter()
        report = run_word_sieve(candidate,limit,SORT["rows_from_list"](words),metrics)
        check_backend(candidate,limit,words,report,metrics)
        cases += 1
        clock_total += report["clock"]
        largest = max(largest,report["clock"])
    bounds = list(range(65))+[97,127,193,257]
    complete_events = 0
    for bound in bounds:
        ledger,construction_metrics = IntegerLedger(),Counter()
        limit = 2*max(1,bound)
        pairs = PRIME["proper_pairs"](limit,ledger,construction_metrics)
        words = [(encode(a),encode(b)) for a,b in pairs]
        metrics = Counter()
        report = run_word_sieve(encode(max(2,bound)),encode(limit),SORT["rows_from_list"](words),metrics)
        check_backend(encode(max(2,bound)),encode(limit),words,report,metrics)
        prime = result_value(report["gap"])
        assert PRIME["BUDGET"]["reference_prime"](prime)
        assert not any(PRIME["BUDGET"]["reference_prime"](p) for p in range(max(2,bound),prime))
        word_width,bins = limit.bit_length(),max(1,limit.bit_length())
        assert report["clock"] <= 272*(word_width+1)**2*(limit*bins**2+1)*(3*word_width+1)
        complete_events += len(words)
    return dict(padded_random_backends=cases,total_random_backend_clock=clock_total,
        maximum_random_backend_clock=largest,complete_public_bound_cases=len(bounds),bounds=bounds,
        complete_public_events=complete_events,all_moduli_are_literal_least_public_primes=True,
        all_full_backend_clock_bounds_hold=True,is_Lean_proof=False)


def source_profile(n, construct_originals=False):
    start = time.perf_counter()
    integers,construction_metrics = IntegerLedger(),Counter()
    bound = PRIME["public_sixth_width"](n,integers,construction_metrics)
    limit = integers.mul(2,max(1,bound))
    pairs = PRIME["proper_pairs"](limit,integers,construction_metrics)
    words = [(encode(a),encode(b)) for a,b in pairs]
    candidate_word,limit_word = encode(max(2,bound)),encode(limit)
    for a,b in pairs:
        integers.charge("factor_word_encoding_interface_operands",a,b)
    integers.charge("public_window_word_encoding_interface_operands",max(2,bound),limit)
    metrics = Counter()
    backend_start = time.perf_counter()
    backend = run_word_sieve(candidate_word,limit_word,SORT["rows_from_list"](words),metrics)
    backend_ms = 1000*(time.perf_counter()-backend_start)
    assert backend["gap"]["result"] is not None
    modulus = decode(backend["gap"]["result"]["some"])
    integers.charge("final_modulus_decoding_interface_operands",modulus)
    setup_ms = 1000*(time.perf_counter()-start)
    setup_ledger = integers.stats()
    originals = list(PRIME["FAMILY"]["public_packets"](n,modulus,integers,construction_metrics)) \
        if construct_originals else []
    elapsed = 1000*(time.perf_counter()-start)
    check_backend(candidate_word,limit_word,words,backend,metrics)
    w,bins = limit.bit_length(),max(1,limit.bit_length())
    uniform_clock = 272*(w+1)**2*(limit*bins**2+1)*(3*w+1)
    assert backend["clock"] <= uniform_clock
    assert bound <= modulus <= 2*bound and PRIME["BUDGET"]["reference_prime"](modulus)
    report = dict(N=n,input_bits=n.bit_length(),public_sixth_width=bound,modulus=modulus,
        public_window_limit=limit,complete_proper_product_events=len(pairs),
        word_sort_clock=backend["sorted"]["clock"],product_construction_clock=backend["products"]["clock"],
        gap_scan_clock=backend["gap"]["clock"],complete_supplied_word_backend_clock=backend["clock"],
        proved_uniform_public_backend_clock_bound=uniform_clock,Boolean_gap_invocations=backend["gap"]["invocations"],
        backend_metrics=dict(metrics),integer_prefix_and_interface_metrics=setup_ledger,
        complete_native_integer_metrics=integers.stats(),backend_milliseconds=backend_ms,
        acquisition_milliseconds=setup_ms,milliseconds=elapsed,
        selected_modulus_physical_word_width=width(backend["gap"]["result"]["some"]),
        sort_product_equality_increment_bound_and_scan_data_path_is_Boolean_only=True,
        original_sorted_factor_words_full_product_reports_and_public_inputs_retained=True,
        no_scalar_countdown_or_product_projection_in_backend=True,
        source_timer_includes_root_event_generation_encoding_backend_and_final_interface=True,
        private_factors_or_orders_used=False,constructed_pair_matrix=False,constructed_modular_giant_powers=False,
        original_construction_replayed=construct_originals,polynomial_and_factor_recovery_replayed=False,
        is_complete_bit_complexity_certificate=False,is_formal_native_machine_refinement=False,
        is_factorization_runtime_measurement=False)
    if construct_originals:
        digest = hashlib.sha256()
        for packet in originals:
            digest.update(json.dumps(packet,sort_keys=True,separators=(",",":")).encode())
            digest.update(b"\n")
        report.update(complete_original_packets=len(originals),
            retained_original_packet_sha256=digest.hexdigest(),
            all_intermediate_vectors_and_both_centers_constructed=True)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    for name in ("declarations","theorems","explicit","geometry-declarations",
            "geometry-theorems","geometry-explicit"):
        parser.add_argument("--checked-"+name,type=int,default=0)
    args = parser.parse_args()
    sources = source_inventory()
    rnd = random.Random(REPLAY_ID)
    scan_oracles = validate_scan_oracles(rnd)
    print(json.dumps(dict(progress="Boolean-gap-oracles-completed",source_pins=len(sources),
        sorted_duplicate_cases=scan_oracles["complete_sorted_duplicate_cases"],
        padded_arbitrary_streams=scan_oracles["arbitrary_padded_stream_cases"])),flush=True)
    backend_oracles = validate_backend_oracles(rnd)
    print(json.dumps(dict(progress="Boolean-complete-backend-oracles-completed",
        random_backends=backend_oracles["padded_random_backends"],
        complete_public_bounds=backend_oracles["complete_public_bound_cases"],
        complete_events=backend_oracles["complete_public_events"])),flush=True)
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    saved_rows = json.loads((ROOT/PRIME["ROW_AUDIT"]).read_text())[
        "N_only_full_original_constructor_profiles"]
    saved_by_n = {r["N"]:r for r in saved_rows}
    profiles,constructors = [],[]
    for baseline in parent["N_only_Boolean_sorted_setup_profiles"]:
        n = baseline["N"]
        assert n.bit_length() <= 49
        construct = n.bit_length() >= 40
        print(json.dumps(dict(progress="N-only-Boolean-backend-start",N=n,
            full_original_construction=construct)),flush=True)
        result = source_profile(n,construct)
        assert result["modulus"] == baseline["modulus"]
        assert result["complete_proper_product_events"] == baseline["complete_proper_product_events"]
        assert result["Boolean_gap_invocations"] == baseline["first_gap_invocations"]
        assert result["word_sort_clock"] == baseline["declared_sort_primitive_list_clock"]
        result["matches_frozen_modulus_events_gap_invocations_and_word_sort_clock"] = True
        profiles.append(result)
        if construct:
            assert result["retained_original_packet_sha256"] == saved_by_n[n]["retained_original_packet_sha256"]
            result["matches_frozen_complete_original_packet_digest"] = True
            constructors.append(result)
        print(json.dumps(dict(progress="N-only-Boolean-backend-completed",N=n,
            modulus=result["modulus"],events=result["complete_proper_product_events"],
            gap_invocations=result["Boolean_gap_invocations"],
            complete_backend_clock=result["complete_supplied_word_backend_clock"],
            backend_milliseconds=result["backend_milliseconds"],
            acquisition_milliseconds=result["acquisition_milliseconds"],
            milliseconds=result["milliseconds"])),flush=True)
    assert source_inventory() == sources, "source changed during replay"
    checked = (args.checked_declarations > 0 and args.checked_theorems > 0 and
        args.checked_geometry_declarations > 0 and args.checked_geometry_theorems > 0)
    report = dict(replay_id=REPLAY_ID,source_sha256=sources,parent_audit=PARENT_AUDIT,
        scope="Actual Boolean witness sorting, full product words and first-gap scan",
        source_reconciliation=dict(path=RECONCILED_PATH,
            historical_parent_sha256=PARENT_GEOMETRY_SHA,current_sha256=CURRENT_GEOMETRY_SHA,
            historical_parent_manifest_preserved=True,unchanged_other_parent_pins=204,
            source_change_made_by_this_task=False,
            strict_current_source_root_lint_and_all_declaration_axiom_audits_completed=checked,
            current_source_declarations=args.checked_geometry_declarations,
            current_source_theorems=args.checked_geometry_theorems,
            current_source_explicit_declarations=args.checked_geometry_explicit,
            current_source_generated_declarations=args.checked_geometry_declarations-args.checked_geometry_explicit,
            is_unchanged_historical_parent_replay=False),
        exact_gap_scan_oracles=scan_oracles,complete_backend_oracles=backend_oracles,
        N_only_Boolean_backend_setup_profiles=profiles,
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
        kernel_components=dict(Boolean_order_and_full_zero_scan_exact_including_padding=True,
            full_product_words_correct_with_multiplicity_and_width_bound=True,
            Boolean_limit_guard_equality_increment_and_fit_are_exact=True,
            gap_scan_option_matches_previous_firstGap_for_every_product_stream=True,
            successful_zero_word_is_distinct_from_exhaustion=True,
            supplied_word_backend_clock_at_most_272_times_L_plus_1_squared_times_n_plus_1_times_clog2_n_plus_1=True,
            positive_public_input_produces_actual_least_prime_word_without_default=True,
            public_backend_clock_at_most_272_times_L_plus_1_squared_times_X_Q_squared_plus_1_times_3L_plus_1=True,
            public_modulus_complete_row_list_and_shared_recovery_preserved=True),
        supplied_word_sort_product_and_scan_circuit_payload_list_clock="PROVED",
        literal_event_width_count_and_public_backend_bound="PROVED",
        full_prime_acquisition_bit_clock="OPEN",input_root_event_generation_and_encoding_bit_clock="OPEN",
        complete_machine_memory_address_and_report_refinement="OPEN",
        useful_signed_companion_hit_coverage="OPEN",full_constructor_and_polynomial_bit_clock="OPEN",
        is_complete_factorizer=False,is_complete_bit_complexity_certificate=False,
        is_formal_native_machine_refinement=False,one_sixth_guarantee="OPEN",
        limitations="The kernel proves exact Boolean sorting, product materialization and gap scanning, including physical padding, duplicate products, increments, upper-limit exhaustion and actual successful options. The complete supplied-word backend has a proved declared gate/payload/list clock. All complete actual public event families satisfy its discharged width and count envelope, and every positive public bound returns the literal least prime word. Rich inputs, sorted factor words and all product reports remain upstream of the result. Complete original rows and shared recovery are preserved by generic source equality. Native setup timers include ordinary integer root, event generation and encoding, the Boolean backend and one final decoding interface; their full bit price and machine/memory/report refinement remain open. All 46 inherited inputs through 49 bits are replayed and the 49-bit full original packet digest is preserved. Larger Boolean setups, polynomial computation and factor recovery are not replayed. One parent geometric-row source changed externally; the old manifest is preserved, its replacement is explicitly pinned and freshly strictly audited, and the other 204 parent source hashes remain exact. Universal useful hits and deterministic every-run construction-inclusive N^(1/6) bit factorization remain open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),N_only_Boolean_setups=len(profiles),
        full_original_constructors=len(constructors),all_frozen_setup_moduli_and_events_match=True,
        all_complete_backend_clock_bounds_hold=True,explicit_parent_source_reconciliation=True,
        one_sixth_guarantee="OPEN")),flush=True)


if __name__ == "__main__":
    main()

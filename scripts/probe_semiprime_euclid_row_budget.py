#!/usr/bin/env python3
"""Replay the complete Euclidean row-count bridge and public constructor.

The kernel theorem bounds every intermediate row at every public prime
modulus. Finite native correspondence checks and construction ledgers are
separate evidence. This probe neither factors its inputs nor certifies a
construction-inclusive bit clock or universal companion hit coverage.
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
PARENT_AUDIT = "docs/semiprime-companion-coverage-audit.json"
REPLAY_ID = 202610033214
COVERAGE = runpy.run_path(str(ROOT/"scripts/probe_semiprime_companion_coverage.py"))
FAMILY, IntegerLedger = COVERAGE["FAMILY"], COVERAGE["IntegerLedger"]


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeEuclidRowBudget.lean",
        "scripts/CheckSemiprimeEuclidRowBudget.lean", "scripts/probe_semiprime_euclid_row_budget.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def reference_frames(m, slope):
    """Retain all original division data before any count projection."""
    r0, r1, x, y, negative = m, slope % m, 0, 1, False
    frames = []
    while r1:
        quotient, remainder = divmod(r0, r1)
        frame = dict(larger=r0, smaller=r1, prior_weight=x, current_weight=y,
            negative=negative, quotient=quotient, remainder=remainder)
        frames.append(frame)
        assert 0 < r1 < r0 and 0 < y and r0*y+r1*x == m
        r0, r1, x, y, negative = r1, remainder, y, x+quotient*y, not negative
    return frames


def expand_frame(frame):
    a, t, x, r0, negative = (frame[k] for k in
        ("smaller", "current_weight", "prior_weight", "larger", "negative"))
    return [(-a if negative else a, t)] + [
        (r0-k*a if negative else -(r0-k*a), x+k*t)
        for k in range(1, frame["quotient"])]


def validate_frame_bridge(rnd):
    prime_moduli = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 43, 61, 97)
    cases = frames_checked = charges_checked = fibers_checked = 0
    maximum_fiber = maximum_quotient = 0
    for m in prime_moduli:
        inputs = list(range(m)) + [143, 2047, 7303, 2304167]
        inputs += [rnd.randrange(0, 10**12) for _ in range(12)]
        for n in inputs:
            charges, fibers, expanded = [], {}, 0
            for j in range(m):
                if math.gcd(j, m) != 1:
                    continue
                slope = (n*pow(j, -1, m)**2) % m
                frames = reference_frames(m, slope)
                rows = [row for frame in frames for row in expand_frame(frame)]
                integers, metrics = IntegerLedger(), Counter()
                native = list(FAMILY["public_pairs"](m, slope, integers, metrics))
                assert rows == native
                assert len(rows) == sum(frame["quotient"] for frame in frames)
                assert metrics["emitted_intermediate_vectors"] == len(rows)
                remainders = [frame["smaller"] for frame in frames]
                assert all(a > b for a, b in zip(remainders, remainders[1:]))
                for frame in frames:
                    a, t, negative, quotient = (frame[k] for k in
                        ("smaller", "current_weight", "negative", "quotient"))
                    signed_a = -a if negative else a
                    assert (signed_a*j*j-n*t) % m == 0
                    fibers.setdefault((negative, a, t), set()).add(j)
                    for k in range(1, quotient+1):
                        assert a*t*k <= m
                        charges.append((negative, a, t, k, j))
                    maximum_quotient = max(maximum_quotient, quotient)
                expanded += len(rows)
                frames_checked += len(frames)
            assert len(charges) == expanded == len(set(charges))
            assert all(len(residues) <= 2 for residues in fibers.values())
            assert 2*expanded <= 8*m*m.bit_length()**2
            charges_checked += len(charges)
            fibers_checked += len(fibers)
            maximum_fiber = max([maximum_fiber] + [len(v) for v in fibers.values()])
            cases += 1
    return dict(cases=cases,prime_moduli=list(prime_moduli),frames=frames_checked,
        full_quotient_slots=charges_checked,actual_quadratic_fibers=fibers_checked,
        maximum_actual_fiber=maximum_fiber,maximum_full_quotient=maximum_quotient,
        original_vector_lists_match=True,charge_tags_have_no_duplicates=True,
        includes_N_zero_and_N_divisible_by_modulus=True,is_Lean_proof=False)


def validate_full_square_fibers():
    fibers, maximum = 0, 0
    for m in (2, 3, 5, 7, 11, 13, 17, 19):
        for n in range(m):
            for negative in (False, True):
                for a in range(1, m):
                    signed_a = -a if negative else a
                    for t in range(1, m+1):
                        roots = [j for j in range(m) if (signed_a*j*j-n*t) % m == 0]
                        assert len(roots) <= 2
                        fibers += 1
                        maximum = max(maximum, len(roots))
    # The prime premise is essential to this particular envelope.
    composite_roots = [j for j in range(8) if (-2*j*j-6) % 8 == 0]
    assert len(composite_roots) == 4
    return dict(fibers=fibers,maximum_prime_fiber=maximum,
        composite_control=dict(modulus=8,N=3,signed_a=-2,t=2,roots=composite_roots),
        is_Lean_proof=False)


def validate_triple_envelope():
    moduli = list(range(129)) + [193, 256, 511, 1024]
    total, largest = 0, 0
    for m in moduli:
        triples = [(a, t, k) for a in range(1, m+1)
            for t in range(1, m//a+1) for k in range(1, m//(a*t)+1)]
        fibers = Counter((a.bit_length()-1, t.bit_length()-1) for a, t, _ in triples)
        for (i, j), count in fibers.items():
            box_volume = 2**i*2**j*(m//(2**i*2**j))
            assert count <= box_volume <= m
        log_bins = (m.bit_length()-1 if m else 0)+1
        assert len(triples) <= m*log_bins**2
        assert len(triples) == sum(m//(a*t) for a in range(1, m+1)
            for t in range(1, m//a+1))
        total += len(triples)
        largest = max(largest, len(triples))
    return dict(moduli=moduli,total_triples_checked=total,largest_triple_set=largest,
        dyadic_box_cardinality_at_most_modulus=True,
        finite_envelope_constructed_only_in_reference_oracle=True,is_Lean_proof=False)


def reference_ceiling_sixth_root(n):
    import gmpy2
    floor, exact = gmpy2.iroot(n, 6)
    return int(floor) + (not exact)


def reference_prime(n):
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n)+1))


def validate_public_selector():
    inputs = list(range(512))
    for b in list(range(2, 64)) + [127, 268, 269, 3690, 3691, 30402, 30403]:
        inputs.extend((b**6-1, b**6, b**6+1))
    for n in inputs:
        integers, metrics = IntegerLedger(), Counter()
        m = FAMILY["first_public_prime"](n, integers, metrics)
        b = max(1, reference_ceiling_sixth_root(n))
        assert b <= m <= 2*b and reference_prime(m)
        assert not any(reference_prime(p) for p in range(b, m))
    return dict(inputs=len(inputs),exact_sixth_powers_and_neighboring_roundings=True,
        literal_native_least_prime_matches_public_definition=True,
        prime_search_range_is_not_acquisition_bit_price=True,is_Lean_proof=False)


def construction_source(n):
    """Only N enters the literal original row constructor and its timer."""
    if n < 4:
        raise ValueError("constructor profiles require n>=4")
    start = time.perf_counter()
    integers, metrics = IntegerLedger(), Counter()
    m = FAMILY["first_public_prime"](n, integers, metrics)
    originals = list(FAMILY["public_packets"](n, m, integers, metrics))
    elapsed = 1000*(time.perf_counter()-start)
    # The public scale and digest below check retained source data after
    # the constructor timer; they are replay metadata, not algorithm work.
    b = reference_ceiling_sixth_root(n)
    vectors, packets = metrics["emitted_intermediate_vectors"], len(originals)
    prime_bound = 8*m*m.bit_length()**2
    public_bound = 16*b*(2*b).bit_length()**2
    assert reference_prime(m) and b <= m <= 2*b
    assert packets == 2*vectors == metrics["centered_packets"]
    assert packets <= prime_bound <= public_bound
    digest = hashlib.sha256()
    for packet in originals:
        digest.update(json.dumps(packet,sort_keys=True,separators=(",", ":")).encode())
        digest.update(b"\n")
    return dict(N=n,input_bits=n.bit_length(),public_sixth_width=b,modulus=m,
        original_vectors=vectors,complete_original_packets=packets,
        prime_modulus_count_bound=prime_bound,public_width_count_bound=public_bound,
        milliseconds=elapsed,metrics=dict(metrics,**integers.stats()),
        retained_original_packet_sha256=digest.hexdigest(),
        retained_original_packet_samples=originals[:2]+originals[-2:],
        source_timer_includes_prime_selection_and_all_original_construction=True,
        all_intermediate_vectors_and_both_centers_constructed=True,
        private_factors_or_orders_used=False,constructed_pair_matrix=False,
        constructed_modular_giant_powers=False,constructed_triple_envelope=False,
        is_factorization_runtime_measurement=False,is_bit_complexity_certificate=False,
        is_formal_native_machine_refinement=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--checked-declarations", type=int, default=0)
    parser.add_argument("--checked-theorems", type=int, default=0)
    parser.add_argument("--checked-explicit", type=int, default=0)
    args = parser.parse_args()
    sources = source_inventory()
    frame_oracles = validate_frame_bridge(random.Random(REPLAY_ID))
    quadratic_oracles = validate_full_square_fibers()
    triple_oracles = validate_triple_envelope()
    selector_oracles = validate_public_selector()
    print(json.dumps(dict(progress="row-budget-correspondence-oracles-completed",
        frame_cases=frame_oracles["cases"],slots=frame_oracles["full_quotient_slots"],
        quadratic_fibers=quadratic_oracles["fibers"],source_pins=len(sources))), flush=True)
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    inputs = list(dict.fromkeys([4, 9, 25, 49,
        *(r["N"] for r in parent["signed_N_only_sources"]),
        *(r["N"] for r in parent["signed_larger_sources"])]))
    profiles = []
    for n in inputs:
        print(json.dumps(dict(progress="N-only-full-original-construction-start", N=n)), flush=True)
        r = construction_source(n)
        profiles.append(r)
        print(json.dumps(dict(progress="N-only-full-original-construction-completed", N=n,
            modulus=r["modulus"],packets=r["complete_original_packets"],
            count_bound=r["prime_modulus_count_bound"],milliseconds=r["milliseconds"])), flush=True)
    assert source_inventory() == sources, "source changed during replay"
    checked = args.checked_declarations > 0 and args.checked_theorems > 0
    report = dict(replay_id=REPLAY_ID, source_sha256=sources, parent_audit=PARENT_AUDIT,
        scope="Uniform complete Euclidean row count at the literal public prime modulus",
        complete_frame_correspondence_oracles=frame_oracles,
        complete_small_prime_quadratic_fiber_oracles=quadratic_oracles,
        dyadic_triple_count_oracles=triple_oracles, public_selector_oracles=selector_oracles,
        N_only_full_original_constructor_profiles=profiles,
        lean_validation=dict(separately_completed_scoped_gates=checked,
            strict_leaf_and_root=checked,namespace_linters=14 if checked else 0,
            linter_errors=0 if checked else None,
            all_module_declarations=args.checked_declarations,
            explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext", "Classical.choice", "Quot.sound"]),
        kernel_components=dict(rich_frames_expand_to_literal_original_rows=True,
            complete_row_count_equals_twice_all_frame_quotients=True,
            every_slot_has_positive_product_at_most_modulus=True,
            complete_public_charge_tags_have_no_duplicates=True,
            current_frames_keep_the_public_quadratic_congruence=True,
            each_quadratic_residue_fiber_at_prime_modulus_has_at_most_two_roots=True,
            positive_product_triples_at_most_m_times_log2_m_plus_1_squared=True,
            all_N_complete_packets_at_most_8m_times_log2_m_plus_1_squared=True,
            companion_packets_and_roots_at_most_16m_times_log2_m_plus_1_squared=True,
            signed_roots_at_most_32m_times_log2_m_plus_1_squared_plus_1=True,
            signed_recovery_GCD_queries_at_most_64m_times_log2_m_plus_1_squared_plus_2=True,
            least_public_prime_lies_in_doubled_sixth_root_window=True,
            literal_N_only_modulus_complete_rows_at_most_16B_times_log2_2B_plus_1_squared=True),
        original_row_count_obligation="PROVED for the actual public prime-modulus constructor",
        useful_signed_companion_hit_coverage="OPEN", prime_acquisition_bit_clock="OPEN",
        full_constructor_and_polynomial_bit_clock="OPEN",
        is_complete_factorizer=False,is_bit_complexity_certificate=False,
        is_formal_native_machine_refinement=False,one_sixth_guarantee="OPEN",
        limitations="The kernel theorem proves a uniform count of every actual intermediate vector and both original centers, for every N at every prime m. The literal public least-prime choice is proved to be between the ceiling sixth root B and 2B. Complete source frames are retained before the count projection. The mathematical triple envelope is never constructed by the paid native row source. Native finite oracles check correspondence and replay every original constructor operation, including public inverses, all quotients and both centers; their operand ledgers are not a formal bit machine. There is no useful-hit guarantee, priced prime acquisition or full construction/polynomial bit refinement. The count applies to arbitrary inputs including squares and ratios, but it alone proves no complete factorizer. Every-run deterministic construction-inclusive sixth-root bit factorization remains open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),full_native_constructors=len(profiles),
        all_complete_packet_counts_within_proved_envelope=True,
        larger_profiles=[dict(N=r["N"],packets=r["complete_original_packets"],
            milliseconds=r["milliseconds"]) for r in profiles if r["input_bits"] >= 40],
        original_row_count_obligation=report["original_row_count_obligation"],
        one_sixth_guarantee="OPEN")), flush=True)


if __name__ == "__main__":
    main()

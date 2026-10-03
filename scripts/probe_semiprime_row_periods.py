#!/usr/bin/env python3
"""Retain exponent differences at cached whole-modulus row coincidences.

The source receives only N and a public integer base. Original packet
construction, powers, cache lookup, relation GCDs, further public probes
and checked wrapped reconstruction are all inside its timer. Private
orders appear only in the separately labeled diagnostic. Native ledgers,
integer arithmetic and list storage are not a deterministic bit certificate.
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
PARENT_AUDIT = "docs/semiprime-augmented-row-coverage-audit.json"
REPLAY_ID = 202610033208
TRACE = runpy.run_path(str(ROOT/"scripts/probe_semiprime_trace_rows.py"))
WEIGHTED = runpy.run_path(str(ROOT/"scripts/probe_semiprime_weighted_rows.py"))
FAMILY = TRACE["FAMILY"]
IntegerLedger, ScalarLedger = TRACE["IntegerLedger"], TRACE["ScalarLedger"]


def cached_period(tags, integers, metrics):
    """A representative star in each equality class; retain full buckets."""
    buckets, relations, period = {}, [], 0
    for tag in tags:
        value, exponent = tag["value"], tag["packet"]["exponent"]
        metrics["public_period_cache_lookups"] += 1
        integers.charge("public_period_cache_lookup_operands",value)
        if value in buckets:
            old = buckets[value][0]["packet"]["exponent"]
            difference = integers.add(exponent,-old)
            integers.charge("signed_difference_absolute_values",difference)
            period = integers.gcd(period,abs(difference))
            metrics["integer_period_gcd_queries"] += 1
            relations.append(dict(value=value,representative_exponent=old,
                original_exponent=exponent,difference=difference,next_gcd=period))
        buckets.setdefault(value,[]).append(tag)
    return period,buckets,relations


def merge_tag_values(tags, integers, metrics):
    """Explicit deterministic comparisons and tag writes; no hash lookup."""
    runs = [[tag] for tag in tags]
    metrics["period_sort_initial_tag_writes"] += len(tags)
    while len(runs)>1:
        merged = []
        for start in range(0,len(runs),2):
            if start+1 == len(runs):
                merged.append(runs[start])
                continue
            left,right,out,i,j = runs[start],runs[start+1],[],0,0
            while i<len(left) and j<len(right):
                integers.charge("period_sort_comparison_operands",left[i]["value"],right[j]["value"])
                metrics["period_sort_value_comparisons"] += 1
                if left[i]["value"]<=right[j]["value"]:
                    out.append(left[i]); i += 1
                else:
                    out.append(right[j]); j += 1
                metrics["period_sort_tag_writes"] += 1
            for tag in left[i:]:
                out.append(tag)
                metrics["period_sort_tag_writes"] += 1
            for tag in right[j:]:
                out.append(tag)
                metrics["period_sort_tag_writes"] += 1
            merged.append(out)
        metrics["period_sort_merge_levels"] += 1
        runs = merged
    ceiling_log = max(0,len(tags)-1).bit_length()
    assert metrics["period_sort_value_comparisons"] <= len(tags)*ceiling_log
    assert metrics["period_sort_tag_writes"] <= len(tags)*ceiling_log
    return runs[0] if runs else []


def sorted_cached_period(tags, integers, metrics):
    """Adjacent equal-value edges retain full original sorted buckets."""
    ordered = merge_tag_values(tags,integers,metrics)
    buckets,relations,period,previous = [],[],0,None
    for tag in ordered:
        value,exponent = tag["value"],tag["packet"]["exponent"]
        equal = False
        if previous is not None:
            metrics["period_adjacent_value_comparisons"] += 1
            integers.charge("period_adjacent_comparison_operands",value,previous["value"])
            equal = value == previous["value"]
        if equal:
            old = previous["packet"]["exponent"]
            difference = integers.add(exponent,-old)
            integers.charge("signed_difference_absolute_values",difference)
            period = integers.gcd(period,abs(difference))
            metrics["integer_period_gcd_queries"] += 1
            relations.append(dict(value=value,previous_exponent=old,
                original_exponent=exponent,difference=difference,next_gcd=period))
            buckets[-1].append(tag)
        else:
            buckets.append([tag])
        previous = tag
    assert metrics["period_adjacent_value_comparisons"] == max(0,len(tags)-1)
    assert metrics["integer_period_gcd_queries"] == len(tags)-len(buckets)
    return period,buckets,relations


def wrapped_candidates(n, d, count, integers):
    """Literal natural subtractions, as in wrappedCandidate in Lean."""
    quotient = integers.divmod(integers.add(n,-1),d)[0]
    product, residue = integers.divmod(quotient,d)
    for label in range(count):
        s = integers.add(residue,integers.mul(label,d))
        v = max(0,integers.add(product,-label))
        discriminant = max(0,integers.add(integers.mul(s,s),-integers.mul(4,v)))
        delta = integers.sqrt(discriminant)
        a = integers.divmod(max(0,integers.add(s,-delta)),2)[0]
        yield label,integers.add(integers.mul(d,a),1)


def row_period_source(n, alpha=2):
    """N-only source; no order, private factor, witness or label advice."""
    if n < 4:
        raise ValueError("composite n>=4 required")
    start = time.perf_counter()
    integers, ring, metrics = IntegerLedger(), ScalarLedger(n), Counter()
    tags, buckets, relations, probes, wrap_checks = [], {}, [], [], []
    period, m, period_check = 0, None, None

    def finish(factor,stage,witness=None):
        return dict(N=n,public_base=alpha,modulus=m,factor=factor,stage=stage,witness=witness,
            packet_count=len(tags),distinct_cached_values=len(buckets),period_gcd=period,
            whole_modulus_period_check=period_check,relations_recorded=len(relations),
            first_relations=relations[:16],last_relations=relations[-8:],
            public_period_probes=probes,wrapped_candidate_checks=wrap_checks,
            milliseconds=1000*(time.perf_counter()-start),
            metrics=dict(metrics,**integers.stats(),**ring.stats()),
            retains_original_packet_buckets=True,retains_signed_exponent_relations=True,
            uses_explicit_merge_sort_and_adjacent_scan=True,uses_hash_cache_lookup=False,
            constructed_pair_matrix=False,private_orders_used_by_source=False,
            wrapped_reconstruction_checks_budget=0 if m is None else 4*m,
            is_complete_factorizer=False,is_bit_complexity_certificate=False,
            is_formal_native_machine_refinement=False)

    square = integers.sqrt(n)
    if integers.mul(square,square) == n and 1 < square < n:
        return finish(square,"public-square")
    common = integers.gcd(n,alpha)
    if 1 < common < n:
        return finish(common,"public-base-gcd")
    if common != 1:
        return finish(None,"inconclusive-base")
    m = FAMILY["first_public_prime"](n,integers,metrics)
    common = integers.gcd(n,m)
    if 1 < common < n:
        return finish(common,"public-modulus-gcd")
    if common != 1:
        return finish(None,"inconclusive-modulus")
    inverse = integers.divmod(integers.inverse(alpha,n),n)[1]
    for packet in FAMILY["public_packets"](n,m,integers,metrics):
        exponent = packet["exponent"]
        value = ring.power(alpha if exponent >= 0 else inverse,abs(exponent))
        metrics["original_giant_powers"] += 1
        tags.append(dict(packet=packet,value=value))
    period,buckets,relations = sorted_cached_period(tags,integers,metrics)
    assert metrics["integer_period_gcd_queries"] <= len(tags)
    if period == 0:
        return finish(None,"zero-retained-period")
    period_check = ring.power(alpha,period)
    metrics["public_period_certificate_power_checks"] += 1
    assert period_check == 1
    for base in range(3,m+1):
        value = ring.power(base,period)
        metrics["further_public_period_powers"] += 1
        for offset in (-1,1):
            endpoint = integers.divmod(integers.add(value,offset),n)[1]
            common = integers.gcd(n,endpoint)
            metrics["period_probe_factor_gcd_queries"] += 1
            probe = dict(base=base,sign_offset=offset,endpoint=endpoint,gcd=common)
            probes.append(probe)
            if 1 < common < n:
                return finish(common,"further-public-period-probe",probe)
    assert metrics["period_probe_factor_gcd_queries"] <= 2*max(0,m-2)
    for label,candidate in wrapped_candidates(n,period,4*m,integers):
        common = integers.gcd(n,candidate)
        metrics["wrapped_reconstruction_factor_gcd_queries"] += 1
        check = dict(wrap_label=label,candidate=candidate,gcd=common)
        wrap_checks.append(check)
        if 1 < common < n:
            return finish(common,"cached-period-wrapped-reconstruction",check)
    assert metrics["wrapped_reconstruction_factor_gcd_queries"] <= 4*m
    return finish(None,"unresolved-period-reconstruction")


def validate_relation_stars(rnd):
    """Independent all-pair GCD oracle on finite tagged equality classes."""
    cases, zero, nonzero = 0, 0, 0
    for _ in range(512):
        n = rnd.randrange(5,600)
        units = [x for x in range(1,n) if math.gcd(n,x) == 1]
        base = rnd.choice(units)
        exponents = [rnd.randrange(-10000,10001) for _ in range(rnd.randrange(25))]
        tags = [dict(packet=dict(exponent=e),value=pow(base,e,n)) for e in exponents]
        integers,metrics = IntegerLedger(),Counter()
        period,buckets,relations = sorted_cached_period(tags,integers,metrics)
        star,star_buckets,_ = cached_period(tags,IntegerLedger(),Counter())
        assert period == star
        assert len(buckets) == len(star_buckets)
        all_pair = 0
        for x in tags:
            for y in tags:
                if x["value"] == y["value"]:
                    all_pair = math.gcd(all_pair,abs(x["packet"]["exponent"]-y["packet"]["exponent"]))
        assert period == all_pair
        assert pow(base,period,n) == 1
        assert len(tags)-len(buckets) == len(relations) == metrics["integer_period_gcd_queries"]
        assert sum(map(len,buckets)) == len(tags)
        cases += 1
        zero += period == 0
        nonzero += period != 0
    return dict(finite_star_equals_all_pair_gcd_cases=cases,
        zero_certificates=zero,nonzero_certificates=nonzero,is_Lean_proof=False)


def private_order_diagnostic(p,q):
    """Private orders classify controls after the N-only runs."""
    from sympy.ntheory import n_order
    n = p*q
    trace = TRACE["trace_rows_source"](n)
    weighted = WEIGHTED["weighted_rows_source"](n)
    return dict(N=n,reference_p=p,reference_q=q,
        reference_component_base_two_orders=[int(n_order(2,p)),int(n_order(2,q))],
        original_guarded_source=trace,weighted_guarded_source=weighted,
        is_N_only_order_classification=False,private_order_claims_kernel_checked=False)


def source_inventory(extra_audits=()):
    """Preserve the frozen parent and any explicitly merged audit branches."""
    paths = set()
    for audit_path in (PARENT_AUDIT,*extra_audits):
        parent = json.loads((ROOT/audit_path).read_text())
        for path,digest in parent["source_sha256"].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
        paths.update(parent["source_sha256"])
        paths.add(audit_path)
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeRowPeriods.lean",
        "scripts/CheckSemiprimeRowPeriods.lean","scripts/probe_semiprime_row_periods.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import nextprime
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--checked-declarations",type=int,default=0)
    parser.add_argument("--checked-theorems",type=int,default=0)
    parser.add_argument("--checked-explicit",type=int,default=0)
    parser.add_argument("--include-audit",action="append",default=[],
        help="Merge each additional frozen audit without mutating its sources")
    args = parser.parse_args()
    sources,rnd = source_inventory(args.include_audit),random.Random(REPLAY_ID)
    algebra = validate_relation_stars(rnd)
    pairs = [(23,89),(1103,2089),(59,233),(17,41),(11,13),(101,101),
        (3,1000003),(14799739,24991489)]
    for _ in range(24):
        p = int(nextprime(rnd.randrange(50,4000)))
        q = int(nextprime(rnd.randrange(p+1,2*p)))
        pairs.append((p,q))
    native = [row_period_source(p*q) for p,q in pairs]
    for result in native:
        d,n = result["factor"],result["N"]
        if d is not None:
            assert 1 < d < n and n%d == 0
    assert native[0]["period_gcd"] == 11 and native[0]["factor"] == 23
    assert native[1]["period_gcd"] == 29 and native[1]["factor"] == 1103
    assert native[1]["stage"] == "cached-period-wrapped-reconstruction"
    assert native[1]["witness"]["wrap_label"] == 3
    diagnostics = [private_order_diagnostic(p,q) for p,q in pairs[:2]]
    assert all(d["original_guarded_source"]["factor"] is None and
        d["weighted_guarded_source"]["factor"] is None for d in diagnostics)
    assert source_inventory(args.include_audit) == sources,"source changed during replay"
    checked = args.checked_declarations > 0 and args.checked_theorems > 0
    report = dict(replay_id=REPLAY_ID,source_sha256=sources,
        parent_audit=PARENT_AUDIT,explicitly_merged_audits=args.include_audit,
        scope="Retained whole-modulus exponent relations, public base probes and balanced wrapped reconstruction",
        finite_relation_oracles=algebra,N_only_sources=native,private_order_diagnostics=diagnostics,
        lean_validation=dict(separately_completed_scoped_gates=checked,
            strict_leaf_and_root=checked,namespace_linters=14 if checked else 0,
            linter_errors=0 if checked else None,all_module_declarations=args.checked_declarations,
            explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        kernel_components=dict(actual_cached_period_certificate=True,
            full_cached_pair_relation_gcd_preserved_by_actual_representative_scan=True,
            exact_signed_reference_star_cancellation=True,
            actual_sorted_adjacent_period_equals_representative_cache=True,
            natural_residue_projection_preserves_signed_relation_gcd=True,
            sorted_scan_value_comparisons_at_most_original_packets=True,
            integer_period_gcd_queries_le_original_packets=True,
            further_base_probe_soundness_and_query_bound=True,
            balanced_common_modulus_threshold_at_least_B=True,
            fewer_than_three_B_wrap_labels=True,four_B_checked_reconstruction_bound=True,
            common_modulus_from_actual_cache_and_public_checks=True,
            full_public_2047_probe_positive_control=True,
            full_public_2304167_wrapped_positive_control=True,
            full_public_sorted_2304167_wrapped_positive_control=True,
            any_signed_exponent_list_original_detector_failure_at_2047=True,
            public_probe_menu_exhaustion_at_2304167=True,
            full_balanced_public_zero_period_control_at_143=True),
        is_complete_factorizer=False,is_bit_complexity_certificate=False,
        is_formal_native_machine_refinement=False,one_sixth_guarantee="OPEN",
        limitations="The cached relation GCD is a certified period multiple, possibly zero, not necessarily the exact order or a divisor of both field cardinalities. The balanced reconstruction theorem requires p<=q<=2p, N<=B^6, D>=B and public prime-divisor unit checks; a prime D reduces the latter to one public g-1 check. No theorem makes these conditions universal or charges their acquisition in a deterministic bit machine. The actual public Lean control computes the entire original packet cache before recovery, without period, collision, factor or wrap-label advice. The actual sorted-adjacent extractor equals the representative procedure, retains exactly the full pair-relation GCD and uses R-1 adjacent comparisons after sorting. The compiled scan count does not price sorting, Boolean comparisons, exponent construction, integer GCDs or a universal packet bound. The native explicit merge sort has separately charged value comparisons and tag writes, with no cache hash lookup; Python arithmetic and list storage remain outside a complete formal bit machine. The all-signed-list negative theorem concerns only the fixed base-two pair/endpoint detector at N=2047; it does not rule out other observables, bases or factoring methods. Private component orders remain diagnostic. Every listed public construction and recovery operation is inside its timer. No every-run guarantee, arbitrary-ratio completion or universal guaranteed sixth-root factorization follows.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),native_cases=len(native),
        native_factors=sum(r["factor"] is not None for r in native),
        native_stages=dict(Counter(r["stage"] for r in native)),
        one_sixth_guarantee="OPEN")),flush=True)


if __name__ == "__main__":
    main()

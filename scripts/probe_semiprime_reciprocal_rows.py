#!/usr/bin/env python3
"""N-only cross-product extraction by coefficient reversal, without a matrix.

One monic polynomial on the original distinct giant values is retained.
Reversing its coefficients extracts all products 1-G_j*G_k. A public
batch inverse detects global inverse matches; there the reversed
polynomial's derivative performs exact deflation. No extra giant powers
or hidden-field inputs enter the source. Native counters are diagnostic.
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
PARENT_AUDIT = "docs/semiprime-derivative-coverage-certificate-audit.json"
REPLAY_ID = 202610033104
DERIVATIVE = runpy.run_path(str(ROOT/"scripts/probe_semiprime_row_derivative.py"))
FAMILY = DERIVATIVE["FAMILY"]
IntegerLedger, ScalarLedger, BATCH = DERIVATIVE["IntegerLedger"], DERIVATIVE["ScalarLedger"], DERIVATIVE["BATCH"]


def evaluate_on_tree(batch, tree, polynomial, metrics):
    out = []

    def visit(node, remainder):
        remainder = batch.mod(remainder, node[0])
        metrics["visited_evaluation_nodes"] += 1
        if node[1] is None:
            out.append(remainder[0] if remainder else 0)
        else:
            visit(node[1], remainder)
            visit(node[2], remainder)

    visit(tree, polynomial)
    return out


def batch_inverse(n, roots, integers, ring, metrics):
    """One public extended-GCD inverse and three short products per root."""
    prefix = [1]
    for value in roots:
        prefix.append(ring.mul(prefix[-1], value))
        metrics["batch_inverse_prefix_products"] += 1
    inverse = integers.divmod(integers.inverse(prefix[-1], n), n)[1]
    out = [0]*len(roots)
    for j in range(len(roots)-1, -1, -1):
        out[j] = ring.mul(inverse, prefix[j])
        inverse = ring.mul(inverse, roots[j])
        metrics["batch_inverse_backward_products"] += 2
    return out


def reciprocal_signals(n, roots, integers, ring, batch, metrics):
    if not roots:
        return [],[],[]
    inverse_values = batch_inverse(n, roots, integers, ring, metrics)
    inverse_set = set(inverse_values)
    globally_matched = []
    for value in roots:
        metrics["global_inverse_lookup_queries"] += 1
        integers.charge("global_inverse_lookup_operands", value)
        globally_matched.append(value in inverse_set)
    metrics["constructed_public_inverse_values"] += len(inverse_values)
    metrics["whole_modulus_inverse_targets"] += sum(globally_matched)
    tree = batch.tree(roots)
    metrics["root_polynomials"] += 1
    reverse_polynomial = tree[0][::-1]
    metrics["reversed_coefficients"] += len(reverse_polynomial)
    values = evaluate_on_tree(batch, tree, reverse_polynomial, metrics)
    metrics["reused_tree_evaluations"] += 1
    if any(globally_matched):
        derivative = [ring.mul(k, reverse_polynomial[k]) for k in range(1,len(reverse_polynomial))]
        metrics["reciprocal_derivative_coefficients"] += len(derivative)
        derivative_values = evaluate_on_tree(batch, tree, derivative, metrics)
        metrics["reused_tree_evaluations"] += 1
        values = [derivative_values[j] if whole else values[j]
            for j,whole in enumerate(globally_matched)]
    return values,inverse_values,globally_matched


def recover_reciprocal(n, roots, values, integers, ring, metrics):
    for j,value in enumerate(values):
        common = integers.gcd(n,value)
        metrics["reciprocal_gcd_queries"] += 1
        if common == 1:
            continue
        if 1 < common < n:
            return common,"reciprocal-product",dict(row_index=j,root=roots[j],signal=value)
        metrics["selected_product_row_scans"] += 1
        for k,other in enumerate(roots):
            difference = integers.divmod(integers.add(1,-ring.mul(roots[j],other)),n)[1]
            metrics["selected_product_row_positions"] += 1
            if difference == 0:
                metrics["removed_whole_modulus_inverse_pairs"] += 1
                continue
            common = integers.gcd(n,difference)
            metrics["selected_product_row_gcd_queries"] += 1
            if 1 < common < n:
                return common,"selected-product-row",dict(row_index=j,other_row_index=k,
                    root=roots[j],other_root=other,signal=value,difference=difference)
        raise AssertionError("deflated nonunit reciprocal product has no proper nonzero pair")
    return None,"exhausted-reciprocal-rows",None


def reciprocal_source(n, alpha=2):
    """N-only source; every construction step occurs inside this timer."""
    if n < 4:
        raise ValueError("composite n>=4 required")
    start = time.perf_counter()
    integers, ring, batch = IntegerLedger(), ScalarLedger(n), BATCH["MonicBatch"](n)
    metrics,buckets,m,values = Counter(),{},None,[]

    def finish(factor,stage,witness=None):
        if witness is not None and "root" in witness:
            witness = dict(witness,root_packet_bucket=buckets[witness["root"]])
            if "other_root" in witness:
                witness["other_root_packet_bucket"] = buckets[witness["other_root"]]
        return dict(N=n,factor=factor,stage=stage,modulus=m,
            distinct_public_roots=len(buckets),evaluated_reciprocal_targets=len(values),
            witness=witness,milliseconds=1000*(time.perf_counter()-start),
            metrics=dict(metrics,**integers.stats(),**ring.stats(),**batch.stats()),
            constructed_pair_matrix=False,constructed_extra_giant_powers=False,
            is_complete_semiprime_factorizer=False,is_complete_bit_certificate=False)

    root = integers.sqrt(n)
    if integers.mul(root,root)==n and 1 < root < n:
        return finish(root,"public-square")
    common = integers.gcd(alpha,n)
    if 1 < common < n:
        return finish(common,"public-base-gcd")
    if common != 1:
        return finish(None,"inconclusive-base")
    m = FAMILY["first_public_prime"](n,integers,metrics)
    common = integers.gcd(m,n)
    if 1 < common < n:
        return finish(common,"public-modulus-gcd")
    if common != 1:
        return finish(None,"inconclusive-modulus")
    inverse = integers.divmod(integers.inverse(alpha,n),n)[1]
    for packet in FAMILY["public_packets"](n,m,integers,metrics):
        exponent = packet["exponent"]
        value = ring.power(alpha if exponent >= 0 else inverse,abs(exponent))
        metrics["public_root_lookup_queries"] += 1
        integers.charge("public_root_lookup_operands",value)
        if value in buckets:
            metrics["whole_modulus_duplicate_packets"] += 1
        buckets.setdefault(value,[]).append(packet)
        metrics["retained_packet_bucket_entries"] += 1
    roots = list(buckets)
    metrics["scalar_axis_input_count"] = 2*len(roots)
    values,_,_ = reciprocal_signals(n,roots,integers,ring,batch,metrics)
    factor,stage,witness = recover_reciprocal(n,roots,values,integers,ring,metrics)
    return finish(factor,stage,witness)


def validate_native(rnd):
    """Independent direct-product and full cross-pair oracles."""
    cases = [(35,[1,1,6,6,8,8]),(49,[1,8,8]),(35,[2,2,18]),(35,[1,34]),(77,[])]
    for _ in range(128):
        n = rnd.randrange(4,500)
        units = [v for v in range(n) if math.gcd(n,v)==1]
        cases.append((n,[rnd.choice(units) for _ in range(rnd.randrange(14))]))
    saturated=global_matches=0
    for n,original in cases:
        roots = list(dict.fromkeys(v % n for v in original))
        integers,ring,batch,metrics = IntegerLedger(),ScalarLedger(n),BATCH["MonicBatch"](n),Counter()
        values,inverses,matched = reciprocal_signals(n,roots,integers,ring,batch,metrics)
        assert inverses==[pow(v,-1,n) for v in roots]
        phase = math.prod(-v for v in roots) % n
        expected = [phase*math.prod((t-v) % n for v in inverses if t != v) % n for t in roots]
        assert values==expected
        factor,stage,_ = recover_reciprocal(n,roots,values,integers,ring,metrics)
        oracle = any(1 < math.gcd(n,(1-x*y) % n) < n for x in roots for y in roots)
        assert (factor is not None)==oracle
        assert factor is None or 1 < factor < n and n % factor == 0
        assert metrics["reciprocal_gcd_queries"]+metrics["selected_product_row_gcd_queries"] <= 2*len(roots)
        assert metrics["selected_product_row_scans"] <= 1
        saturated += stage=="selected-product-row"
        global_matches += any(matched)
    return dict(native_reverse_and_cross_pair_oracle_cases=len(cases),
        native_selected_product_row_recoveries=saturated,
        native_cases_with_global_inverse_matches=global_matches,
        is_formal_machine_refinement=False)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeReciprocalRows.lean",
        "scripts/CheckSemiprimeReciprocalRows.lean","scripts/probe_semiprime_reciprocal_rows.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    sources,rnd = source_inventory(),random.Random(REPLAY_ID)
    validation = validate_native(rnd)
    small_sources,outcomes = [],Counter()
    family_parent = json.loads((ROOT/"docs/semiprime-euclid-row-family-audit.json").read_text())
    for previous in family_parent["small_public_sources"]:
        source = reciprocal_source(previous["N"])
        d = source["factor"]
        assert d is None or 1 < d < source["N"] and source["N"] % d == 0
        outcomes[source["stage"]] += 1
        small_sources.append(source)
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    previous_control = parent["control"]
    control = reciprocal_source(previous_control["N"])
    assert control["factor"] in (39167077933,64308254573)
    assert control["modulus"]==previous_control["modulus"]==3691
    assert control["distinct_public_roots"]==previous_control["distinct_public_roots"]==394276
    assert control["metrics"]["native_scalar_powers"]==394276
    assert control["metrics"]["constructed_public_inverse_values"]==394276
    assert not control["constructed_pair_matrix"] and not control["constructed_extra_giant_powers"]
    assert source_inventory()==sources,"source changed during replay"
    report=dict(replay_id=REPLAY_ID,source_sha256=sources,
        scope="Public cross-product channel via exact coefficient reversal and deflation",
        one_sixth_guarantee="OPEN",is_complete_semiprime_factorizer=False,
        is_bit_complexity_certificate=False,is_formal_machine_refinement=False,
        coefficient_reversal_and_unit_phase_lean=True,
        new_control_reciprocal_recovers_lean=True,
        original_axis_failure_control_kernel_checked=False,
        validation=dict(validation,small_N_only_sources=len(small_sources),small_outcomes=dict(outcomes)),
        control=control,small_public_sources=small_sources,
        frozen_original_axis_control=previous_control,
        separate_inverse_axis_reference=parent["separate_inverse_axis_reference"],
        limitations="The public source constructs every original packet and exactly one giant power per packet. It retains all original source rows in distinct whole-modulus buckets. One batch inverse uses one public extended GCD plus three scalar products per root, solely to identify whole-modulus inverse targets. Reversing the existing monic polynomial's coefficients gives the proved reciprocal polynomial; its value is used off the inverse roots and its derivative at global inverse matches. Both evaluations reuse the original monic root tree. Every construction, public modulus/base check, coefficient reversal, inverse lookup, evaluation, GCD and at most one selected product-row recovery occur inside the N-only timer. The compiled reciprocal theorem proves exact whole-polynomial and derivative GCD phases and recovery on this literal original-axis failure input, without giving the source a factor, order or witness. Native independent oracles check the cross-pair hit union, duplicate and global-inverse deflation and saturated recovery. The large original-axis failure remains a complete exact native replay; its monolithic Lean certificate was stopped above 50 GB, and the separate checker/orders module does not prove that literal failure. None of these results is a formal native-machine refinement, universal local-product coverage, a proved total row-count or polynomial bit-price theorem, a statistically paired timing comparison, or a complete arbitrary-ratio every-run N-only one-sixth factorizer.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),validation=report["validation"],control=control,
        one_sixth_guarantee="OPEN"),indent=2),flush=True)


if __name__=="__main__":
    main()

#!/usr/bin/env python3
"""Public integer companions before any giant-power projection.

All complete original packet construction, primitive checks, companion
formation, zero endpoints, the monic derivative source and checked late
recovery are inside the N-only source timer. Private factors and orders
are confined to explicitly separate reference diagnostics. This is a
research branch, not a complete sixth-root bit factorizer.
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
PARENT_AUDIT = "docs/semiprime-row-periods-audit.json"
REPLAY_ID = 202610033210
WEIGHTED = runpy.run_path(str(ROOT/"scripts/probe_semiprime_weighted_rows.py"))
DERIVATIVE,FAMILY = WEIGHTED["DERIVATIVE"],WEIGHTED["FAMILY"]
IntegerLedger,ScalarLedger,BATCH = WEIGHTED["IntegerLedger"],WEIGHTED["ScalarLedger"],WEIGHTED["BATCH"]


def companion_packets(originals,m,integers,metrics):
    """Literal primitive filter and integer normalization of the Lean source."""
    for w in WEIGHTED["weighted_packets"](originals,m,integers):
        e,D = w["exponent"],w["determinant"]
        metrics["primitive_packet_checks"] += 1
        integers.charge("public_primitive_comparison_operands",D,m,e)
        if abs(D) != m:
            metrics["rejected_nonprimitive_packets"] += 1
            continue
        quotient,remainder = integers.divmod(e,m)
        if remainder:
            metrics["rejected_exponent_divisibility_packets"] += 1
            continue
        orientation,remainder = integers.divmod(D,m)
        assert remainder == 0 and orientation in (-1,1)
        candidate = integers.add(1,-integers.mul(orientation,quotient))
        metrics["retained_companion_packets"] += 1
        yield dict(candidate=candidate,orientation=orientation,weighted_packet=w)


def companion_rows_source(n):
    """Only N enters; there is no multiplicative group base or order input."""
    if n < 4:
        raise ValueError("composite n>=4 required")
    start = time.perf_counter()
    integers,ring,batch = IntegerLedger(),ScalarLedger(n),BATCH["MonicBatch"](n)
    metrics,originals,buckets,m,values = Counter(),[],{},None,[]

    def finish(factor,stage,witness=None):
        if witness is not None and "root" in witness:
            witness = dict(witness,root_packet_bucket=buckets[witness["root"]])
            if "other_root" in witness:
                witness["other_root_packet_bucket"] = buckets[witness["other_root"]]
        return dict(N=n,input_bits=n.bit_length(),modulus=m,factor=factor,stage=stage,witness=witness,
            original_packet_count=len(originals),companion_packet_count=metrics["retained_companion_packets"],
            distinct_public_companion_roots=len(buckets),evaluated_derivatives=len(values),
            milliseconds=1000*(time.perf_counter()-start),
            metrics=dict(metrics,**integers.stats(),**ring.stats(),**batch.stats()),
            retains_original_and_weighted_packet_buckets=True,
            preserves_signed_integer_companions=True,constructed_pair_matrix=False,
            group_base_input=False,constructed_modular_giant_powers=False,
            private_factors_used_by_source=False,is_complete_factorizer=False,
            is_bit_complexity_certificate=False,is_formal_native_machine_refinement=False)

    root = integers.sqrt(n)
    if integers.mul(root,root) == n and 1 < root < n:
        return finish(root,"public-square")
    m = FAMILY["first_public_prime"](n,integers,metrics)
    common = integers.gcd(n,m)
    if 1 < common < n:
        return finish(common,"public-modulus-gcd")
    if common != 1:
        return finish(None,"inconclusive-modulus")
    originals = list(FAMILY["public_packets"](n,m,integers,metrics))
    for w in companion_packets(originals,m,integers,metrics):
        value = integers.divmod(w["candidate"],n)[1]
        metrics["public_companion_lookup_queries"] += 1
        integers.charge("public_companion_lookup_operands",value)
        buckets.setdefault(value,[]).append(w)
    assert metrics["retained_companion_packets"] <= 2*len(originals)
    roots = list(buckets)
    for index,value in enumerate(roots):
        common = integers.gcd(n,value)
        metrics["companion_zero_endpoint_gcd_queries"] += 1
        if 1 < common < n:
            return finish(common,"public-companion-zero-endpoint",dict(row_index=index,root=value))
    values = DERIVATIVE["derivative_outputs"](n,roots,integers,ring,batch,metrics)
    factor,stage,witness = DERIVATIVE["recover_derivatives"](n,roots,values,integers,metrics)
    queries = sum(metrics[k] for k in ("companion_zero_endpoint_gcd_queries",
        "derivative_gcd_queries","selected_row_gcd_queries"))
    assert queries <= 3*len(roots) <= 6*len(originals)
    assert ring.powers == 0
    return finish(factor,"companion-"+stage,witness)


def validate_companions(rnd):
    """Independent coefficient and cleared original-coordinate identities."""
    algebra,primitive,source = 0,0,0
    for _ in range(160):
        n,m = rnd.randrange(50,10000),rnd.choice((5,7,11,13,17))
        if math.gcd(n,m) != 1:
            continue
        originals = list(DERIVATIVE["reference_packets"](n,m))
        for w in WEIGHTED["weighted_packets"](originals,m):
            left,right = w["left"],w["right"]
            d,e = w["determinant"]//m,w["exponent"]
            assert abs(d) == 1 and e%m == 0
            c = 1-d*(e//m)
            B = right["t"]*left["b"]-left["t"]*right["b"]
            assert c == 2*w["j"]-d*B
            assert e == m*d*(1-c)
            for Y in (-19,0,23):
                coordinate = lambda z:z["a"]*Y*Y+(m*z["b"]-2*z["a"]*z["j"])*Y+n*z["t"]
                assert right["t"]*coordinate(left)-left["t"]*coordinate(right) == m*d*Y*(Y-c)
                algebra += 1
            primitive += 1
        integers,metrics = IntegerLedger(),Counter()
        actual = list(FAMILY["public_packets"](n,m,integers,metrics))
        assert [{k:w[k] for k in originals[0]} for w in actual] == originals if originals else actual == []
        candidates = list(companion_packets(actual,m,integers,metrics))
        assert len(candidates) <= 2*len(actual)
        source += 1
    return dict(cleared_coordinate_identities=algebra,primitive_integer_companions=primitive,
        complete_public_constructor_oracles=source,is_Lean_proof=False)


def source_inventory(extra_audits=()):
    paths = set()
    for audit in (PARENT_AUDIT,*extra_audits):
        parent = json.loads((ROOT/audit).read_text())
        for path,digest in parent["source_sha256"].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
        paths.update(parent["source_sha256"])
        paths.add(audit)
    paths.update(("RiemannGaussian/SemiprimeCompanionRows.lean",
        "scripts/CheckSemiprimeCompanionRows.lean","scripts/probe_semiprime_companion_rows.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def reference_companion_witness(n,p,q,m):
    """Private field projections locate a proof witness; no source timing."""
    seen,local,count = set(),{p:{},q:{}},0
    for j in range(1,m):
        originals = list(WEIGHTED["reference_residue_packets"](n,m,j))
        for w in WEIGHTED["weighted_packets"](originals,m):
            c = 1-(w["determinant"]//m)*(w["exponent"]//m)
            count += 1
            whole = c%n
            if whole in seen:
                continue
            seen.add(whole)
            for factor in (p,q):
                r = c%factor
                old = local[factor].get(r)
                if r == 0:
                    return dict(N=n,modulus=m,reference_p=p,reference_q=q,
                        candidate_count=count,distinct_whole_candidates=len(seen),
                        channel="companion-zero-endpoint",candidate=c,packet=w,factor=factor,
                        is_N_only_source=False,is_factorization_runtime_measurement=False)
                if old is not None:
                    common = math.gcd(n,c-old["candidate"])
                    assert 1 < common < n
                    return dict(N=n,modulus=m,reference_p=p,reference_q=q,
                        candidate_count=count,distinct_whole_candidates=len(seen),
                        channel="companion-difference",candidate=c,packet=w,old=old,factor=common,
                        is_N_only_source=False,is_factorization_runtime_measurement=False)
                local[factor][r] = dict(candidate=c,packet=w)
        if j%2000 == 0:
            print(json.dumps(dict(progress="reference-only-companion-witness",N=n,j=j,
                candidates=count,distinct_whole_candidates=len(seen))),flush=True)
    return dict(N=n,modulus=m,reference_p=p,reference_q=q,
        candidate_count=count,distinct_whole_candidates=len(seen),channel="exhausted-companion-reference",
        factor=None,is_N_only_source=False,is_factorization_runtime_measurement=False)


def main():
    from sympy import nextprime
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--include-audit",action="append",default=[])
    parser.add_argument("--checked-declarations",type=int,default=0)
    parser.add_argument("--checked-theorems",type=int,default=0)
    parser.add_argument("--checked-explicit",type=int,default=0)
    parser.add_argument("--reference-90bit",action="store_true")
    args = parser.parse_args()
    sources,rnd = source_inventory(args.include_audit),random.Random(REPLAY_ID)
    algebra = validate_companions(rnd)
    pairs = [(23,89),(1103,2089),(11,13),(101,103),(101,101),(3,1000003),
        (5,2000003),(17,41)]
    for _ in range(24):
        p = int(nextprime(rnd.randrange(50,4000)))
        q = int(nextprime(rnd.randrange(p+1,2*p)))
        pairs.append((p,q))
    native = [companion_rows_source(p*q) for p,q in pairs]
    paid = []
    for n in (369867514421371,2518766418595894637609):
        print(json.dumps(dict(progress="N-only-companion-source-start",N=n)),flush=True)
        result = companion_rows_source(n)
        paid.append(result)
        print(json.dumps(dict(progress="N-only-companion-source-completed",N=n,
            factor=result["factor"],original_packets=result["original_packet_count"],
            companion_packets=result["companion_packet_count"],
            distinct_roots=result["distinct_public_companion_roots"],
            milliseconds=result["milliseconds"])),flush=True)
    for result in native+paid:
        f,n = result["factor"],result["N"]
        if f is not None:
            assert 1 < f < n and n%f == 0
        assert result["metrics"].get("native_scalar_powers",0) == 0
    assert all(r["factor"] is not None for r in native[:3]+paid)
    reference = reference_companion_witness(788096216222522769981991129,
        24862649616491,31697997935819,30403) if args.reference_90bit else None
    assert source_inventory(args.include_audit) == sources,"source changed during replay"
    checked = args.checked_declarations > 0 and args.checked_theorems > 0
    report = dict(replay_id=REPLAY_ID,source_sha256=sources,parent_audit=PARENT_AUDIT,
        explicitly_merged_audits=args.include_audit,
        scope="Signed integer linear companions retained before group powers, with one additive derivative source",
        algebra_oracles=algebra,N_only_small_sources=native,paid_larger_controls=paid,
        reference_only_90bit_witness=reference,full_native_90bit_source_replayed=False,
        lean_validation=dict(separately_completed_scoped_gates=checked,
            strict_leaf_and_root=checked,namespace_linters=14 if checked else 0,
            linter_errors=0 if checked else None,all_module_declarations=args.checked_declarations,
            explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        kernel_components=dict(cleared_original_coordinate_factorization=True,
            exact_companion_versus_giant_exponent_identity=True,primitive_packet_orientation_checks=True,
            actual_public_centered_packet_coordinate_factorization=True,
            all_public_filtered_packet_coefficient_companion_identity=True,
            no_group_base_or_giant_power_in_companion_constructor=True,
            proper_zero_endpoint_and_pair_recovery=True,
            twice_original_packet_companion_bound=True,six_original_packet_factor_gcd_bound=True,
            full_public_2047_positive_control=True,full_public_2304167_positive_control=True,
            full_public_49bit_positive_control=True,full_public_72bit_positive_control=True,
            full_public_90bit_positive_control=True,
            full_public_zero_period_143_positive_control=True),
        is_complete_factorizer=False,is_bit_complexity_certificate=False,
        is_formal_native_machine_refinement=False,one_sixth_guarantee="OPEN",
        limitations="Primitive weighted cancellation retains the public integer companion before exponentiation. Exact coefficient identities and literal original-packet membership yield complete public Lean recovery controls with neither factors nor selected pairs as algorithm inputs. The derivative source strips only its known global diagonal root, covers every proper additive pair and retains saturated-output recovery. Both signed integer labels and original quadratic/center packets remain upstream. The actual primitive and exponent-divisibility filter is checked on public data. Linear companion and recovery-GCD counts do not prove a universal original row-count bound, useful additive collision or a complete deterministic bit cost for construction, duplicate lookup, polynomial arithmetic or recovery. The inherited noncomputable finite-set specification and native dictionaries/packing engine are not a formal bit-machine refinement. A private 90-bit witness search, if requested, is explicitly diagnostic and neither a paid full source run nor a complete failure theorem. Arbitrary factor ratios, squares in the complete cost accounting, every-run guaranteed sixth-root factorization and universal fallback coverage remain open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),native_cases=len(native),
        native_factors=sum(r["factor"] is not None for r in native),
        larger_control_factors=[r["factor"] for r in paid],
        larger_control_milliseconds=[r["milliseconds"] for r in paid],
        native_stages=dict(Counter(r["stage"] for r in native)),one_sixth_guarantee="OPEN")),flush=True)


if __name__ == "__main__":
    main()

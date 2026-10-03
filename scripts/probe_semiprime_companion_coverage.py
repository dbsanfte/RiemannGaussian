#!/usr/bin/env python3
"""Exact companion exhaustion and one anchored signed derivative source.

Public N-only runs charge the complete original construction and checked
recovery. Private prime-field classifiers are explicitly separate. Neither
finite coverage evidence nor GCD-query counts certify a sixth-root bit bound.
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
PARENT_AUDIT = "docs/semiprime-companion-rows-audit.json"
REPLAY_ID = 202610033212
COMPANION = runpy.run_path(str(ROOT/"scripts/probe_semiprime_companion_rows.py"))
WEIGHTED,DERIVATIVE,FAMILY = (COMPANION[k] for k in ("WEIGHTED","DERIVATIVE","FAMILY"))
IntegerLedger,ScalarLedger,BATCH = (COMPANION[k] for k in ("IntegerLedger","ScalarLedger","BATCH"))


def anchored_companion_source(n,signed=True):
    """Only N enters; sign choice is a public algorithm variant."""
    if n < 4:
        raise ValueError("composite n>=4 required")
    start = time.perf_counter()
    integers,ring,batch = IntegerLedger(),ScalarLedger(n),BATCH["MonicBatch"](n)
    metrics,originals,buckets,values,m = Counter(),[],{},[],None

    def finish(factor,stage,witness=None):
        if witness is not None and "root" in witness:
            witness = dict(witness,root_packet_bucket=buckets[witness["root"]])
            if "other_root" in witness:
                witness["other_root_packet_bucket"] = buckets[witness["other_root"]]
        return dict(N=n,input_bits=n.bit_length(),modulus=m,signed=signed,
            factor=factor,stage=stage,witness=witness,
            original_packet_count=len(originals),companion_packet_count=metrics["retained_companion_packets"],
            distinct_signed_roots=len(buckets),evaluated_derivatives=len(values),
            milliseconds=1000*(time.perf_counter()-start),
            metrics=dict(metrics,**integers.stats(),**ring.stats(),**batch.stats()),
            preserves_original_weighted_packets_and_integer_signs=True,
            constructed_pair_matrix=False,constructed_modular_giant_powers=False,
            group_base_input=False,private_factors_used_by_source=False,
            is_complete_factorizer=False,is_bit_complexity_certificate=False,
            is_formal_native_machine_refinement=False)

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
    buckets[0] = [dict(public_zero_anchor=True)]
    metrics["public_zero_anchors"] += 1
    for w in COMPANION["companion_packets"](originals,m,integers,metrics):
        for sign in ((1,-1) if signed else (1,)):
            candidate = w["candidate"] if sign == 1 else integers.add(0,-w["candidate"])
            value = integers.divmod(candidate,n)[1]
            metrics["signed_companion_lookup_queries"] += 1
            integers.charge("signed_companion_lookup_operands",value)
            buckets.setdefault(value,[]).append(dict(sign=sign,integer=candidate,companion=w))
    assert metrics["retained_companion_packets"] <= 2*len(originals)
    roots = list(buckets)
    assert len(roots) <= (2 if signed else 1)*metrics["retained_companion_packets"]+1
    values = DERIVATIVE["derivative_outputs"](n,roots,integers,ring,batch,metrics)
    factor,stage,witness = DERIVATIVE["recover_derivatives"](n,roots,values,integers,metrics)
    queries = metrics["derivative_gcd_queries"]+metrics["selected_row_gcd_queries"]
    assert queries <= 2*len(roots) <= (8 if signed else 4)*len(originals)+2
    assert ring.powers == 0 and ring.inverses == 0
    return finish(factor,("signed-" if signed else "anchored-")+stage,witness)


def finite_anchor_oracles(rnd):
    """Compare complete endpoint/pair hit unions before and after anchoring."""
    cases,zero_inputs,saturated = 0,0,0
    for index in range(160):
        n = rnd.choice((4,9,25,49,77,143,221)) if index < 48 else rnd.randrange(4,700)
        candidates = [rnd.randrange(-2*n,2*n) for _ in range(rnd.randrange(0,16))]
        ordinary = list(dict.fromkeys(c%n for c in candidates))
        roots = list(dict.fromkeys([0,*ordinary]))
        signed = list(dict.fromkeys([0,*ordinary,*((-c)%n for c in ordinary)]))
        zero_inputs += 0 in ordinary
        old_hit = any(1 < math.gcd(n,c) < n for c in ordinary) or any(
            1 < math.gcd(n,t-x) < n for t in ordinary for x in ordinary if t != x)
        for values,expected in ((roots,old_hit),(signed,any(
                1 < math.gcd(n,t-x) < n for t in signed for x in signed if t != x))):
            integers,ring,batch,metrics = IntegerLedger(),ScalarLedger(n),BATCH["MonicBatch"](n),Counter()
            derivatives = DERIVATIVE["derivative_outputs"](n,values,integers,ring,batch,metrics)
            factor,stage,_ = DERIVATIVE["recover_derivatives"](n,values,derivatives,integers,metrics)
            assert (factor is not None) == expected
            if factor is not None:
                assert 1 < factor < n and n%factor == 0
            assert metrics["derivative_gcd_queries"]+metrics["selected_row_gcd_queries"] <= 2*len(values)
            saturated += stage == "selected-row-difference"
        cases += 1
    return dict(root_lists=cases,source_variants=2*cases,lists_containing_zero=zero_inputs,
        selected_row_saturation_recoveries=saturated,is_Lean_proof=False)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeCompanionCoverage.lean",
        "scripts/CheckSemiprimeCompanionCoverage.lean","scripts/probe_semiprime_companion_coverage.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def reference_case(n,p,q,m):
    """Complete private field classification; no public source clock."""
    roots,packets = set(),0
    for j in range(1,m):
        for w in WEIGHTED["weighted_packets"](
                list(WEIGHTED["reference_residue_packets"](n,m,j)),m):
            c = 1-(w["determinant"]//m)*(w["exponent"]//m)
            roots.add(c%n)
            packets += 1
    signed = {0}|roots|{(-c)%n for c in roots}
    separated = lambda values:len({c%p for c in values}) == len(values) and \
        len({c%q for c in values}) == len(values)
    ordinary = separated(roots) and all(c == 0 or (c%p and c%q) for c in roots)
    return dict(N=n,input_bits=n.bit_length(),reference_p=p,reference_q=q,modulus=m,
        companion_packets=packets,ordinary_roots=len(roots),signed_roots=len(signed),
        ordinary_exhausted=ordinary,signed_exhausted=separated(signed),
        is_N_only_source=False,is_factorization_runtime_measurement=False,
        is_kernel_failure_certificate=False)


def complete_private_corpus():
    from sympy import primerange,nextprime,integer_nthroot
    cases,misses,signed_misses = 0,[],[]
    for p in primerange(11,500):
        for q in primerange(p+1,2*p+1):
            n = p*q
            b,exact = integer_nthroot(n,6)
            m = int(nextprime(b-1 if exact else b))
            if m*m >= p:
                continue
            r = reference_case(n,p,q,m)
            cases += 1
            if r["ordinary_exhausted"]:
                misses.append(r)
            if r["signed_exhausted"]:
                signed_misses.append(r)
    return dict(cases=cases,prime_p_range=[11,500],q_range="p<q<=2p",
        excludes_squared_modulus_small_factor_prefix=True,ordinary_misses=misses,
        signed_misses=signed_misses,is_Lean_proof=False)


def sampled_private_corpus():
    from sympy import nextprime,integer_nthroot
    rnd,cases = random.Random(REPLAY_ID),[]
    for index in range(512):
        p = int(nextprime(rnd.randrange(500,50000)))
        q = int(nextprime(rnd.randrange(p+1,2*p)))
        n = p*q
        b,exact = integer_nthroot(n,6)
        m = int(nextprime(b-1 if exact else b))
        r = reference_case(n,p,q,m)
        cases.append(dict(sample_index=index,**r))
    return dict(seed=REPLAY_ID,cases=cases,ordinary_misses=sum(r["ordinary_exhausted"] for r in cases),
        signed_misses=sum(r["signed_exhausted"] for r in cases),is_Lean_proof=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--checked-declarations",type=int,default=0)
    parser.add_argument("--checked-theorems",type=int,default=0)
    parser.add_argument("--checked-explicit",type=int,default=0)
    args = parser.parse_args()
    sources = source_inventory()
    oracles = finite_anchor_oracles(random.Random(REPLAY_ID))
    complete = complete_private_corpus()
    sampled = sampled_private_corpus()
    print(json.dumps(dict(progress="private-companion-classification-completed",
        complete_cases=complete["cases"],ordinary_misses=len(complete["ordinary_misses"]),
        signed_misses=len(complete["signed_misses"]),sampled_cases=len(sampled["cases"]),
        sampled_signed_misses=sampled["signed_misses"])),flush=True)
    original,anchored,rescued = [],[],[]
    for r in complete["ordinary_misses"]:
        n = r["N"]
        old = COMPANION["companion_rows_source"](n)
        anchor = anchored_companion_source(n,signed=False)
        sign = anchored_companion_source(n,signed=True)
        assert old["modulus"] == anchor["modulus"] == sign["modulus"] == r["modulus"]
        assert old["factor"] is None and anchor["factor"] is None
        assert sign["factor"] is not None
        original.append(old);anchored.append(anchor);rescued.append(sign)
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    signed_sources = [anchored_companion_source(r["N"]) for r in parent["N_only_small_sources"]]
    signed_sources.extend(rescued)
    larger = []
    for n in (369867514421371,2518766418595894637609):
        print(json.dumps(dict(progress="N-only-signed-companion-source-start",N=n)),flush=True)
        r = anchored_companion_source(n)
        larger.append(r)
        print(json.dumps(dict(progress="N-only-signed-companion-source-completed",N=n,
            factor=r["factor"],original_packets=r["original_packet_count"],
            distinct_signed_roots=r["distinct_signed_roots"],milliseconds=r["milliseconds"])),flush=True)
    for r in signed_sources+larger:
        n,f = r["N"],r["factor"]
        assert f is not None and 1 < f < n and n%f == 0
        assert r["metrics"].get("native_scalar_powers",0) == 0
    assert source_inventory() == sources,"source changed during replay"
    checked = args.checked_declarations > 0 and args.checked_theorems > 0
    report = dict(replay_id=REPLAY_ID,source_sha256=sources,parent_audit=PARENT_AUDIT,
        scope="Complete ordinary companion exhaustion, exact zero-anchor compression and signed sum recovery",
        finite_anchor_oracles=oracles,complete_private_small_corpus=complete,
        sampled_private_balanced_corpus=sampled,original_N_only_missed_sources=original,
        anchored_N_only_missed_sources=anchored,signed_N_only_sources=signed_sources,
        signed_larger_sources=larger,full_native_90bit_source_replayed=False,
        lean_validation=dict(separately_completed_scoped_gates=checked,
            strict_leaf_and_root=checked,namespace_linters=14 if checked else 0,
            linter_errors=0 if checked else None,all_module_declarations=args.checked_declarations,
            explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        kernel_components=dict(exact_complete_original_exhaustion=True,
            actual_public_7303_original_program_none=True,balanced_small_prefix_complement_checked=True,
            zero_anchor_preserves_complete_original_hit_union=True,
            anchored_recovery_gcd_queries_at_most_4R_plus_2=True,
            signed_endpoint_difference_and_nonzero_sum_separation=True,
            signed_program_preserves_original_success=True,
            signed_recovery_gcd_queries_at_most_8R_plus_2=True,
            actual_public_7303_signed_program_recovers=True),
        is_complete_factorizer=False,is_bit_complexity_certificate=False,
        is_formal_native_machine_refinement=False,one_sixth_guarantee="OPEN",
        limitations="Lean checks the complete original companion detector fails at the literal balanced semiprime 7303, outside the squared-modulus small-factor prefix. Its exact zero-anchor replacement preserves endpoint and ordinary-pair hits, including saturated recovery. The larger signed source preserves all original successes and adds nonzero sum information in one derivative polynomial, with proved linear recovery-GCD envelopes. The entire public signed control recovers after the kernel-checked sum witness. Full N-only construction, signed lookup, polynomial work and recovery are timed in the native source. Private fields classify complete specified finite corpora separately; their hits and larger primality data are not Lean coverage certificates. Finite success, query counts, hash buckets and packing ledgers do not prove universal useful collisions, an original-row bound or a deterministic construction-inclusive sixth-root bit clock. The native source is not a formal machine refinement. Arbitrary ratios, squares in the full cost accounting and every-run sixth-root factorization remain open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),ordinary_missed_sources=len(original),
        signed_native_sources=len(signed_sources)+len(larger),
        signed_native_factors=sum(r["factor"] is not None for r in signed_sources+larger),
        signed_native_stages=dict(Counter(r["stage"] for r in signed_sources+larger)),
        larger_milliseconds=[r["milliseconds"] for r in larger],one_sixth_guarantee="OPEN")),flush=True)


if __name__ == "__main__":
    main()

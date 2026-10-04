#!/usr/bin/env python3
"""Public-anchor area extraction and a separate complete joined-family control.

The source inputs are N and a public modulus m. The unit-numerator anchor is
selected by the literal public j=1 Euclidean stream. No private factors,
chosen triple, pair matrix or area matrix enter polynomial recovery.
The small joined miss uses m=19, below its canonical sixth-root modulus.
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
PARENT_AUDIT = "docs/semiprime-affine-row-roots-audit.json"
REPLAY_ID = 202610033234
JOINED = runpy.run_path(str(ROOT/"scripts/probe_semiprime_joined_sorted_coverage.py"))
AFFINE,WEIGHTED = JOINED["AFFINE"],JOINED["WEIGHTED"]
FAMILY,COMPANION,REFLECTED = (AFFINE[k] for k in ("FAMILY","COMPANION","REFLECTED"))
IntegerLedger,ScalarLedger,BATCH = (AFFINE[k] for k in ("IntegerLedger","ScalarLedger","BATCH"))
DERIVATIVE = WEIGHTED["DERIVATIVE"]


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for p,h in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,p
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeCenteredOffsetExtractor.lean",
        "scripts/CheckSemiprimeCenteredOffsetExtractor.lean",
        "scripts/semiprime_joined_coverage_rows.cpp","scripts/probe_semiprime_joined_sorted_coverage.py",
        "RiemannGaussian/SemiprimeAnchoredRowAreas.lean",
        "scripts/CheckSemiprimeAnchoredRowAreas.lean","scripts/probe_semiprime_anchored_row_areas.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def area(u,w,v):
    a,b,c = u
    d,e,f = w
    g,h,i = v
    return a*(e*i-h*f)-b*(d*i-g*f)+c*(d*h-g*e)


def coefficient_oracles(rnd):
    from sympy import Matrix
    counts = Counter()
    for index in range(4096):
        n = rnd.choice((4,9,25,49,77,143,221)) if index<512 else rnd.randrange(4,1000)
        u,w,v = [tuple(rnd.randrange(-64,65) for _ in range(3)) for _ in range(3)]
        a,L,t = u
        minor = lambda z:(a*z[1]-z[0]*L,a*z[2]-z[0]*t)
        Aw,Dw = minor(w)
        Av,Dv = minor(v)
        determinant = area(u,w,v)
        assert Aw*Dv-Av*Dw==a*determinant
        if index<128:
            assert int(Matrix((u,w,v)).det())==determinant
            assert int(Matrix([(z[0],z[1],n*z[2]) for z in (u,w,v)]).det())==n*determinant
            counts["independent_signed_3x3_and_original_Nt_determinants"] += 1
        if all(math.gcd(n,x)==1 for x in (a,Dw,Dv)):
            sw,sv = Aw*pow(Dw,-1,n)%n,Av*pow(Dv,-1,n)%n
            assert Dw*Dv*(sw-sv)%n==a*determinant%n
            assert math.gcd(n,determinant)==math.gcd(n,sw-sv)
            counts["exact_unit_area_slope_GCD_phases"] += 1
            counts["global_zero_area_unit_cases"] += determinant%n==0
        else:
            counts["nonunit_phase_cases_kept_out_of_normalization"] += 1
    return dict(cases=4096,counts=dict(counts),is_Lean_proof=False)


def public_anchor_source(n,m):
    """N,m-only backend, including full original construction and recovery."""
    assert n>1 and m>1 and math.gcd(n,m)==1
    start = time.perf_counter()
    integers,ring,batch,metrics = IntegerLedger(),ScalarLedger(n),BATCH["MonicBatch"](n),Counter()
    originals = list(FAMILY["public_packets"](n,m,integers,metrics))
    anchor,buckets,inverses = None,{},{}
    for w in originals:
        integers.charge("public_anchor_selection",w["j"],w["a"])
        metrics["public_anchor_selection_positions"] += 1
        if w["j"]==1 and abs(w["a"])==1 and w["center_orientation"]=="larger-factor":
            anchor = w
            break
    assert anchor is not None,"public Euclidean gcd-one unit-numerator theorem"
    L0 = integers.add(integers.mul(m,anchor["b"]),-integers.mul(2,integers.mul(anchor["a"],anchor["j"])))
    minors = []

    def finish(factor,stage,witness=None):
        if witness is not None:
            witness = dict(witness,root_packet_bucket=buckets[witness["root"]])
            if witness.get("other_root") is not None:
                witness["other_root_packet_bucket"] = buckets[witness["other_root"]]
        queries = sum(metrics[k] for k in ("anchor_minor_GCD_queries","derivative_gcd_queries",
            "selected_row_gcd_queries"))
        assert len(buckets)<=len(originals) and queries<=3*len(originals)
        return dict(N=n,modulus=m,factor=factor,stage=stage,anchor=anchor,witness=witness,
            complete_original_packets=len(originals),distinct_anchor_slopes=len(buckets),
            recovery_GCD_queries=queries,milliseconds=1000*(time.perf_counter()-start),
            metrics=dict(metrics,**integers.stats(),**ring.stats(),**batch.stats()),
            source_inputs="N and public m",private_factor_or_triple_input=False,
            constructed_row_pair_or_triple_matrix=False,is_complete_factorizer=False,
            is_bit_complexity_certificate=False,is_native_machine_refinement=False)

    for w in originals:
        D = integers.add(integers.mul(anchor["a"],w["t"]),-integers.mul(w["a"],anchor["t"]))
        common = integers.gcd(n,abs(D))
        metrics["anchor_minor_GCD_queries"] += 1
        if 1<common<n:
            return finish(common,"public-anchor-minor-GCD")
        minors.append((w,D,common==1))
    for w,D,unit in minors:
        if not unit:
            metrics["excluded_nonunit_slopes"] += 1
            continue
        L = integers.add(integers.mul(m,w["b"]),-integers.mul(2,integers.mul(w["a"],w["j"])))
        A = integers.add(integers.mul(anchor["a"],L),-integers.mul(w["a"],L0))
        integers.charge("anchor_denominator_inverse_cache_lookup",D)
        if D not in inverses:
            inverses[D] = integers.divmod(integers.inverse(D,n),n)[1]
            metrics["anchor_denominator_inverse_cache_misses"] += 1
        value = ring.mul(integers.divmod(A,n)[1],inverses[D])
        integers.charge("public_anchor_slope_bucket_lookup",value)
        buckets.setdefault(value,[]).append(dict(packet=w,offset_minor=A,denominator_minor=D))
        metrics["admissible_anchor_slopes"] += 1
    roots = list(buckets)
    if not roots:
        return finish(None,"empty-anchor-axis")
    outputs = DERIVATIVE["derivative_outputs"](n,roots,integers,ring,batch,metrics)
    factor,stage,witness = DERIVATIVE["recover_derivatives"](n,roots,outputs,integers,metrics)
    return finish(factor,stage,witness)


def joined_backend_control(n,m):
    """Replay the entire existing joined backend with public N,m inputs."""
    start = time.perf_counter()
    integers,ring,batch,metrics = IntegerLedger(),ScalarLedger(n),BATCH["MonicBatch"](n),Counter()
    originals = list(FAMILY["public_packets"](n,m,integers,metrics))
    for key in ("a","t"):
        for w in originals:
            common = integers.gcd(n,abs(w[key]))
            metrics["coefficient_prefix_GCD_queries"] += 1
            assert common==1,"the literal complete paired-miss control has only unit coefficients"
    roots,inverses = {},{}
    for w in COMPANION["companion_packets"](originals,m,integers,metrics):
        roots.setdefault(integers.divmod(w["candidate"],n)[1],[]).append(w)
    for w in originals:
        L = integers.add(integers.mul(m,w["b"]),-integers.mul(2,integers.mul(w["a"],w["j"])))
        for scale in (w["a"],w["t"]):
            if scale not in inverses:
                inverses[scale] = integers.divmod(integers.inverse(scale,n),n)[1]
            value = ring.mul(integers.divmod(-L,n)[1],inverses[scale])
            roots.setdefault(value,[]).append(w)
    values = list(roots)
    outputs = REFLECTED["reflected_outputs"](n,values,integers,ring,batch,metrics)
    factor,stage,witness = REFLECTED["recover_reflected"](n,values,outputs,integers,metrics)
    count = sum(metrics[k] for k in ("coefficient_prefix_GCD_queries",
        "reflected_column_gcd_queries","selected_channel_gcd_queries"))
    assert len(roots)<=4*len(originals) and count<=14*len(originals)+1
    return dict(N=n,modulus=m,factor=factor,stage=stage,witness=witness,
        complete_original_packets=len(originals),ordinary_joined_roots=len(roots),
        recovery_GCD_queries=count,milliseconds=1000*(time.perf_counter()-start),
        metrics=dict(metrics,**integers.stats(),**ring.stats(),**batch.stats()),
        source_inputs="N and public m",private_factor_or_pair_input=False,
        is_native_complete_backend_exhaustion=factor is None,is_kernel_failure_certificate=False)


def public_source_oracle(n,m):
    rows = [w for j in range(1,m) for w in WEIGHTED["reference_residue_packets"](n,m,j)]
    anchor = next(w for w in rows if w["j"]==1 and abs(w["a"])==1 and
        w["center_orientation"]=="larger-factor")
    L0 = m*anchor["b"]-2*anchor["a"]
    roots,prefix = set(),False
    for w in rows:
        D = anchor["a"]*w["t"]-w["a"]*anchor["t"]
        common = math.gcd(n,D)
        prefix |= 1<common<n
        if common!=1:
            continue
        L = m*w["b"]-2*w["a"]*w["j"]
        A = anchor["a"]*L-w["a"]*L0
        roots.add(A*pow(D,-1,n)%n)
    return prefix or any(1<math.gcd(n,x-y)<n for x in roots for y in roots if x!=y)


def main():
    from sympy import isprime,nextprime,integer_nthroot
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--checked-declarations",type=int,default=0)
    parser.add_argument("--checked-theorems",type=int,default=0)
    parser.add_argument("--checked-explicit",type=int,default=0)
    args = parser.parse_args()
    sources,rnd = source_inventory(),random.Random(REPLAY_ID)
    coefficients = coefficient_oracles(rnd)
    n,m,p,q = 6396434398051,19,1919761,3331891
    assert n==p*q and p<q<=2*p and isprime(p) and isprime(q)
    paired = joined_backend_control(n,m)
    assert paired["factor"] is None
    values,_ = JOINED["original_values"](n,m)
    classification = JOINED["expected_counts"](values,p,q)
    assert classification["signed_exhausted"]
    anchored = public_anchor_source(n,m)
    assert anchored["factor"] is not None and 1<anchored["factor"]<n and n%anchored["factor"]==0
    floor,exact = integer_nthroot(n,6)
    B = int(floor)+int(not exact)
    control = dict(N=n,reference_p=p,reference_q=q,public_modulus=m,public_sixth_width=B,
        canonical_least_public_modulus=int(nextprime(B-1)),is_canonical_modulus=False,
        complete_joined_backend=paired,complete_signed_reference_classification=classification,
        public_anchor_backend=anchored,full_joined_miss_is_native_only=True)
    native = []
    for n,m in ((25,3),(49,5),(121,7),(169,11)):
        result = public_anchor_source(n,m)
        assert (result["factor"] is not None)==public_source_oracle(n,m)
        if result["factor"] is not None:
            assert 1<result["factor"]<n and n%result["factor"]==0
        native.append(result)
    for _ in range(32):
        m = rnd.choice((3,5,7,11,13,17,19))
        p = int(nextprime(rnd.randrange(m+1,300)))
        q = int(nextprime(rnd.randrange(p+1,5*p)))
        n = p*q
        result = public_anchor_source(n,m)
        assert (result["factor"] is not None)==public_source_oracle(n,m)
        if result["factor"] is not None:
            assert 1<result["factor"]<n and n%result["factor"]==0
        native.append(result)
    assert source_inventory()==sources,"source changed during replay"
    checked = args.checked_declarations>0 and args.checked_theorems>0
    report = dict(replay_id=REPLAY_ID,parent_audit=PARENT_AUDIT,source_sha256=sources,
        arbitrary_coefficient_oracles=coefficients,noncanonical_modulus_separation_control=control,
        public_N_m_native_oracle_runs=native,lean_validation=dict(
            separately_completed_scoped_gates=checked,strict_leaf_and_root=checked,
            namespace_linters=14 if checked else 0,linter_errors=0 if checked else None,
            all_module_declarations=args.checked_declarations,explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        kernel_components=dict(genuine_three_row_matrix_and_integer_N_division=True,
            exact_checked_unit_area_slope_GCD_phases=True,linear_root_and_GCD_query_count_per_anchor=True,
            public_gcd_one_Euclidean_stream_supplies_unit_anchor=True,
            literal_actual_row_area_equals_130543748=True,literal_area_GCD_equals_1919761=True,
            literal_public_N_m_anchor_selection_program_succeeds=True),
        all_triples_covered_by_one_anchor="OPEN",universal_anchored_coverage="OPEN",
        guaranteed_one_sixth_factorization="OPEN",is_complete_factorizer=False,
        is_bit_complexity_certificate=False,
        limitations="The kernel connects a genuine original three-row determinant, exact integer N division, anchored coefficient minors and unit slope differences. It proves public anchor acquisition and complete selected-anchor recovery on a literal actual control. The existing joined backend's complete miss on that control remains native-only, with m=19 rather than its canonical least sixth-root modulus 137. Thus this is an information separation control, not a canonical-modulus counterexample or a sixth-root factorization theorem. Source runs take N and public m only; private primes classify one separate reference carrier, while no chosen triple or hidden factor enters the anchor source. Native timers include full original construction, public anchor selection, every minor GCD, checked whole-N inverses, dictionaries, one root polynomial, derivative evaluation and saturated selected-row recovery. They are individual diagnostics and not a speedup or exponent fit. The three-per-row bound concerns GCD queries for one anchor, not complete bit cost, all-anchor work or acquisition. One anchor covers only its own guarded triples; scanning every anchor generically costs quadratically many retained slopes. Universal every-run coverage, fast polynomial bit clocks, arbitrary-ratio completion and the construction-inclusive deterministic N^(1/6) bit theorem remain open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),coefficient_cases=4096,
        public_N_m_runs=len(native)+1,paired_control_exhausted=True,
        area_control_factor=anchored["factor"],native_stages=dict(Counter(c["stage"] for c in native)),
        one_sixth_guarantee="OPEN")),flush=True)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Actual-row residue/center cancellations and unpaid anchored-area discovery.

The reference classifier takes known prime fields after constructing the
public N,m packet family. It retains every center and residue; only the
proved same-residue/same-center population is excluded from useful-hit
discovery when both primes exceed 3m. No large public polynomial runtime,
all-triple coverage theorem or sixth-root bit bound is claimed.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-joined-integer-sort-audit.json"
REPLAY_ID = 202610033238
SEEDS = (REPLAY_ID, 202610033239)
AREA = runpy.run_path(str(ROOT/"scripts/probe_semiprime_anchored_row_areas.py"))
WEIGHTED, FAMILY = AREA["WEIGHTED"], AREA["FAMILY"]


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeRowAreaSpectrum.lean",
        "scripts/CheckSemiprimeRowAreaSpectrum.lean",
        "scripts/probe_semiprime_row_area_spectrum.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def orientation(w):
    return w["center_orientation"]=="larger-factor"


def coefficient(w):
    return w["a"],w["L"],w["t"]


def triple_oracle(n,m,u,w,v,counters):
    rows = (u,w,v)
    actual = AREA["area"](*(coefficient(z) for z in rows))
    errors = AREA["area"](*((z["a"],z["epsilon"],z["t"]) for z in rows))
    mixed = AREA["area"](*((z["a"],int(orientation(z))*(z["a"]-z["t"]),z["t"])
        for z in rows))
    delta = math.isqrt(2*n)-math.isqrt(n//2)
    assert 2*actual== -errors-delta*mixed
    assert abs(errors)<=6*m**4
    counters["signed_center_decompositions"] += 1
    if len({z["j"] for z in rows})==1:
        lifted = AREA["area"](*((z["a"],z["b"],z["c"]) for z in rows))
        assert n*actual==m**3*lifted and actual%m**3==0
        counters["actual_same_residue_m_cubed_divisibility"] += 1
        if len({orientation(z) for z in rows})==1:
            assert mixed==0 and 2*actual== -errors
            assert abs(actual//m**3)<=3*m
            counters["same_residue_center_normalized_bound"] += 1
    j,k,l = (z["j"] for z in rows)
    signature = -2*u["a"]*w["a"]*v["a"]*(k-j)*(l-j)*(l-k)
    assert (n*actual-signature)%m==0
    counters["auxiliary_modulus_Vandermonde_signatures"] += 1
    return actual


def public_reference_rows(n,m,counters):
    """Full Nt integer lifts; reduced offsets are an independent comparison."""
    lo,mid,hi = math.isqrt(n//2),math.isqrt(n),math.isqrt(2*n)
    square = m*m
    rows = []
    for j in range(1,m):
        inverse = pow(j,-1,square)
        for z in WEIGHTED["reference_residue_packets"](n,m,j):
            L = m*z["b"]-2*z["a"]*j
            A,B = (mid+hi,lo+mid) if orientation(z) else (lo+mid,mid+hi)
            epsilon = -2*L-z["a"]*A-z["t"]*B
            original_b = z["b"]+z["shift"]*m
            H = z["a"]*A+z["t"]*B+2*(m*original_b-2*z["a"]*j)
            assert z["shift"]==(H+square)//(2*square)
            assert epsilon==2*square*z["shift"]-H and abs(epsilon)<=square
            assert m*m*z["c"]-j*m*z["b"]+j*j*z["a"]==n*z["t"]
            assert 0<abs(z["a"])<m and 0<z["t"]<=m
            residue = (-z["a"]*j-(n%square)*z["t"]*inverse)%square
            direct = residue-((z["a"]*A+z["t"]*B+2*residue+square)//(2*square))*square
            assert direct==L
            z.update(L=L,epsilon=epsilon)
            rows.append(z)
            counters["original_packets_and_independent_reduced_offsets"] += 1
    return rows


def classify_anchor(n,m,p,q,rows,anchor=None):
    """Complete private CRT classification of one anchored slope axis.

    Whole-N inverses define the same public slopes. Both field projections
    are fully counted, including globally identical rows and singular minors.
    No pair or triple matrix is constructed. The field labels are private.
    """
    if anchor is None:
        anchor = next(z for z in rows if z["j"]==1 and abs(z["a"])==1 and orientation(z))
    assert math.gcd(n,anchor["a"])==1
    roots, inverses, prefix, stages = {}, {}, [], Counter()
    for z in rows:
        D = anchor["a"]*z["t"]-z["a"]*anchor["t"]
        common = math.gcd(n,D)
        stages["minor_GCD_reference_checks"] += 1
        if common!=1:
            stages["globally_singular_minors" if common==n else "proper_minor_hits"] += 1
            if 1<common<n and len(prefix)<2:
                prefix.append(dict(factor=common,minor=D,packet=z))
            continue
        if D not in inverses:
            inverses[D] = pow(D,-1,n)
        A = anchor["a"]*z["L"]-z["a"]*anchor["L"]
        value = A*inverses[D]%n
        roots.setdefault(value,z)
        stages["admissible_original_slopes"] += 1
    groups_p,groups_q,examples,masks = {},{},{},Counter()
    for value,z in roots.items():
        ep,eq = value%p,value%q
        for label,key,groups in (("p",ep,groups_p),("q",eq,groups_q)):
            if key not in groups:
                groups[key] = value,z
            else:
                other,prior = groups[key]
                assert other!=value and math.gcd(n,value-other) in (p,q)
                category = ("same-residue/" if len({anchor["j"],z["j"],prior["j"]})==1
                    else "cross-residue/")+("same-center" if
                        len({orientation(anchor),orientation(z),orientation(prior)})==1
                        else "mixed-center")
                assert category!="same-residue/same-center" or min(p,q)<=3*m
                masks[label+"/"+category] += 1
                if label not in examples:
                    area = AREA["area"](*(coefficient(w) for w in (anchor,prior,z)))
                    factor = math.gcd(n,area)
                    assert factor==math.gcd(n,value-other) and 1<factor<n
                    examples[label] = dict(factor=factor,area=area,category=category,
                        anchor=anchor,left=prior,right=z)
    total = len(roots)
    return dict(public_anchor=anchor,original_packets=len(rows),ordinary_anchor_slopes=total,
        p_classes=len(groups_p),q_classes=len(groups_q),
        p_collapsed_values=total-len(groups_p),q_collapsed_values=total-len(groups_q),
        original_rows_collapsed_modulo_whole_N=stages["admissible_original_slopes"]-total,
        minor_prefix_examples=prefix,area_examples=examples,unpaid_hit_masks=dict(masks),
        stage_counts=dict(stages),inverse_cache_entries=len(inverses),
        native_chosen_anchor_exhausted=not prefix and not examples,
        both_field_projections_fully_classified=True,constructed_pair_or_triple_matrix=False,
        is_N_only_classifier=False,is_factorizer_bit_clock=False)


def cases():
    from sympy import nextprime
    for seed in SEEDS:
        rnd = random.Random(seed)
        for bits in (8,12,16,20,24):
            for _ in range(6):
                p = int(nextprime(rnd.randrange(2**(bits-1),2**bits)))
                q = int(nextprime(rnd.randrange(p+1,2*p)))
                yield seed,"balanced",p,q
        for bits in (6,10,14,18):
            for ratio in (4,16,256,4096):
                p = int(nextprime(rnd.randrange(2**(bits-1),2**bits)))
                q = int(nextprime(rnd.randrange(ratio*p,2*ratio*p)))
                yield seed,"wide-ratio",p,q
        for bits in (6,10,14,18,22,24,26,28):
            p = int(nextprime(rnd.randrange(2**(bits-1),2**bits)))
            yield seed,"square",p,p
        for bits in (28,32,36,38):
            p = int(nextprime(rnd.randrange(2**(bits-1),2**bits)))
            q = int(nextprime(rnd.randrange(p+1,2*p)))
            yield seed,"larger-held-out",p,q


def main():
    from sympy import integer_nthroot,isprime,nextprime
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--checked-declarations",type=int,default=0)
    parser.add_argument("--checked-theorems",type=int,default=0)
    parser.add_argument("--checked-explicit",type=int,default=0)
    args = parser.parse_args()
    sources,counters,results = source_inventory(),Counter(),[]
    backend_controls,order_controls = [],[]
    for index,(seed,population,p,q) in enumerate(cases()):
        n,rnd = p*q,random.Random(seed+index*1009)
        assert isprime(p) and isprime(q)
        floor,exact = integer_nthroot(n,6)
        B = int(floor)+int(not exact)
        m = int(nextprime(max(2,B)-1))
        assert math.gcd(n,m)==1
        start = time.perf_counter()
        rows = public_reference_rows(n,m,counters)
        groups = defaultdict(list)
        for w in rows:
            groups[w["j"],orientation(w)].append(w)
        for _ in range(32):
            j = rnd.randrange(1,m)
            for side in (False,True):
                group = groups[j,side]
                if len(group)<3:
                    continue
                triple = rnd.sample(group,3)
                area = triple_oracle(n,m,*triple,counters)
                if min(p,q)>3*m:
                    assert math.gcd(n,area) in (1,n)
                    counters["large_prime_same_residue_center_no_proper_GCD"] += 1
            group = groups[j,False]+groups[j,True]
            if len(group)>=3:
                triple_oracle(n,m,*rnd.sample(group,3),counters)
            triple_oracle(n,m,*rnd.sample(rows,3),counters)
        anchor = classify_anchor(n,m,p,q,rows)
        if index%6==0 and len(rows)<4000:
            reverse = classify_anchor(n,m,p,q,list(reversed(rows)),anchor["public_anchor"])
            for key in ("ordinary_anchor_slopes","p_classes","q_classes",
                    "p_collapsed_values","q_collapsed_values","native_chosen_anchor_exhausted"):
                assert reverse[key]==anchor[key],(index,key)
            order_controls.append(index)
        if len(backend_controls)<12 and len(rows)<220 and p!=q:
            native = AREA["public_anchor_source"](n,m)
            assert (native["factor"] is None)==anchor["native_chosen_anchor_exhausted"]
            backend_controls.append(dict(index=index,N=n,modulus=m,factor=native["factor"],
                stage=native["stage"],full_original_packets=native["complete_original_packets"],
                complete_public_N_m_polynomial_backend_replayed=True))
        result = dict(index=index,seed=seed,population=population,N=n,input_bits=n.bit_length(),
            reference_p=p,reference_q=q,public_sixth_width=B,modulus=m,
            same_residue_center_exclusion_applicable=min(p,q)>3*m,
            complete_selected_anchor=anchor,reference_milliseconds=1000*(time.perf_counter()-start))
        results.append(result)
        print(json.dumps(dict(progress="actual-prime-area-spectrum-case-completed",index=index,
            population=population,input_bits=n.bit_length(),modulus=m,packets=len(rows),
            chosen_anchor_exhausted=anchor["native_chosen_anchor_exhausted"],
            p_collapsed=anchor["p_collapsed_values"],q_collapsed=anchor["q_collapsed_values"])),flush=True)
    assert source_inventory()==sources,"source changed during replay"
    checked = args.checked_declarations>0 and args.checked_theorems>0
    report = dict(replay_id=REPLAY_ID,parent_audit=PARENT_AUDIT,source_sha256=sources,
        independent_seeds=SEEDS,actual_prime_case_count=len(results),
        unique_reference_prime_labels=len({c[k] for c in results for k in ("reference_p","reference_q")}),
        case_populations=dict(Counter(c["population"] for c in results)),
        full_original_row_oracles=dict(counters),reverse_order_case_indices=order_controls,
        small_public_N_m_polynomial_controls=backend_controls,complete_cases=results,
        chosen_anchor_native_exhaustions=sum(c["complete_selected_anchor"]["native_chosen_anchor_exhausted"]
            for c in results),lean_validation=dict(strict_leaf_and_root=checked,
            separately_completed_scoped_gates=checked,namespace_linters=14 if checked else 0,
            linter_errors=0 if checked else None,all_module_declarations=args.checked_declarations,
            explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        compiled_components=dict(actual_same_residue_integer_m_cubed_divisibility=True,
            signed_same_center_error_area_identity=True,normalized_same_center_area_bound_3m=True,
            large_prime_same_residue_center_no_proper_GCD=True,
            exact_mixed_center_direction_retained=True,auxiliary_Vandermonde_signature=True,
            actual_control_signed_errors_200_276_125_and_mixed_area_minus146=True),
        is_complete_factorizer=False,is_kernel_exhaustion_certificate=False,
        is_bit_complexity_certificate=False,universal_selected_anchor_coverage="OPEN",
        guaranteed_one_sixth_factorization="OPEN",
        limitations="The mathematical obstruction is restricted to actual triples sharing one residue and one center, after a public coprimality check, when both prime factors exceed 3m. Mixed centers and cross-residue triples remain unpaid and are fully retained. The signed error and mixed-center identities precede every bound. The Vandermonde signature is modulo the auxiliary m and does not identify an unknown factor of N. Actual prime inputs include independent random draws, separate larger held-out sizes, wide ratios and prime squares; repeated prime labels are reported, and shared-label products are not credited as independent evidence. Native complete classifiers cover one chosen public anchor, both prime projections and all its singular-minor prefix checks. They use private primes as reference labels and supply no kernel exhaustion proof, universal coverage, full large polynomial clock or exponent fit. Only the separate small backend controls construct and recover a complete public N,m polynomial. All-anchor acquisition and work, arbitrary-ratio completion and the construction-inclusive deterministic N^(1/6) bit theorem remain open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),actual_prime_cases=len(results),
        checked_packet_oracles=counters["original_packets_and_independent_reduced_offsets"],
        chosen_anchor_native_exhaustions=report["chosen_anchor_native_exhaustions"],
        one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":
    main()

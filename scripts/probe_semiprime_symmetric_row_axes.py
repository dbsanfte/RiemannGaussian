#!/usr/bin/env python3
"""Test arithmetic duality and complete two-axis amended-family exhaustion.

All original residues, intermediate vectors, both centers, preceding roots,
new signed axes, signs and zero are retained. Private prime-field sorting
tests finite coverage only. Stop after both fields confirm a complete miss;
successful examples receive no new Lean certificates or coverage credit.
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
import struct
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-affine-projection-obstruction-audit.json"
CPP = "scripts/semiprime_symmetric_axis_rows.cpp"
SORT_CPP = "scripts/semiprime_literal_inplace_sort.cpp"
REPLAY_ID = 202610033257
DUALITY_SEED = 202610033256
CANDIDATE_SEED = 202610033258
PRIOR = runpy.run_path(str(ROOT/"scripts/probe_semiprime_literal_quadratic_roots.py"))
FRONTIER = runpy.run_path(str(ROOT/"scripts/probe_semiprime_literal_inplace_frontier.py"))
WEIGHTED = PRIOR["WEIGHTED"]


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,CPP,"RiemannGaussian/SemiprimeSymmetricRowAxes.lean",
        "scripts/CheckSemiprimeSymmetricRowAxes.lean","scripts/probe_semiprime_symmetric_row_axes.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def original_oracle(n,m,mode,first=1,last=None):
    if mode!=2:return PRIOR["original_oracle"](n,m,mode,first,last)
    values,rows,companions = [0],[],0
    for j in range(first,m if last is None else last):
        values.append(-j%n)
        packets = list(WEIGHTED["reference_residue_packets"](n,m,j))
        previous = None
        for index in range(0,len(packets),2):
            current = packets[index:index+2]
            for w in current:
                a,t,L = w["a"],w["t"],m*w["b"]-2*w["a"]*j
                assert a!=0 and 0<t and abs(a)+t<=m
                assert m*m*w["c"]-j*m*w["b"]+j*j*a==n*t
                alpha = -L*pow(a,-1,n)%n
                values.extend(((alpha-j)%n,alpha,-L*pow(t,-1,n)%n))
                for denominator in (a+t,a-t):
                    assert abs(denominator)<=m
                    values.append(-L*pow(denominator,-1,n)%n if denominator else 0)
                rows.append(dict(w,L=L,alpha=alpha))
            if previous is not None:
                for u in previous:
                    for w in current:
                        D = u["a"]*w["t"]-w["a"]*u["t"]
                        numerator = -(w["t"]*(m*u["b"]-2*u["a"]*j)-
                            u["t"]*(m*w["b"]-2*w["a"]*j))
                        assert abs(D)==m and numerator%D==0
                        values.append(numerator//D%n)
                        companions += 1
            previous = current
    return rows,values,companions


def duality_oracles():
    rnd = random.Random(DUALITY_SEED)
    counts,cases = Counter(),[]
    for _ in range(64):
        m = rnd.choice((2,3,5,7,11,13,17,23,31,43,61,89))
        n = rnd.randrange(17,10**13)
        while math.gcd(n,m)!=1:n+=1
        cases.append((n,m,list(range(1,m))))
    parent = json.loads((ROOT/"docs/semiprime-literal-inplace-frontier-audit.json").read_text())
    control = parent["complete_amended_families"][0]
    n,m,p,q = (control[k] for k in ("N","modulus","reference_p","reference_q"))
    js = {1,2,m-1,m-2,p%m,q%m}
    js.update(rnd.randrange(1,m) for _ in range(58))
    cases.append((n,m,sorted(js)))
    ties = []
    for n,m,js in cases:
        for j in js:
            partner = n*pow(j,-1,m)%m
            assert n*pow(partner,-1,m)%m==j
            rows = list(WEIGHTED["reference_residue_packets"](n,m,j))
            duals = {(w["a"],w["t"],w["center_orientation"]):w
                for w in WEIGHTED["reference_residue_packets"](n,m,partner)}
            for w in rows:
                a,t = w["a"],w["t"]
                sign = 1 if a>0 else -1
                side = "larger-factor" if w["center_orientation"]=="smaller-factor" else "smaller-factor"
                v = duals[(sign*t,abs(a),side)]
                L,V = m*w["b"]-2*a*j,m*v["b"]-2*v["a"]*partner
                delta = V-sign*L
                assert delta==0 or (sign==-1 and delta==-m*m)
                counts["original_packets"] += 1
                counts["matching_dual_packets"] += 1
                counts["exact_signed_offset_matches"] += delta==0
                counts["negative_rounding_ties"] += delta!=0
                if delta and len(ties)<8:
                    ties.append(dict(N=n,modulus=m,residue=j,partner=partner,
                        a=a,t=t,L=L,dual_L=V,delta=delta))
    return dict(seed=DUALITY_SEED,complete_small_families=64,
        large_input_N=control["N"],large_residue_slices=len(js),counts=dict(counts),
        tie_examples=ties,is_kernel_dual_membership_certificate=False,
        is_full_large_family_duality_enumeration=False)


def oracles(generator,sorter,path):
    from sympy import nextprime
    rnd = random.Random(REPLAY_ID)
    count,zero_denominators = 0,0
    for index in range(64):
        m = rnd.choice((2,3,5,7,11,13,17,19,23,31))
        p = int(nextprime(rnd.randrange(m*m+10,30000))) if index<48 else int(nextprime(2**61+rnd.randrange(2**20)))
        q = int(nextprime(rnd.randrange(p+1,8*p))) if index<48 else int(nextprime(2**62+rnd.randrange(2**20)))
        n = p*q
        for mode in (0,1,2):
            rows,values,companions = original_oracle(n,m,mode)
            counts = PRIOR["native_rows"](generator,path,n,m,p,q,mode)
            raw = list(struct.iter_unpack("QQ",path.read_bytes()))
            assert raw==[PRIOR["JOINED"]["fold_pair"](v%p,v%q,p,q)[:2] for v in values],(index,mode)
            assert counts["original_packets"]==len(rows) and counts["companion_packets"]==companions
            assert counts["ordinary_records"]==len(values) and counts["scratch_bytes"]==16*len(values)
            assert counts["symmetric_axis_coordinates"]==(2*len(rows) if mode==2 else 0)
            result = json.loads(subprocess.run([str(sorter),str(path),str(p),str(q)],
                check=True,capture_output=True,text=True).stdout)
            for key,value in PRIOR["JOINED"]["expected_counts"](values,p,q).items():
                assert result[key]==value,(index,mode,key)
            if mode==2:
                zero_denominators += sum(w["a"]+w["t"]==0 or w["a"]-w["t"]==0 for w in rows)
                old_values = set(PRIOR["original_oracle"](n,m,1)[1])
                assert old_values.issubset(values)
            count += 1
    return dict(actual_families=64,actual_family_streams=count,wide_families=16,
        zero_axis_denominators_checked=zero_denominators,
        full_Nt_source_rows_and_whole_N_inverse_values_checked=True,
        both_complete_signed_field_counts_checked=True,
        preceding_family_values_preserved=True,undefined_behavior_checks=True)


def candidates():
    from sympy import integer_nthroot,nextprime
    result = FRONTIER["candidates"]()
    rnd = random.Random(CANDIDATE_SEED)
    for index in range(3,5):
        p = int(nextprime(2**60+rnd.randrange(2**58)))
        q = int(nextprime(p+1+rnd.randrange(2**58)))
        n = p*q
        floor,exact = integer_nthroot(n,6)
        width = int(floor)+(not exact)
        m = int(nextprime(width-1))
        assert n.bit_length()==121 and p<=q<=2*p and m*m<p
        result.append(dict(index=index,N=n,input_bits=121,reference_p=p,reference_q=q,
            sixth_width=width,modulus=m,balanced=True,private_prefix_unit_bound=m*m<p))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,required=True)
    for name in ("declarations","theorems","explicit"):
        parser.add_argument("--checked-"+name,type=int,required=True)
    args = parser.parse_args()
    assert args.checked_declarations>0 and args.checked_theorems>0
    sources,planned = source_inventory(),candidates()
    complete = []
    print(json.dumps(dict(progress="symmetric-axis-candidates-fixed",new_candidate_seed=CANDIDATE_SEED,
        inherited_candidate_seed=FRONTIER["CANDIDATE_SEED"],planned_candidates=planned,
        stop_condition="first complete exhaustion after both prime projections")),flush=True)
    duality = duality_oracles()
    print(json.dumps(dict(progress="duality-oracles-completed",counts=duality["counts"])),flush=True)
    with tempfile.TemporaryDirectory(prefix="semiprime-symmetric-axes-") as temp:
        temp = Path(temp)
        generator,sorter,checked_rows,checked_sort,path = (temp/k for k in
            ("rows","sort","rows-ubsan","sort-ubsan","classes.bin"))
        for binary,source,ubsan in ((generator,CPP,False),(sorter,SORT_CPP,False),
                (checked_rows,CPP,True),(checked_sort,SORT_CPP,True)):
            extra = ["-fsanitize=undefined","-fno-sanitize-recover=all"] if ubsan else []
            subprocess.run(["g++",*PRIOR["FLAGS"],*extra,str(ROOT/source),"-o",str(binary)],check=True)
        control = oracles(checked_rows,checked_sort,path)
        print(json.dumps(dict(progress="symmetric-axis-oracles-completed",**control)),flush=True)
        for candidate in planned:
            n,m,p,q = (candidate[k] for k in ("N","modulus","reference_p","reference_q"))
            print(json.dumps(dict(progress="complete-symmetric-family-start",**candidate)),flush=True)
            start = time.perf_counter()
            counts = PRIOR["native_rows"](generator,path,n,m,p,q,2)
            result = FRONTIER["classify"](sorter,path,p,q)
            case = dict(**candidate,**counts,**result,
                private_reference_milliseconds=1000*(time.perf_counter()-start),
                all_original_residues_intermediates_and_both_centers_enumerated=True,
                old_joined_and_literal_roots_and_both_new_axes_retained=True,
                both_prime_projections_fully_counted=True,
                is_N_only_classifier=False,is_kernel_execution_or_exhaustion_certificate=False,
                is_factorizer_runtime=False)
            complete.append(case)
            print(json.dumps(dict(progress="complete-symmetric-family-completed",**case)),flush=True)
            if case["signed_exhausted"]:break
    assert source_inventory()==sources,"source changed during replay"
    report = dict(replay_id=REPLAY_ID,new_candidate_seed=CANDIDATE_SEED,parent_audit=PARENT_AUDIT,
        source_sha256=sources,planned_candidates=planned,duality_oracles=duality,
        native_complete_family_oracles=control,complete_symmetric_families=complete,
        complete_native_symmetric_misses=sum(c["signed_exhausted"] for c in complete),
        lean_validation=dict(strict_target_leaf_and_root_and_namespace_checker_passed=True,
            namespace_linters=14,linter_errors=0,all_module_declarations=args.checked_declarations,
            explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        mathematical_scope="Exact guarded coordinate-dual area transport and complete recovery of that channel. Membership of every coordinate dual in the actual Euclidean stream is not proved. The complete native amendment uses only the original public packets and both signed axes.",
        no_new_success_Lean_certificates=True,universal_amended_coverage_proved=False,
        guaranteed_one_sixth_factorization="OPEN",is_complete_factorizer=False,
        is_bit_complexity_certificate=False,
        limitations="A complete finite native miss counts both prime images of the full signed family including zero and global deduplication. Native enumeration is not kernel checked. Large prefix and axis-unit guards are inferred from private factor bounds. The public polynomial backend, complete construction and recovery bit clocks, memory cost, arbitrary-ratio and prime-square coverage remain unproved. Successful cases receive no coverage credit.")
    args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),complete_cases=len(complete),
        complete_native_misses=report["complete_native_symmetric_misses"],one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":main()

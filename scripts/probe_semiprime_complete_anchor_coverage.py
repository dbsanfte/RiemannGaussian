#!/usr/bin/env python3
"""Complete private anchored classifiers on the canonical joined-family miss.

The chosen residues 1 and 2 are public. A unit-numerator row is selected by
each original Euclidean stream; no private triple selects the anchor. The
native generator uses residue-batch inversions and preserves whole-N slope
duplicates. Private prime fields classify the axes; their timers are not
N-only polynomial factorization clocks or sixth-root bit certificates.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import subprocess
import tempfile
import time

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-area-anchor-frontier-audit.json"
JOINED_AUDIT = "docs/semiprime-joined-second-integer-sort-audit.json"
CPP = "scripts/semiprime_anchored_coverage_rows.cpp"
REPLAY_ID = 202610033244
FRONTIER = runpy.run_path(str(ROOT/"scripts/probe_semiprime_area_anchor_frontier.py"))
PRIOR = FRONTIER["PRIOR"]
FLAGS = ("-std=c++20","-O3","-Wall","-Wextra","-Werror")
DTYPE = np.dtype([("p",np.uint64),("q",np.uint64)])


def source_inventory():
    paths = set()
    for name in (PARENT_AUDIT,JOINED_AUDIT):
        parent = json.loads((ROOT/name).read_text())
        for path,digest in parent["source_sha256"].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
        paths.update(parent["source_sha256"])
        paths.add(name)
    paths.update((CPP,"scripts/probe_semiprime_complete_anchor_coverage.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def run_native(binary,path,n,m,p,q,j,generate_only=False,slice_limits=None):
    small,large = math.isqrt(n//2)+math.isqrt(n),math.isqrt(n)+math.isqrt(2*n)
    args = [str(binary),str(m),str(n%(m*m)),str(small),str(large),str(p),str(q),str(j),str(path)]
    if generate_only:
        args.append("generate-only")
        if slice_limits is not None:
            args.extend(map(str,slice_limits))
    result = subprocess.run(args,check=True,stdout=subprocess.PIPE,text=True)
    return json.loads(result.stdout)


def original_oracle(n,m,p,q,j,first=1,last=None):
    last = m if last is None else last
    rows = [z for k in range(first,last) for z in PRIOR["WEIGHTED"]["reference_residue_packets"](n,m,k)]
    anchor = next(z for z in PRIOR["WEIGHTED"]["reference_residue_packets"](n,m,j)
        if abs(z["a"])==1 and PRIOR["orientation"](z))
    L0 = m*anchor["b"]-2*anchor["a"]*j
    values,records,singular = [],[],0
    for z in rows:
        D = anchor["a"]*z["t"]-z["a"]*anchor["t"]
        common = math.gcd(n,D)
        if D==0:
            assert common==n
            singular += 1
            continue
        assert common==1
        L = m*z["b"]-2*z["a"]*z["j"]
        value = (anchor["a"]*L-z["a"]*L0)*pow(D,-1,n)%n
        records.append((value%p,value%q))
        values.append(value)
    roots = set(values)
    return records,dict(original_packets=len(rows),anchor_residue=j,
        anchor_numerator=anchor["a"],anchor_denominator=anchor["t"],
        globally_singular_minor_packets=singular,proper_minor_prefix_hits=0,
        ordinary_records=len(records),scratch_bytes=len(records)*16,
        ordinary_whole_values=len(roots),p_classes=len({v%p for v in roots}),
        q_classes=len({v%q for v in roots}))


def main():
    from sympy import isprime,nextprime
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    sources,rnd = source_inventory(),random.Random(REPLAY_ID)
    compiler = subprocess.run(["g++","--version"],check=True,capture_output=True,
        text=True).stdout.splitlines()[0]
    joined = json.loads((ROOT/JOINED_AUDIT).read_text())["completed_case"]
    n,p,q,m = (joined[k] for k in ("N","reference_p","reference_q","modulus"))
    assert joined["signed_exhausted"] and isprime(p) and isprime(q) and isprime(m)
    assert n==p*q and m*m<min(p,q)
    oracles,controls,complete = [],[],[]
    with tempfile.TemporaryDirectory(prefix="semiprime-complete-anchor-") as temp:
        temp = Path(temp)
        binary,sanitized,path = temp/"anchor",temp/"anchor-ubsan",temp/"classes.bin"
        subprocess.run(["g++",*FLAGS,str(ROOT/CPP),"-o",str(binary)],check=True)
        subprocess.run(["g++",*FLAGS,"-fsanitize=undefined","-fno-sanitize-recover=all",
            str(ROOT/CPP),"-o",str(sanitized)],check=True)
        for index in range(64):
            modulus = rnd.choice((3,5,7,11,13,17,19,23,31))
            if index<48:
                a = int(nextprime(rnd.randrange(modulus*modulus+10,20000)))
                b = int(nextprime(rnd.randrange(a+1,4*a)))
            else:
                a = int(nextprime(2**61+rnd.randrange(2**20)))
                b = int(nextprime(2**62+rnd.randrange(2**20)))
            public_anchor = rnd.randrange(1,modulus)
            records,expected = original_oracle(a*b,modulus,a,b,public_anchor)
            metadata = run_native(sanitized,path,a*b,modulus,a,b,public_anchor,generate_only=True)
            raw = np.fromfile(path,dtype=DTYPE)
            assert [(int(z["p"]),int(z["q"])) for z in raw]==records,index
            assert metadata["chosen_anchor_exhausted"] is None
            actual = run_native(sanitized,path,a*b,modulus,a,b,public_anchor)
            for key,value in expected.items():assert actual[key]==value,(index,key,actual,expected)
            assert actual["chosen_anchor_exhausted"]==(expected["ordinary_whole_values"]==
                expected["p_classes"]==expected["q_classes"])
            oracles.append(dict(index=index,modulus=modulus,public_anchor_residue=public_anchor,
                original_packets=expected["original_packets"],wide_field_case=index>=48))
        # Full-N integer lifts for sampled residues at the literal large input.
        for j in (1,2,3,17,127,p%m,q%m,m-1):
            if j==0:continue
            records,expected = original_oracle(n,m,p,q,1,first=j,last=j+1)
            actual = run_native(sanitized,path,n,m,p,q,1,generate_only=True,slice_limits=(j,j+1))
            raw = np.fromfile(path,dtype=DTYPE)
            assert [(int(z["p"]),int(z["q"])) for z in raw]==records,j
            assert actual["original_packets"]==expected["original_packets"]
        print(json.dumps(dict(progress="native-anchor-oracles-completed",whole_N_families=64,
            literal_large_residue_slices=8)),flush=True)
        parent = json.loads((ROOT/PARENT_AUDIT).read_text())
        for case in parent["complete_cases"]:
            old = case["complete_selected_anchor"]
            if not old["native_chosen_anchor_exhausted"]:continue
            nn,mm,pp,qq = (case[k] for k in ("N","modulus","reference_p","reference_q"))
            assert mm*mm<min(pp,qq)
            actual = run_native(binary,path,nn,mm,pp,qq,1)
            for new,prior in (("original_packets","original_packets"),
                    ("ordinary_whole_values","ordinary_anchor_slopes"),("p_classes","p_classes"),
                    ("q_classes","q_classes"),("p_collapsed_values","p_collapsed_values"),
                    ("q_collapsed_values","q_collapsed_values")):
                assert actual[new]==old[prior],(case["index"],new)
            assert actual["chosen_anchor_exhausted"]
            controls.append(dict(N=nn,modulus=mm,**actual))
        print(json.dumps(dict(progress="native-anchor-large-held-out-controls-completed",cases=len(controls))),flush=True)
        for j in (1,2):
            print(json.dumps(dict(progress="complete-literal-canonical-anchor-start",N=n,
                reference_p=p,reference_q=q,modulus=m,public_anchor_residue=j)),flush=True)
            start = time.perf_counter()
            actual = run_native(binary,path,n,m,p,q,j)
            case = dict(N=n,input_bits=n.bit_length(),reference_p=p,reference_q=q,modulus=m,
                public_anchor_residue=j,**actual,
                reference_classification_milliseconds=1000*(time.perf_counter()-start),
                all_original_residues_intermediates_and_centers_enumerated=True,
                all_nonzero_minor_units_inferred_from_checked_bound_m_squared=True,
                is_N_only_classifier=False,is_factorizer_runtime_measurement=False,
                is_kernel_exhaustion_certificate=False)
            complete.append(case)
            print(json.dumps(dict(progress="complete-literal-canonical-anchor-completed",**case)),flush=True)
    assert source_inventory()==sources,"source changed during replay"
    report = dict(replay_id=REPLAY_ID,parent_audits=[PARENT_AUDIT,JOINED_AUDIT],source_sha256=sources,
        compiler=compiler,compiler_flags=FLAGS,whole_N_integer_lift_and_classification_oracles=oracles,
        literal_large_integer_lift_residue_slices=8,finite_undefined_behavior_checks=True,
        complete_previous_anchor_miss_controls=controls,complete_canonical_cases=complete,
        deterministic_public_anchor_residues=[1,2],joined_pair_family_miss_preserved=True,
        original_NumPy_replay_preserved=True,is_complete_factorizer=False,
        is_N_only_algorithm=False,is_bit_complexity_certificate=False,
        is_kernel_execution_or_exhaustion_certificate=False,
        guaranteed_one_sixth_factorization="OPEN",
        limitations="The native generator uses the exact reduced-offset fork, all Euclidean intermediates and both original public centers. Batch inversions normalize nonzero minors in separate private fields; every zero minor remains a globally singular prefix entry. The input restriction m²<min(p,q), together with the checked joint coefficient envelope, certifies that no nonzero minor has a proper prefix GCD. This reference backend infers prefix units from those private bounds and does not execute every whole-N GCD. Whole-N ordinary slope duplicates are counted before complete independent P/Q projections; no reflected sign quotient is used. Whole-N integer lift/individual inverse oracles cover 64 families, 16 wide-field cases and eight slices at the literal large input. The three earlier complete chosen-anchor misses are independently replayed. Public residues 1 and 2 select unit-numerator anchors without a private factor or chosen triple, but the classifiers use private prime labels and do not construct large public root polynomials. Finite successes or failures on this fixed schedule neither prove universal coverage nor exhaust all anchors/triples. Timers include this bounded native reference generation and sorting only, not factorizer bit clocks, all-ratio acquisition, native Lean refinement or the complete deterministic N^(1/6) theorem.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),whole_N_oracles=64,
        complete_canonical_axes=len(complete),canonical_native_exhaustions=sum(c["chosen_anchor_exhausted"] for c in complete),
        one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":
    main()

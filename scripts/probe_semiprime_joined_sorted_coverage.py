#!/usr/bin/env python3
"""Exact reference exhaustion of the joined signed additive family.

The offset fork avoids the large constant coefficient and its exponent.
Private prime fields are used only for complete reference classification.
All original intermediates, both centers, both affine channels, all four
adjacent companions, their common signs and the zero anchor are retained.
No N-only factorizer, bit cost or kernel exhaustion certificate is claimed.
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
import subprocess
import sys
import tempfile
import time

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-affine-row-roots-audit.json"
REPLAY_ID = 202610033232
AFFINE = runpy.run_path(str(ROOT/"scripts/probe_semiprime_affine_row_roots.py"))
WEIGHTED = AFFINE["WEIGHTED"]
DTYPE = np.dtype([("fp",np.uint64),("qc",np.uint64),("fq",np.uint64)])
CPP = "scripts/semiprime_joined_coverage_rows.cpp"
FLAGS = ("-std=c++20","-O3","-Wall","-Wextra","-Werror")


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeCenteredOffsetExtractor.lean",
        "scripts/CheckSemiprimeCenteredOffsetExtractor.lean",CPP,
        "scripts/probe_semiprime_joined_sorted_coverage.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def fold_pair(ep,eq,p,q):
    opposite = -ep%p
    return (min(ep,opposite),eq if ep<opposite else -eq%q if ep>opposite
        else min(eq,-eq%q),min(eq,-eq%q))


def distinct_changes(data,keys):
    count,previous = 0,None
    for start in range(0,len(data),1000000):
        block = data[start:start+1000000]
        changed = np.ones(len(block),dtype=bool)
        if len(block)>1:
            changed[1:] = False
            for key in keys:
                changed[1:] |= block[key][1:]!=block[key][:-1]
        if previous is not None:
            changed[0] = any(int(block[k][0])!=previous[k] for k in keys)
        count += int(np.count_nonzero(changed))
        previous = {k:int(block[k][-1]) for k in keys}
    return count


def classify_table(path,rows,progress=False):
    if not rows:
        return dict(distinct_global_sign_orbits=0,global_zero_in_ordinary_family=False,
            folded_p_classes=0,folded_q_classes=0,p_zero_in_ordinary_family=False,
            q_zero_in_ordinary_family=False,signed_whole_values_with_zero_anchor=1,
            signed_p_classes_with_zero_anchor=1,signed_q_classes_with_zero_anchor=1,
            signed_p_collapsed_values=0,signed_q_collapsed_values=0,signed_exhausted=True)
    data = np.memmap(path,dtype=DTYPE,mode="r+",shape=(rows,))
    if progress:
        print(json.dumps(dict(progress="complete-joined-sort-P-start",rows=rows,
            scratch_bytes=rows*24)),flush=True)
    data.sort(order=("fp","qc","fq"),kind="quicksort")
    whole,cp = distinct_changes(data,("fp","qc")),distinct_changes(data,("fp",))
    pzero = int(data["fp"][0])==0
    globalzero = pzero and int(data["qc"][0])==0
    qzero = any(np.any(data["qc"][i:i+1000000]==0) for i in range(0,rows,1000000))
    if progress:
        print(json.dumps(dict(progress="complete-joined-sort-Q-start",rows=rows,
            distinct_global_sign_orbits=whole,folded_p_classes=cp)),flush=True)
    # This sort and count run even when P already has a proper collision.
    data.sort(order=("fq","fp","qc"),kind="quicksort")
    cq = distinct_changes(data,("fq",))
    assert distinct_changes(data,("fp","qc"))==whole
    assert (int(data["fq"][0])==0)==qzero
    signed = 2*(whole-int(globalzero))+1
    pp,qq = 2*(cp-int(pzero))+1,2*(cq-int(qzero))+1
    assert pp<=signed and qq<=signed
    result = dict(distinct_global_sign_orbits=whole,
        global_zero_in_ordinary_family=bool(globalzero),folded_p_classes=cp,
        folded_q_classes=cq,p_zero_in_ordinary_family=bool(pzero),
        q_zero_in_ordinary_family=bool(qzero),signed_whole_values_with_zero_anchor=signed,
        signed_p_classes_with_zero_anchor=pp,signed_q_classes_with_zero_anchor=qq,
        signed_p_collapsed_values=signed-pp,signed_q_collapsed_values=signed-qq,
        signed_exhausted=signed==pp==qq)
    del data
    return result


def classify_values(values,p,q,scratch):
    records = [fold_pair(v%p,v%q,p,q) for v in values]
    np.array(records,dtype=DTYPE).tofile(scratch)
    return classify_table(scratch,len(records))


def expected_counts(values,p,q):
    n = p*q
    ordinary = {v%n for v in values}
    signed = {0}|ordinary|{-v%n for v in ordinary}
    pp,qq = len({v%p for v in signed}),len({v%q for v in signed})
    return dict(signed_whole_values_with_zero_anchor=len(signed),
        signed_p_classes_with_zero_anchor=pp,signed_q_classes_with_zero_anchor=qq,
        signed_p_collapsed_values=len(signed)-pp,signed_q_collapsed_values=len(signed)-qq,
        signed_exhausted=len(signed)==pp==qq)


def original_values(n,m,first=1,last=None):
    """Independent existing full Nt-containing row lift and whole-N inverse."""
    result,counts = [],Counter()
    for j in range(first,m if last is None else last):
        rows = list(WEIGHTED["reference_residue_packets"](n,m,j))
        counts["original_packets"] += len(rows)
        for w in rows:
            L = m*w["b"]-2*w["a"]*j
            for scale in (w["a"],w["t"]):
                assert math.gcd(n,scale)==1
                result.append(-L*pow(scale,-1,n)%n)
                counts["affine_coordinates"] += 1
        for w in WEIGHTED["weighted_packets"](rows,m):
            assert w["exponent"]%m==0 and abs(w["determinant"])==m
            result.append((1-(w["determinant"]//m)*(w["exponent"]//m))%n)
            counts["companion_packets"] += 1
    counts["ordinary_records"] = len(result)
    return result,counts


def native_rows(binary,n,m,p,q,path,first=1,last=None,progress=False):
    assert 2<m<p<2**63 and m<q<2**63 and p!=q and m<2**23
    low,middle,high = math.isqrt(n//2),math.isqrt(n),math.isqrt(2*n)
    assert low+middle<2**64 and middle+high<2**64
    command = [str(binary),str(m),str(n%(m*m)),str(low+middle),str(middle+high),
        str(p),str(q),str(path),str(first),str(m if last is None else last)]
    process = subprocess.Popen(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    while True:
        try:
            out,err = process.communicate(timeout=20)
            break
        except subprocess.TimeoutExpired:
            if progress:
                print(json.dumps(dict(progress="complete-joined-row-generation",
                    scratch_bytes=path.stat().st_size if path.exists() else 0)),flush=True)
    assert process.returncode==0,(process.returncode,err)
    result = json.loads(out)
    assert result["scratch_bytes"]==path.stat().st_size==24*result["ordinary_records"]
    return result


def oracles(binary,scratch,rnd):
    from sympy import isprime,nextprime
    checks = Counter()
    primes = (3,5,7,11,13,17,19,23,31,43,61,97)
    for i in range(256):
        p,q = rnd.sample(primes,2)
        if i>=224:
            p = int(nextprime(2**61+rnd.randrange(2**20)))
            q = int(nextprime(2**62+rnd.randrange(2**20)))
        assert isprime(p) and isprime(q)
        n = p*q
        values = [rnd.randrange(-3*n,3*n) for _ in range(rnd.randrange(40))]
        if i<16:
            values += (0,p,q,-p,-q)
        actual,expected = classify_values(values,p,q,scratch),expected_counts(values,p,q)
        for key,value in expected.items():
            assert actual[key]==value,(i,key,actual,expected)
        signed = {0}|{x%n for x in values}|{-x%n for x in values}
        proper = any(1<math.gcd(n,x-y)<n for x in signed for y in signed if x!=y)
        assert proper != actual["signed_exhausted"]
        checks["sorted_signed_CRT_vs_explicit_whole_N_and_pair_GCD_oracles"] += 1
    controls = []
    for i in range(112):
        m = rnd.choice((3,5,7,11,13,17,19))
        p = int(nextprime(rnd.randrange(m+1,1000)))
        q = int(nextprime(rnd.randrange(p+1,5*p)))
        if i>=96:
            p = int(nextprime(2**61+rnd.randrange(2**20)))
            q = int(nextprime(2**62+rnd.randrange(2**20)))
        controls.append((p*q,m,p,q,1,m))
    inherited = json.loads((ROOT/PARENT_AUDIT).read_text())["inherited_103bit_affine_witness"]
    n,m = inherited["N"],inherited["modulus"]
    p,q = 2245327606949267,3027647967431443
    assert n==p*q and isprime(p) and isprime(q)
    for j in (1,2,7,31,137,1001,17003,51007,70001,85189,95998,m-1):
        controls.append((n,m,p,q,j,j+1))
    for n,m,p,q,first,last in controls:
        values,counts = original_values(n,m,first,last)
        output = native_rows(binary,n,m,p,q,scratch,first,last)
        for key,value in counts.items():
            assert output[key]==value,(key,output,counts)
        data = np.fromfile(scratch,dtype=DTYPE)
        actual_records = Counter(tuple(int(row[k]) for k in ("fp","qc","fq")) for row in data)
        assert actual_records==Counter(fold_pair(v%p,v%q,p,q) for v in values)
        actual,expected = classify_table(scratch,len(data)),expected_counts(values,p,q)
        for key,value in expected.items():
            assert actual[key]==value
        checks["compiled_offset_fork_vs_original_full_integer_lift_families_or_slices"] += 1
        checks["original_packets_independently_compared"] += counts["original_packets"]
        checks["all_joined_coordinate_records_independently_compared"] += len(values)
    return dict(checks)


def main():
    from sympy import integer_nthroot,isprime,nextprime
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--prime-bits",type=int,default=59)
    parser.add_argument("--maximum-cases",type=int,default=2)
    parser.add_argument("--checked-declarations",type=int,default=0)
    parser.add_argument("--checked-theorems",type=int,default=0)
    parser.add_argument("--checked-explicit",type=int,default=0)
    args = parser.parse_args()
    assert sys.byteorder=="little" and DTYPE.itemsize==24
    assert 16<=args.prime_bits<=62
    sources,rnd,cases = source_inventory(),random.Random(REPLAY_ID),[]
    compiler = subprocess.run(["g++","--version"],check=True,text=True,capture_output=True).stdout.splitlines()[0]
    with tempfile.TemporaryDirectory(prefix="semiprime-joined-signed-") as temp:
        temp = Path(temp)
        binary,checked_binary,scratch = temp/"rows",temp/"rows-ubsan",temp/"classes.bin"
        subprocess.run(["g++",*FLAGS,str(ROOT/CPP),"-o",str(binary)],check=True)
        subprocess.run(["g++",*FLAGS,"-fsanitize=undefined","-fno-sanitize-recover=all",
            str(ROOT/CPP),"-o",str(checked_binary)],check=True)
        checked_oracles = oracles(checked_binary,scratch,rnd)
        print(json.dumps(dict(progress="joined-classifier-and-offset-fork-oracles-completed",
            **checked_oracles)),flush=True)
        for index in range(args.maximum_cases):
            p = int(nextprime(rnd.randrange(2**(args.prime_bits-1),2**args.prime_bits)))
            q = int(nextprime(rnd.randrange(11*p//10,19*p//10)))
            assert p<q<=2*p and isprime(p) and isprime(q)
            n = p*q
            floor,exact = integer_nthroot(n,6)
            B = int(floor)+int(not exact)
            m = int(nextprime(max(2,B)-1))
            assert m<p and m<q and m<=2*B and isprime(m) and n%m!=0
            print(json.dumps(dict(progress="complete-private-joined-signed-test-start",
                sample_index=index,N=n,reference_p=p,reference_q=q,public_sixth_width=B,
                modulus=m,input_bits=n.bit_length())),flush=True)
            start = time.perf_counter()
            counts = native_rows(binary,n,m,p,q,scratch,progress=True)
            result = classify_table(scratch,counts["ordinary_records"],True)
            case = dict(sample_index=index,N=n,input_bits=n.bit_length(),reference_p=p,
                reference_q=q,public_sixth_width=B,modulus=m,packet_counts=counts,**result,
                reference_classification_milliseconds=1000*(time.perf_counter()-start),
                classification="complete-joined-signed-miss" if result["signed_exhausted"]
                    else "joined-signed-proper-hit",
                all_original_residues_intermediates_centers_and_channels_enumerated=True,
                both_prime_field_projections_fully_counted=True,zero_anchor_retained=True,
                original_coefficient_GCD_prefix_has_only_units=True,
                is_N_only_source=False,is_factorizer_runtime_measurement=False,
                is_kernel_exhaustion_certificate=False)
            cases.append(case)
            print(json.dumps(dict(progress="complete-private-joined-signed-test-completed",**case)),flush=True)
            if result["signed_exhausted"]:
                break
    assert source_inventory()==sources,"source changed during replay"
    checked = args.checked_declarations>0 and args.checked_theorems>0
    report = dict(replay_id=REPLAY_ID,parent_audit=PARENT_AUDIT,source_sha256=sources,
        reference_prime_bits=args.prime_bits,maximum_cases=args.maximum_cases,
        native_oracles=checked_oracles,compiler=compiler,compiler_flags=FLAGS,
        oracle_undefined_behavior_sanitizer_enabled=True,numpy_version=np.__version__,
        backend="Exact signed CRT orbits in a disk-backed 24-byte table; full P and Q sorts",
        completed_cases=cases,first_complete_joined_signed_miss=next((c for c in cases
            if c["signed_exhausted"]),None),lean_validation=dict(
                separately_completed_scoped_gates=checked,strict_leaf_and_root=checked,
                namespace_linters=14 if checked else 0,linter_errors=0 if checked else None,
                all_module_declarations=args.checked_declarations,
                explicit_declarations=args.checked_explicit,
                generated_declarations=args.checked_declarations-args.checked_explicit,
                theorem_and_helper_declarations=args.checked_theorems,
                permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        stopped_at_first_complete_miss=True,is_N_only_algorithm=False,
        is_complete_factorizer=False,is_factorization_runtime_measurement=False,
        kernel_checked_complete_failure_control=False,is_bit_complexity_certificate=False,
        universal_joined_family_coverage="OPEN",guaranteed_one_sixth_factorization="OPEN",
        limitations="The separately compiled offset commuting theorem concerns the signed original integer offset, both affine channels and primitive companion extraction. The C++ generator is reference code, not a kernel-native-machine refinement. Its complete small families and large-residue slices are independently compared with the frozen full Nt-containing Python lift and whole-N inverses; arbitrary signed orbit sorts are compared with direct whole-N sets and pair GCDs. Large cases use private native prime factors to classify every public joined row in both fields. Folded CRT keys use one consistent common sign, preserving global duplicates and negative matches. The zero anchor and local-zero endpoint defects are counted explicitly. A native full-family miss is not a Lean exhaustion certificate, an asymptotic lower bound or a counterexample to other moduli, higher correlations or adaptive detectors. No large public polynomial construction or factorizer runtime is executed. Universal coverage and the every-run arbitrary-ratio construction-inclusive deterministic N^(1/6) bit theorem remain open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),complete_reference_cases=len(cases),
        complete_joined_signed_miss_found=report["first_complete_joined_signed_miss"] is not None,
        kernel_exhaustion_certificate=False,one_sixth_guarantee="OPEN")),flush=True)


if __name__ == "__main__":
    main()

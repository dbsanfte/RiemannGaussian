#!/usr/bin/env python3
"""Independent full signed additive classification using native integer sorting.

The NumPy replay is left intact. This separately generated table classifies
the same frozen first 118-bit input. Private fields label reference classes;
no public factorizer, bit theorem or kernel exhaustion proof is asserted.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import random
import runpy
import subprocess
import tempfile
import time

import numpy as np

ROOT=Path(__file__).resolve().parents[1]
PARENT_AUDIT="docs/semiprime-anchored-row-areas-audit.json"
REPLAY_ID=202610033236
SORT_CPP="scripts/semiprime_joined_coverage_sort.cpp"
JOINED=runpy.run_path(str(ROOT/"scripts/probe_semiprime_joined_sorted_coverage.py"))


def source_inventory():
    parent=json.loads((ROOT/PARENT_AUDIT).read_text())
    for p,h in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,p
    paths=set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,SORT_CPP,"scripts/probe_semiprime_joined_integer_sort.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def classify(binary,path,p,q):
    result=subprocess.run([str(binary),str(path),str(p),str(q)],check=True,
        capture_output=True,text=True)
    return json.loads(result.stdout)


def main():
    from sympy import integer_nthroot,isprime,nextprime
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    sources,rnd=source_inventory(),random.Random(REPLAY_ID)
    compiler=subprocess.run(["g++","--version"],check=True,capture_output=True,text=True).stdout.splitlines()[0]
    with tempfile.TemporaryDirectory(prefix="semiprime-joined-integer-") as temp:
        temp=Path(temp)
        generator,sorter,sanitized,path=temp/"rows",temp/"sort",temp/"sort-ubsan",temp/"classes.bin"
        subprocess.run(["g++",*JOINED["FLAGS"],str(ROOT/JOINED["CPP"]),"-o",str(generator)],check=True)
        subprocess.run(["g++",*JOINED["FLAGS"],str(ROOT/SORT_CPP),"-o",str(sorter)],check=True)
        subprocess.run(["g++",*JOINED["FLAGS"],"-fsanitize=undefined","-fno-sanitize-recover=all",
            str(ROOT/SORT_CPP),"-o",str(sanitized)],check=True)
        for index in range(512):
            p,q=rnd.sample((3,5,7,11,13,17,19,23,31,43,61,97),2)
            if index>=480:
                p=int(nextprime(2**61+rnd.randrange(2**20)))
                q=int(nextprime(2**62+rnd.randrange(2**20)))
            n=p*q
            values=[rnd.randrange(-3*n,3*n) for _ in range(rnd.randrange(60))]
            if index<32:
                values += (0,p,q,-p,-q)
            records=[JOINED["fold_pair"](v%p,v%q,p,q) for v in values]
            np.array(records,dtype=JOINED["DTYPE"]).tofile(path)
            actual=classify(sanitized,path,p,q)
            expected=JOINED["expected_counts"](values,p,q)
            for k,v in expected.items():
                assert actual[k]==v,(index,k,actual,expected)
            numpy=JOINED["classify_table"](path,len(records))
            assert actual==numpy,(index,actual,numpy)
        print(json.dumps(dict(progress="native-integer-sort-oracles-completed",checks=512)),flush=True)
        n=287924677746770498819378760678822563
        p,q,m=423196074159314927,680357629306313869,812627
        floor,exact=integer_nthroot(n,6)
        B=int(floor)+int(not exact)
        assert n==p*q and p<q<=2*p and isprime(p) and isprime(q)
        assert m==int(nextprime(B-1)) and isprime(m) and m<p and m<q and n%m!=0
        print(json.dumps(dict(progress="independent-complete-joined-test-start",N=n,
            reference_p=p,reference_q=q,modulus=m,public_sixth_width=B)),flush=True)
        start=time.perf_counter()
        counts=JOINED["native_rows"](generator,n,m,p,q,path,progress=True)
        # Send sorter progress to the log while retaining its JSON stdout.
        process=subprocess.run([str(sorter),str(path),str(p),str(q)],check=True,
            stdout=subprocess.PIPE,text=True)
        classification=json.loads(process.stdout)
        case=dict(N=n,input_bits=n.bit_length(),reference_p=p,reference_q=q,modulus=m,
            public_sixth_width=B,packet_counts=counts,**classification,
            reference_classification_milliseconds=1000*(time.perf_counter()-start),
            original_coefficient_GCD_prefix_has_only_units=True,
            all_original_residues_intermediates_centers_and_channels_enumerated=True,
            both_prime_field_projections_fully_counted=True,zero_anchor_retained=True,
            is_N_only_source=False,is_factorization_runtime_measurement=False,
            is_kernel_exhaustion_certificate=False)
    assert source_inventory()==sources,"source changed during replay"
    report=dict(replay_id=REPLAY_ID,parent_audit=PARENT_AUDIT,source_sha256=sources,
        compiler=compiler,compiler_flags=JOINED["FLAGS"],
        independent_signed_sort_oracles=512,oracle_undefined_behavior_sanitizer_enabled=True,
        backend="Native lexicographic integer sort of global signed CRT orbits; scalar Q sort",
        same_first_118bit_input_as_original_NumPy_replay=True,original_NumPy_process_preserved=True,
        completed_case=case,found_complete_joined_signed_miss=case["signed_exhausted"],
        is_complete_factorizer=False,is_N_only_algorithm=False,
        is_factorization_runtime_measurement=False,kernel_checked_failure_control=False,
        is_bit_complexity_certificate=False,universal_joined_coverage="OPEN",
        guaranteed_one_sixth_factorization="OPEN",
        limitations="The same frozen complete row generator is compiled independently and emits a fresh table; the original running NumPy sort is neither interrupted nor read while mutating. All signed CRT and zero-anchor statistics match explicit whole-N sets and the previous NumPy classifier on 512 arbitrary lists, including 32 full-width field cases. The native integer sorter has undefined-behavior sanitization in the finite oracles. The new full reference table includes every original intermediate and both centers, both affine coordinates and all four adjacent companion combinations. Q classes are counted independently from one representative of every global signed orbit; global duplicates and opposite-sign matches remain exact. Private native primes supply reference labels only. No large N-only polynomial source, factorizer runtime, bit refinement or Lean full-family exhaustion certificate is produced. A native miss concerns this fixed canonical family and its pair/endpoint observables, not other moduli, anchors, higher correlations or all factoring algorithms. Every-run arbitrary-ratio construction-inclusive deterministic N^(1/6) bit factorization remains open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),complete_joined_signed_miss_found=case["signed_exhausted"],
        signed_whole=case["signed_whole_values_with_zero_anchor"],
        p_collapsed=case["signed_p_collapsed_values"],q_collapsed=case["signed_q_collapsed_values"],
        one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":
    main()

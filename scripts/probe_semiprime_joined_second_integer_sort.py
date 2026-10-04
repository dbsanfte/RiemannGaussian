#!/usr/bin/env python3
"""Independently classify the second frozen 119-bit joined-family input.

Reuse the pinned generator and the already validated integer sorter on a
fresh complete table. Preserve the ongoing original NumPy replay. Private
prime-field labels are reference data, not public factorizer inputs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import runpy
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-joined-integer-sort-audit.json"
REPLAY_ID = 202610033240
PRIOR = runpy.run_path(str(ROOT/"scripts/probe_semiprime_joined_integer_sort.py"))
JOINED = PRIOR["JOINED"]


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"scripts/probe_semiprime_joined_second_integer_sort.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def main():
    from sympy import integer_nthroot,isprime,nextprime
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    sources = source_inventory()
    n = 344480927244364494083113546915969253
    p,q,m = 526706927522612147,654027713029416199,837271
    floor,exact = integer_nthroot(n,6)
    B = int(floor)+int(not exact)
    assert n==p*q and p<q<=2*p and isprime(p) and isprime(q)
    assert m==int(nextprime(B-1)) and isprime(m) and m<p and m<q and n%m!=0
    compiler = subprocess.run(["g++","--version"],check=True,capture_output=True,
        text=True).stdout.splitlines()[0]
    with tempfile.TemporaryDirectory(prefix="semiprime-joined-second-") as temp:
        temp = Path(temp)
        generator,sorter,path = temp/"rows",temp/"sort",temp/"classes.bin"
        subprocess.run(["g++",*JOINED["FLAGS"],str(ROOT/JOINED["CPP"]),"-o",str(generator)],check=True)
        subprocess.run(["g++",*JOINED["FLAGS"],str(ROOT/PRIOR["SORT_CPP"]),"-o",str(sorter)],check=True)
        print(json.dumps(dict(progress="independent-second-complete-joined-test-start",N=n,
            reference_p=p,reference_q=q,modulus=m,public_sixth_width=B)),flush=True)
        start = time.perf_counter()
        counts = JOINED["native_rows"](generator,n,m,p,q,path,progress=True)
        process = subprocess.run([str(sorter),str(path),str(p),str(q)],check=True,
            stdout=subprocess.PIPE,text=True)
        classification = json.loads(process.stdout)
        case = dict(N=n,input_bits=n.bit_length(),reference_p=p,reference_q=q,modulus=m,
            public_sixth_width=B,packet_counts=counts,**classification,
            reference_classification_milliseconds=1000*(time.perf_counter()-start),
            original_coefficient_GCD_prefix_has_only_units=True,
            all_original_residues_intermediates_centers_and_channels_enumerated=True,
            both_prime_field_projections_fully_counted=True,zero_anchor_retained=True,
            is_N_only_source=False,is_factorization_runtime_measurement=False,
            is_kernel_exhaustion_certificate=False)
    assert source_inventory()==sources,"source changed during replay"
    report = dict(replay_id=REPLAY_ID,parent_audit=PARENT_AUDIT,source_sha256=sources,
        compiler=compiler,compiler_flags=JOINED["FLAGS"],
        unchanged_backend_oracles_in_parent=512,backend_oracles_repeated=False,
        original_NumPy_process_preserved=True,same_second_frozen_input_as_NumPy_replay=True,
        completed_case=case,found_complete_joined_signed_miss=case["signed_exhausted"],
        is_complete_factorizer=False,is_N_only_algorithm=False,
        is_factorization_runtime_measurement=False,is_bit_complexity_certificate=False,
        kernel_checked_failure_control=False,universal_joined_coverage="OPEN",
        guaranteed_one_sixth_factorization="OPEN",
        limitations="This is a new complete input to the unchanged pinned generator and integer sorter. The parent's 512 exact signed-set and NumPy oracles, including undefined-behavior sanitization and 32 wide-field cases, are retained without repeating routine implementation tests. A fresh table retains every residue, intermediate, both centers, both affine channels and all four adjacent companions. Both prime projections are completely counted, with consistent whole-N signs, global duplicates and a zero anchor. Private primes are reference labels only. No public large root polynomial, factorizer bit clock, Lean execution refinement or kernel full-family exhaustion certificate is produced. A finite miss concerns this fixed canonical family and its pair/endpoint observables; other moduli, anchors and higher correlations remain distinct questions. Guaranteed every-run arbitrary-ratio construction-inclusive deterministic N^(1/6) bit factorization remains open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),complete_joined_signed_miss_found=case["signed_exhausted"],
        signed_whole=case["signed_whole_values_with_zero_anchor"],
        p_collapsed=case["signed_p_collapsed_values"],q_collapsed=case["signed_q_collapsed_values"],
        one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":
    main()

#!/usr/bin/env python3
"""Confirm the first amended-family miss through the frozen 24-byte path.

This independent complete sorter keeps its P table and a separate Q vector.
The primary frontier sorter compacts and transforms a 16-byte table in place.
The same finite negative result must agree in both complete projections.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import random
import runpy
import struct
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-literal-inplace-frontier-audit.json"
REPLAY_ID = 202610033254
PRIOR = runpy.run_path(str(ROOT/"scripts/probe_semiprime_literal_quadratic_roots.py"))
CPP = "scripts/semiprime_literal_quotient_rows.cpp"
SORT_CPP = "scripts/semiprime_joined_coverage_sort.cpp"


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"scripts/probe_semiprime_literal_frontier_confirmation.py",CPP,SORT_CPP))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    sources = source_inventory()
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    misses = [c for c in parent["complete_amended_families"] if c["signed_exhausted"]]
    assert misses,"no complete amended-family miss to confirm"
    case = misses[0]
    n,m,p,q = (case[k] for k in ("N","modulus","reference_p","reference_q"))
    rnd = random.Random(REPLAY_ID)
    residues = sorted({1,2,3,m-3,m-2,m-1,p%m,q%m,*[rnd.randrange(1,m) for _ in range(32)]}-{0})
    print(json.dumps(dict(progress="independent-amended-miss-confirmation-start",N=n,modulus=m,
        original_inplace_sign_orbits=case["distinct_global_sign_orbits"])),flush=True)
    compared_packets,compared_values = 0,0
    with tempfile.TemporaryDirectory(prefix="semiprime-literal-confirmation-") as temp:
        temp = Path(temp)
        generator,sorter,path = (temp/k for k in ("rows","sort","classes.bin"))
        for binary,source in ((generator,CPP),(sorter,SORT_CPP)):
            subprocess.run(["g++",*PRIOR["FLAGS"],str(ROOT/source),"-o",str(binary)],check=True)
        for j in residues:
            rows,values,companions = PRIOR["original_oracle"](n,m,1,first=j,last=j+1)
            counts = PRIOR["native_rows"](generator,path,n,m,p,q,1,first=j,last=j+1)
            raw = list(struct.iter_unpack("QQQ",path.read_bytes()))
            assert raw==[PRIOR["JOINED"]["fold_pair"](v%p,v%q,p,q) for v in values],j
            assert counts["original_packets"]==len(rows) and counts["companion_packets"]==companions
            compared_packets += len(rows)
            compared_values += len(values)
        print(json.dumps(dict(progress="independent-full-Nt-miss-slices-checked",residues=len(residues),
            original_packets=compared_packets,scalar_values=compared_values)),flush=True)
        start = time.perf_counter()
        counts = PRIOR["native_rows"](generator,path,n,m,p,q,1)
        result = json.loads(subprocess.run([str(sorter),str(path),str(p),str(q)],check=True,
            stdout=subprocess.PIPE,text=True).stdout)
        elapsed = 1000*(time.perf_counter()-start)
        for key in PRIOR["JOINED"]["expected_counts"]([0],p,q):assert result[key]==case[key],key
        for key in ("original_packets","companion_packets","literal_shifted_coordinates",
                "known_residue_coordinates","affine_coordinates","ordinary_records"):
            assert counts[key]==case[key],key
        assert counts["scratch_bytes"]==24*case["ordinary_records"]
        assert result["signed_exhausted"]
    assert source_inventory()==sources,"source changed during confirmation"
    report = dict(replay_id=REPLAY_ID,parent_audit=PARENT_AUDIT,source_sha256=sources,
        canonical_full_Nt_slice_checks=dict(residues=residues,original_packets=compared_packets,
            scalar_values=compared_values,all_centers_and_intermediates_compared=True),
        independent_complete_confirmation=dict(N=n,modulus=m,reference_p=p,reference_q=q,
            **counts,**result,private_reference_milliseconds=elapsed,
            agrees_with_primary_complete_counts=True,both_prime_projections_fully_counted=True,
            original_frozen_generator_used=True,original_frozen_separate_Q_sorter_used=True),
        is_kernel_execution_or_exhaustion_certificate=False,is_N_only_classifier=False,
        is_complete_factorizer=False,is_bit_complexity_certificate=False,
        universal_amended_coverage_proved=False,guaranteed_one_sixth_factorization="OPEN",
        limitations="Two distinct complete native encodings and sorting implementations agree on a signed exhaustion of the full amended family. New canonical full Nt-containing residue slices check the original offsets and stream membership. This is a corroborated finite native failure, with prime labels and prefix unit conditions checked by external arithmetic. No large kernel enumeration or execution/exhaustion certificate is supplied, and no complete public prefix/polynomial bit factorizer is timed. Older positive controls remain valid; they do not imply universal coverage.")
    if args.output:args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),confirmed_complete_native_miss=True,
        signed_classes=result["signed_whole_values_with_zero_anchor"],one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":main()

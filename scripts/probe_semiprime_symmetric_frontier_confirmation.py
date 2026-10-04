#!/usr/bin/env python3
"""Confirm the first larger symmetric-family miss through the frozen in-place sorter.

The primary larger-input classifier counts separate bucketed Q labels. This
replay regenerates the full scalar stream and instead transforms whole-N
sign pairs in place. Every global, P and Q count must agree. Private native
exhaustion is not a Lean certificate or an N-only factorizer bit clock.
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
PARENT_AUDIT = "docs/semiprime-symmetric-bucket-frontier-audit.json"
REPLAY_ID = 202610033264
CURRENT = runpy.run_path(str(ROOT/"scripts/probe_semiprime_symmetric_row_axes.py"))
BUCKET = runpy.run_path(str(ROOT/"scripts/probe_semiprime_symmetric_bucket_confirmation.py"))
PRIOR,FRONTIER = CURRENT["PRIOR"],CURRENT["FRONTIER"]
SORT_CPP = "scripts/semiprime_literal_inplace_sort.cpp"


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,SORT_CPP,"scripts/probe_semiprime_symmetric_frontier_confirmation.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,required=True)
    args = parser.parse_args()
    sources = source_inventory()
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    misses = [c for c in parent["complete_symmetric_families"] if c["signed_exhausted"]]
    assert misses,"no saved complete symmetric-family miss to confirm"
    case = misses[0]
    n,m,p,q = (case[k] for k in ("N","modulus","reference_p","reference_q"))
    with tempfile.TemporaryDirectory(prefix="semiprime-symmetric-inplace-confirmation-") as temp:
        temp = Path(temp)
        generator,sorter,path = (temp/k for k in ("rows","sort","classes.bin"))
        BUCKET["compile_binary"](generator,CURRENT["CPP"])
        BUCKET["compile_binary"](sorter,SORT_CPP)
        rnd = random.Random(REPLAY_ID)
        residues = sorted({1,2,3,m-3,m-2,m-1,p%m,q%m,*[rnd.randrange(1,m) for _ in range(40)]}-{0})
        packets,scalars = 0,0
        for j in residues:
            rows,values,companions = CURRENT["original_oracle"](n,m,2,first=j,last=j+1)
            counts = PRIOR["native_rows"](generator,path,n,m,p,q,2,first=j,last=j+1)
            raw = list(struct.iter_unpack("QQ",path.read_bytes()))
            assert raw==[PRIOR["JOINED"]["fold_pair"](v%p,v%q,p,q)[:2] for v in values],j
            assert counts["original_packets"]==len(rows) and counts["companion_packets"]==companions
            result = json.loads(subprocess.run([str(sorter),str(path),str(p),str(q)],
                check=True,capture_output=True,text=True).stdout)
            FRONTIER["check_classes"](result,values,p,q)
            packets += len(rows); scalars += len(values)
        print(json.dumps(dict(progress="complete-inplace-symmetric-miss-confirmation-start",N=n,modulus=m,
            full_Nt_residue_slices_checked=len(residues),original_packets=packets,scalar_values=scalars)),flush=True)
        start = time.perf_counter()
        counts = PRIOR["native_rows"](generator,path,n,m,p,q,2)
        result = FRONTIER["classify"](sorter,path,p,q)
        elapsed = 1000*(time.perf_counter()-start)
        for key in PRIOR["JOINED"]["expected_counts"]([0],p,q):assert result[key]==case[key],key
        for key in ("original_packets","companion_packets","mode","literal_shifted_coordinates",
                "known_residue_coordinates","symmetric_axis_coordinates","affine_coordinates",
                "ordinary_records","scratch_bytes"):
            assert counts[key]==case[key],key
        assert result["signed_exhausted"]
    assert source_inventory()==sources,"source changed during confirmation"
    report = dict(replay_id=REPLAY_ID,parent_audit=PARENT_AUDIT,source_sha256=sources,
        canonical_full_Nt_slice_checks=dict(residues=residues,original_packets=packets,scalar_values=scalars,
            all_original_intermediates_and_both_centers_checked=True),
        complete_inplace_confirmation=dict(N=n,modulus=m,reference_p=p,reference_q=q,**counts,**result,
            private_reference_milliseconds=elapsed,all_primary_population_counts_agree=True,
            both_factor_projections_fully_counted=True),
        different_complete_classifiers_agree=True,same_frozen_original_packet_generator=True,
        no_new_success_Lean_certificates=True,is_kernel_execution_or_exhaustion_certificate=False,
        is_N_only_factorizer=False,is_bit_complexity_certificate=False,
        universal_symmetric_family_coverage_proved=False,guaranteed_one_sixth_factorization="OPEN",
        limitations="The complete finite miss is corroborated by bucketed separate-Q-label counting and by whole-N in-place tuple transformation. Both use the frozen packet generator; fresh full-Nt slices independently check stream values. Private factor bounds discharge large prefix/unit guards externally. No large Lean exhaustion or complete public construction/acquisition/recovery/memory bit clock is supplied.")
    args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),confirmed_complete_native_miss=True,
        signed_classes=result["signed_whole_values_with_zero_anchor"],one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":main()

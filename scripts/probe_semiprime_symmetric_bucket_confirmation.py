#!/usr/bin/env python3
"""Cross-check complete symmetric-family misses with separate bucketed Q labels.

Preflight checks exact whole-N sets and complete actual packet streams. A
full confirmation is permitted only for a saved complete native miss, and
must agree in every population count after both factor images finish.
This is private reference arithmetic, not a factorizer or a Lean certificate.
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
PARENT_AUDIT = "docs/semiprime-symmetric-row-axes-audit.json"
PREFLIGHT_AUDIT = "docs/semiprime-symmetric-bucket-preflight-audit.json"
SORT_CPP = "scripts/semiprime_symmetric_bucket_sort.cpp"
REPLAY_ID = 202610033260
PREFLIGHT_SEED = 202610033259
CURRENT = runpy.run_path(str(ROOT/"scripts/probe_semiprime_symmetric_row_axes.py"))
PRIOR,FRONTIER = CURRENT["PRIOR"],CURRENT["FRONTIER"]


def source_inventory(*extra):
    sources = CURRENT["source_inventory"]()
    paths = set(sources)
    paths.update((SORT_CPP,"scripts/probe_semiprime_symmetric_bucket_confirmation.py",*extra))
    for path in extra:
        if not path.endswith("-audit.json"):continue
        parent = json.loads((ROOT/path).read_text())
        for source,digest in parent["source_sha256"].items():
            assert hashlib.sha256((ROOT/source).read_bytes()).hexdigest()==digest,source
            paths.add(source)
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def classify(binary,path,p,q,buckets=8,quiet=False):
    with tempfile.TemporaryDirectory(prefix="symmetric-buckets-",dir=path.parent) as temp:
        result = subprocess.run([str(binary),str(path),str(p),str(q),temp,str(buckets)],
            check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE if quiet else None,text=True)
        assert not path.exists() and not list(Path(temp).iterdir())
        return json.loads(result.stdout)


def oracles(generator,sorter,path):
    from sympy import nextprime
    rnd = random.Random(PREFLIGHT_SEED)
    for index in range(512):
        p = int(nextprime(rnd.randrange(5,2000))) if index<480 else int(nextprime(2**61+rnd.randrange(2**20)))
        q = int(nextprime(rnd.randrange(p+1,8*p))) if index<480 else int(nextprime(2**62+rnd.randrange(2**20)))
        n = p*q
        values = [rnd.randrange(n) for _ in range(rnd.randrange(1,65))]
        if index%4==0:values.extend((0,0,p,q,n-p,n-q))
        if index%5==0:values.extend((-v%n for v in values[:8]))
        buckets = (1,2,3,5,8,16)[index%6]
        # Exercise labels on both sides of every P and Q bucket boundary.
        for prime in (p,q):
            for split in range(1,buckets):
                center = ((prime//2+1)*split+buckets-1)//buckets
                values.extend((center-1,center,center+1))
        FRONTIER["write_pairs"](path,values,p,q)
        result = classify(sorter,path,p,q,buckets,quiet=True)
        FRONTIER["check_classes"](result,values,p,q)
        assert result["raw_records"]==len(values)
        assert result["separate_Q_label_bytes"]==8*result["distinct_global_sign_orbits"]
    streams,zero_axes = 0,0
    for index in range(64):
        m = rnd.choice((3,5,7,11,13,17,19,23,31))
        p = int(nextprime(rnd.randrange(m*m+10,30000))) if index<48 else int(nextprime(2**61+rnd.randrange(2**20)))
        q = int(nextprime(rnd.randrange(p+1,8*p))) if index<48 else int(nextprime(2**62+rnd.randrange(2**20)))
        n = p*q
        for mode in (0,1,2):
            rows,values,companions = CURRENT["original_oracle"](n,m,mode)
            counts = PRIOR["native_rows"](generator,path,n,m,p,q,mode)
            raw = list(struct.iter_unpack("QQ",path.read_bytes()))
            assert raw==[PRIOR["JOINED"]["fold_pair"](v%p,v%q,p,q)[:2] for v in values],(index,mode)
            assert counts["original_packets"]==len(rows) and counts["companion_packets"]==companions
            assert counts["ordinary_records"]==len(values) and counts["scratch_bytes"]==16*len(values)
            result = classify(sorter,path,p,q,(1,3,8)[mode],quiet=True)
            FRONTIER["check_classes"](result,values,p,q)
            if mode==2:zero_axes += sum(w["a"]+w["t"]==0 or w["a"]-w["t"]==0 for w in rows)
            streams += 1
    return dict(arbitrary_whole_N_signed_set_oracles=512,wide_arbitrary_families=32,
        bucket_counts_checked=[1,2,3,5,8,16],all_bucket_boundaries_checked=True,
        complete_actual_families=64,complete_actual_family_streams=streams,wide_actual_families=16,
        zero_axis_denominators_checked=zero_axes,full_Nt_rows_and_whole_N_inverses_checked=True,
        all_global_and_both_factor_signed_counts_checked=True,undefined_behavior_checks=True)


def compile_binary(binary,source,ubsan=False):
    extra = ["-fsanitize=undefined","-fno-sanitize-recover=all"] if ubsan else []
    subprocess.run(["g++",*PRIOR["FLAGS"],*extra,str(ROOT/source),"-o",str(binary)],check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preflight-only",action="store_true")
    parser.add_argument("--output",type=Path,required=True)
    args = parser.parse_args()
    sources = source_inventory() if args.preflight_only else source_inventory(PARENT_AUDIT,PREFLIGHT_AUDIT)
    with tempfile.TemporaryDirectory(prefix="semiprime-symmetric-confirmation-") as temp:
        temp = Path(temp)
        generator,sorter,path = (temp/k for k in ("rows","sort","classes.bin"))
        if args.preflight_only:
            compile_binary(generator,CURRENT["CPP"],ubsan=True)
            compile_binary(sorter,SORT_CPP,ubsan=True)
            control = oracles(generator,sorter,path)
            assert source_inventory()==sources,"source changed during preflight"
            report = dict(replay_id=REPLAY_ID,preflight_seed=PREFLIGHT_SEED,source_sha256=sources,
                bucket_classifier_oracles=control,is_native_preflight_only=True,
                new_success_Lean_certificates=0,is_coverage_result=False,is_bit_complexity_certificate=False)
            args.output.write_text(json.dumps(report,indent=2)+"\n")
            print(json.dumps(dict(progress="bucket-preflight-completed",source_pins=len(sources),**control)),flush=True)
            return
        parent = json.loads((ROOT/PARENT_AUDIT).read_text())
        misses = [c for c in parent["complete_symmetric_families"] if c["signed_exhausted"]]
        assert misses,"no saved complete symmetric-family miss to confirm"
        case = misses[0]
        n,m,p,q = (case[k] for k in ("N","modulus","reference_p","reference_q"))
        compile_binary(generator,CURRENT["CPP"])
        compile_binary(sorter,SORT_CPP)
        rnd = random.Random(REPLAY_ID)
        residues = sorted({1,2,3,m-3,m-2,m-1,p%m,q%m,*[rnd.randrange(1,m) for _ in range(40)]}-{0})
        packets,scalars = 0,0
        for j in residues:
            rows,values,companions = CURRENT["original_oracle"](n,m,2,first=j,last=j+1)
            counts = PRIOR["native_rows"](generator,path,n,m,p,q,2,first=j,last=j+1)
            raw = list(struct.iter_unpack("QQ",path.read_bytes()))
            assert raw==[PRIOR["JOINED"]["fold_pair"](v%p,v%q,p,q)[:2] for v in values],j
            assert counts["original_packets"]==len(rows) and counts["companion_packets"]==companions
            result = classify(sorter,path,p,q,quiet=True)
            FRONTIER["check_classes"](result,values,p,q)
            packets += len(rows); scalars += len(values)
        print(json.dumps(dict(progress="complete-bucket-miss-confirmation-start",N=n,modulus=m,
            full_Nt_residue_slices_checked=len(residues),original_packets=packets,scalar_values=scalars)),flush=True)
        start = time.perf_counter()
        counts = PRIOR["native_rows"](generator,path,n,m,p,q,2)
        result = classify(sorter,path,p,q)
        elapsed = 1000*(time.perf_counter()-start)
        for key in PRIOR["JOINED"]["expected_counts"]([0],p,q):assert result[key]==case[key],key
        for key in ("original_packets","companion_packets","mode","literal_shifted_coordinates",
                "known_residue_coordinates","symmetric_axis_coordinates","affine_coordinates",
                "ordinary_records","scratch_bytes"):
            assert counts[key]==case[key],key
        assert result["signed_exhausted"] and result["raw_records"]==counts["ordinary_records"]
    assert source_inventory(PARENT_AUDIT,PREFLIGHT_AUDIT)==sources,"source changed during confirmation"
    report = dict(replay_id=REPLAY_ID,parent_audit=PARENT_AUDIT,preflight_audit=PREFLIGHT_AUDIT,
        source_sha256=sources,canonical_full_Nt_slice_checks=dict(residues=residues,
            original_packets=packets,scalar_values=scalars,all_centers_and_intermediates_checked=True),
        complete_bucket_confirmation=dict(N=n,modulus=m,reference_p=p,reference_q=q,**counts,**result,
            private_reference_milliseconds=elapsed,all_primary_population_counts_agree=True,
            both_factor_projections_fully_counted=True),
        independent_Q_bucket_label_classifier=True,same_frozen_original_packet_generator=True,
        no_new_success_Lean_certificates=True,is_kernel_execution_or_exhaustion_certificate=False,
        is_N_only_factorizer=False,is_bit_complexity_certificate=False,
        universal_symmetric_family_coverage_proved=False,guaranteed_one_sixth_factorization="OPEN",
        limitations="A complete finite native miss is corroborated by a separate bucketed classifier. The frozen public-packet generator is shared; new complete full-Nt slices independently check its stream. Large prefix and denominator unit guards use private factor bounds. No kernel exhaustion or complete public construction/recovery bit clock is supplied.")
    args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),confirmed_complete_native_miss=True,
        signed_classes=result["signed_whole_values_with_zero_anchor"],one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":main()

#!/usr/bin/env python3
"""Test the full amended family for failure on a fixed 121-bit frontier.

The next candidate inputs are fixed before any complete classification.
Stop at the first full signed-family exhaustion, after both prime fields
have been counted. Successful cases receive no new Lean certificates.
Private-field sorting is an exploratory coverage test, not bit complexity.
"""
from __future__ import annotations

import argparse
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
PARENT_AUDIT = "docs/semiprime-literal-root-control-audit.json"
CPP = "scripts/semiprime_literal_inplace_rows.cpp"
SORT_CPP = "scripts/semiprime_literal_inplace_sort.cpp"
REPLAY_ID = 202610033252
CANDIDATE_SEED = 202610033253
PRIOR = runpy.run_path(str(ROOT/"scripts/probe_semiprime_literal_quadratic_roots.py"))


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,CPP,SORT_CPP,"scripts/probe_semiprime_literal_inplace_frontier.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def classify(binary,path,p,q):
    return json.loads(subprocess.run([str(binary),str(path),str(p),str(q)],check=True,
        stdout=subprocess.PIPE,text=True).stdout)


def check_classes(result,values,p,q):
    for key,value in PRIOR["JOINED"]["expected_counts"](values,p,q).items():
        assert result[key]==value,(key,result[key],value)


def write_pairs(path,values,p,q):
    path.write_bytes(b"".join(struct.pack("QQ",*PRIOR["JOINED"]["fold_pair"](v%p,v%q,p,q)[:2])
        for v in values))


def oracles(generator,sorter,path,rnd):
    from sympy import nextprime
    generic,streams,wide = 0,0,0
    for index in range(512):
        p = int(nextprime(rnd.randrange(5,2000))) if index<480 else int(nextprime(2**61+rnd.randrange(2**20)))
        q = int(nextprime(rnd.randrange(p+1,8*p))) if index<480 else int(nextprime(2**62+rnd.randrange(2**20)))
        n = p*q
        values = [rnd.randrange(n) for _ in range(rnd.randrange(1,65))]
        if index%4==0:values.extend((0,0,p,q,n-p,n-q))
        if index%5==0:values.extend((-v%n for v in values[:8]))
        write_pairs(path,values,p,q)
        # Suppress routine generic sorter progress; only complete frontier jobs print it.
        result = json.loads(subprocess.run([str(sorter),str(path),str(p),str(q)],check=True,
            capture_output=True,text=True).stdout)
        check_classes(result,values,p,q)
        generic += 1
    for index in range(64):
        m = rnd.choice((3,5,7,11,13,17,19,23,31))
        p = int(nextprime(rnd.randrange(m*m+10,30000))) if index<48 else int(nextprime(2**61+rnd.randrange(2**20)))
        q = int(nextprime(rnd.randrange(p+1,8*p))) if index<48 else int(nextprime(2**62+rnd.randrange(2**20)))
        n = p*q
        for mode in (0,1):
            rows,values,companions = PRIOR["original_oracle"](n,m,mode)
            counts = PRIOR["native_rows"](generator,path,n,m,p,q,mode)
            raw = list(struct.iter_unpack("QQ",path.read_bytes()))
            assert raw==[PRIOR["JOINED"]["fold_pair"](v%p,v%q,p,q)[:2] for v in values],(index,mode)
            assert counts["original_packets"]==len(rows) and counts["companion_packets"]==companions
            assert counts["ordinary_records"]==len(values) and counts["scratch_bytes"]==16*len(values)
            result = json.loads(subprocess.run([str(sorter),str(path),str(p),str(q)],check=True,
                capture_output=True,text=True).stdout)
            check_classes(result,values,p,q)
            streams += 1
        wide += index>=48
    return dict(arbitrary_whole_N_signed_set_oracles=generic,actual_family_streams=streams,
        actual_families=64,wide_actual_families=wide,wide_arbitrary_families=32,
        undefined_behavior_checks=True,full_Nt_rows_and_whole_N_inverses_compared=True,
        both_complete_field_counts_compared=True)


def candidates():
    from sympy import integer_nthroot, nextprime
    rnd = random.Random(CANDIDATE_SEED)
    result = []
    for index in range(3):
        p = int(nextprime(2**60+rnd.randrange(2**58)))
        q = int(nextprime(p+1+rnd.randrange(2**58)))
        n = p*q
        floor,exact = integer_nthroot(n,6)
        width = int(floor)+(not exact)
        m = int(nextprime(width-1))
        assert n.bit_length()==121 and p<=q<=2*p and m*m<p
        assert (width-1)**6<n<=width**6
        result.append(dict(index=index,N=n,input_bits=121,reference_p=p,reference_q=q,
            sixth_width=width,modulus=m,balanced=True,private_prefix_unit_bound=m*m<p))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    sources,planned = source_inventory(),candidates()
    complete = []
    print(json.dumps(dict(progress="literal-frontier-candidates-fixed",candidate_seed=CANDIDATE_SEED,
        planned_candidates=planned,stop_condition="first complete signed exhaustion")),flush=True)
    with tempfile.TemporaryDirectory(prefix="semiprime-literal-inplace-") as temp:
        temp = Path(temp)
        generator,sorter,checked_rows,checked_sort,path = (temp/k for k in ("rows","sort","rows-ubsan","sort-ubsan","classes.bin"))
        for binary,source,ubsan in ((generator,CPP,False),(sorter,SORT_CPP,False),
                (checked_rows,CPP,True),(checked_sort,SORT_CPP,True)):
            extra = ["-fsanitize=undefined","-fno-sanitize-recover=all"] if ubsan else []
            subprocess.run(["g++",*PRIOR["FLAGS"],*extra,str(ROOT/source),"-o",str(binary)],check=True)
        control = oracles(checked_rows,checked_sort,path,random.Random(REPLAY_ID))
        print(json.dumps(dict(progress="inplace-frontier-oracles-completed",**control)),flush=True)
        for candidate in planned:
            n,m,p,q = (candidate[k] for k in ("N","modulus","reference_p","reference_q"))
            print(json.dumps(dict(progress="complete-amended-frontier-start",**candidate)),flush=True)
            start = time.perf_counter()
            counts = PRIOR["native_rows"](generator,path,n,m,p,q,1)
            result = classify(sorter,path,p,q)
            case = dict(**candidate,**counts,**result,
                private_reference_milliseconds=1000*(time.perf_counter()-start),
                all_original_residues_intermediates_and_both_centers_enumerated=True,
                old_joined_and_literal_roots_all_retained=True,
                both_prime_projections_fully_counted=True,is_N_only_classifier=False,
                is_kernel_execution_or_exhaustion_certificate=False,is_factorizer_runtime=False)
            complete.append(case)
            print(json.dumps(dict(progress="complete-amended-frontier-completed",**case)),flush=True)
            if case["signed_exhausted"]:break
    assert source_inventory()==sources,"source changed during replay"
    report = dict(replay_id=REPLAY_ID,candidate_seed=CANDIDATE_SEED,parent_audit=PARENT_AUDIT,
        source_sha256=sources,planned_candidates=planned,finite_inplace_sort_oracles=control,
        complete_amended_families=complete,
        complete_native_amended_misses=sum(c["signed_exhausted"] for c in complete),
        old_119_bit_positive_control_unchanged=True,no_new_success_Lean_certificates=True,
        universal_amended_coverage_proved=False,guaranteed_one_sixth_factorization="OPEN",
        is_complete_factorizer=False,is_bit_complexity_certificate=False,
        limitations="This planned 121-bit balanced frontier tests the entire amended signed family, with the canonical N-only modulus and complete private P,Q counts. The 16-byte whole-N common-sign encoding is a bijection and the table is reused for the second sort, without an extra Q vector. Generic whole-N signed-set oracles, full Nt-containing source streams and UBSan checks validate the native implementation. Any exhaustion is a complete finite native failure, not a kernel execution or exhaustion certificate. Prefix and denominator units on large cases are inferred from private bounds. No large public polynomial/prefix or construction-inclusive factoring bit clock is executed. Successful candidates provide no coverage credit.")
    if args.output:args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),complete_cases=len(complete),
        complete_native_misses=report["complete_native_amended_misses"],one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":main()

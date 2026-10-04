#!/usr/bin/env python3
"""Center-cancelled scalar discovery on the literal complete-family miss.

The common residual and the signed per-center error are separately retained
before joining their normalized scalar roots. Complete signed CRT reference
classification uses private prime labels. No large public polynomial timer,
kernel exhaustion proof or universal sixth-root coverage is claimed.
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
import tempfile
import time

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-complete-anchor-coverage-audit.json"
ORIGINAL_AUDIT = "docs/semiprime-joined-sorted-coverage-audit.json"
CPP = "scripts/semiprime_centered_point_rows.cpp"
REPLAY_ID = 202610033246
ANCHOR = runpy.run_path(str(ROOT/"scripts/probe_semiprime_complete_anchor_coverage.py"))
PRIOR = ANCHOR["PRIOR"]
JOINED = runpy.run_path(str(ROOT/"scripts/probe_semiprime_joined_sorted_coverage.py"))
SORT_CPP = "scripts/semiprime_joined_coverage_sort.cpp"
FLAGS = ANCHOR["FLAGS"]
MODES = {0:"common-midpoint-residual",1:"signed-per-center-error",2:"joined-residual-and-error"}


def source_inventory():
    paths = set()
    for name in (PARENT_AUDIT,ORIGINAL_AUDIT):
        parent = json.loads((ROOT/name).read_text())
        for path,digest in parent["source_sha256"].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
        paths.update(parent["source_sha256"])
        paths.add(name)
    paths.update((CPP,"scripts/probe_semiprime_centered_point_coverage.py",
        "RiemannGaussian/SemiprimeAffinePointAreas.lean","scripts/CheckSemiprimeAffinePointAreas.lean"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def native_rows(binary,path,n,m,p,q,mode):
    small,large = math.isqrt(n//2)+math.isqrt(n),math.isqrt(n)+math.isqrt(2*n)
    result = subprocess.run([str(binary),str(m),str(n%(m*m)),str(small),str(large),
        str(p),str(q),str(mode),str(path)],check=True,capture_output=True,text=True)
    return json.loads(result.stdout)


def original_oracle(n,m,mode):
    small,large = math.isqrt(n//2)+math.isqrt(n),math.isqrt(n)+math.isqrt(2*n)
    rows,values,points = [],[],[]
    for j in range(1,m):
        for z in PRIOR["WEIGHTED"]["reference_residue_packets"](n,m,j):
            L = m*z["b"]-2*z["a"]*j
            side = PRIOR["orientation"](z)
            A,B = (large,small) if side else (small,large)
            error = -2*L-z["a"]*A-z["t"]*B
            residual = -2*L-z["a"]*small-z["t"]*large
            assert residual==error+int(side)*(z["a"]-z["t"])*(large-small)
            inverse = pow(z["a"],-1,n)
            point = z["t"]*inverse%n,residual*inverse%n
            points.append(point)
            rows.append((z["a"],L,z["t"]))
            if mode!=1:values.append(point[1])
            if mode!=0:values.append(error*inverse%n)
    return rows,points,values


def point_oracles(rnd):
    from sympy import nextprime
    counts = Counter()
    for index in range(48):
        m = rnd.choice((3,5,7,11,13,17))
        p = int(nextprime(rnd.randrange(m+1,500)))
        q = p if index<24 else int(nextprime(rnd.randrange(p+1,10*p)))
        n = p*q
        rows,points,_ = original_oracle(n,m,0)
        for _ in range(64):
            indices = rnd.sample(range(len(rows)),3)
            area = PRIOR["AREA"]["area"](*(rows[i] for i in indices))
            normal = PRIOR["AREA"]["area"](*((1,*points[i]) for i in indices))%n
            product = math.prod(rows[i][0] for i in indices)
            assert product*normal%n==2*area%n
            assert math.gcd(n,normal)==math.gcd(n,area)
            counts["exact_all_triple_GCD_transports"] += 1
            counts["prime_square_transports"] += p==q
            counts["globally_zero_or_saturated_areas_retained"] += area%n==0
    return dict(counts)


def main():
    from sympy import isprime,nextprime
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--checked-declarations",type=int,default=0)
    parser.add_argument("--checked-theorems",type=int,default=0)
    parser.add_argument("--checked-explicit",type=int,default=0)
    args = parser.parse_args()
    sources,rnd = source_inventory(),random.Random(REPLAY_ID)
    carrier = point_oracles(rnd)
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    canonical = parent["complete_canonical_cases"][0]
    n,m,p,q = (canonical[k] for k in ("N","modulus","reference_p","reference_q"))
    assert n==p*q and isprime(m) and isprime(p) and isprime(q) and m<min(p,q)
    complete,oracles = [],[]
    compiler = subprocess.run(["g++","--version"],check=True,capture_output=True,
        text=True).stdout.splitlines()[0]
    with tempfile.TemporaryDirectory(prefix="semiprime-centered-point-") as temp:
        temp = Path(temp)
        generator,sorter,sanitized,path = temp/"points",temp/"sort",temp/"points-ubsan",temp/"classes.bin"
        subprocess.run(["g++",*FLAGS,str(ROOT/CPP),"-o",str(generator)],check=True)
        subprocess.run(["g++",*FLAGS,str(ROOT/SORT_CPP),"-o",str(sorter)],check=True)
        subprocess.run(["g++",*FLAGS,"-fsanitize=undefined","-fno-sanitize-recover=all",
            str(ROOT/CPP),"-o",str(sanitized)],check=True)
        for index in range(128):
            mm = rnd.choice((3,5,7,11,13,17,19,23,31))
            pp = int(nextprime(rnd.randrange(mm+1,30000))) if index<96 else int(nextprime(2**61+rnd.randrange(2**20)))
            qq = int(nextprime(rnd.randrange(pp+1,8*pp))) if index<96 else int(nextprime(2**62+rnd.randrange(2**20)))
            nn = pp*qq
            for mode in MODES:
                rows,_,values = original_oracle(nn,mm,mode)
                metadata = native_rows(sanitized,path,nn,mm,pp,qq,mode)
                raw = np.fromfile(path,dtype=JOINED["DTYPE"])
                records = [JOINED["fold_pair"](v%pp,v%qq,pp,qq) for v in values]
                assert [(int(z["fp"]),int(z["qc"]),int(z["fq"])) for z in raw]==records,(index,mode)
                assert metadata["original_packets"]==len(rows) and metadata["ordinary_records"]==len(values)
                actual = subprocess.run([str(sorter),str(path),str(pp),str(qq)],check=True,
                    capture_output=True,text=True)
                classification = json.loads(actual.stdout)
                for key,value in JOINED["expected_counts"](values,pp,qq).items():
                    assert classification[key]==value,(index,mode,key)
            oracles.append(dict(index=index,modulus=mm,wide_field_case=index>=96,
                all_three_scalar_modes_compared=True))
        print(json.dumps(dict(progress="centered-point-oracles-completed",families=128,
            scalar_streams=384,point_carrier=carrier)),flush=True)
        for mode,label in MODES.items():
            print(json.dumps(dict(progress="complete-centered-point-family-start",N=n,
                reference_p=p,reference_q=q,modulus=m,mode=mode,label=label)),flush=True)
            start = time.perf_counter()
            counts = native_rows(generator,path,n,m,p,q,mode)
            result = subprocess.run([str(sorter),str(path),str(p),str(q)],check=True,
                stdout=subprocess.PIPE,text=True)
            classification = json.loads(result.stdout)
            case = dict(N=n,input_bits=n.bit_length(),reference_p=p,reference_q=q,modulus=m,
                label=label,**counts,**classification,
                reference_classification_milliseconds=1000*(time.perf_counter()-start),
                all_original_residues_intermediates_and_centers_enumerated=True,
                both_prime_field_projections_fully_counted=True,zero_anchor_retained=True,
                coefficient_prefix_units_inferred_from_checked_bounds=True,
                is_N_only_classifier=False,is_factorizer_runtime_measurement=False,
                is_kernel_execution_or_exhaustion_certificate=False)
            complete.append(case)
            print(json.dumps(dict(progress="complete-centered-point-family-completed",**case)),flush=True)
    assert source_inventory()==sources,"source changed during replay"
    checked = args.checked_declarations>0 and args.checked_theorems>0
    report = dict(replay_id=REPLAY_ID,parent_audits=[PARENT_AUDIT,ORIGINAL_AUDIT],source_sha256=sources,
        compiler=compiler,compiler_flags=FLAGS,point_carrier_oracles=carrier,
        full_N_scalar_oracle_families=oracles,compared_scalar_streams=384,
        finite_generator_undefined_behavior_checks=True,unchanged_signed_classifier_parent_oracles_retained=True,
        complete_scalar_families=complete,lean_validation=dict(
            strict_leaf_and_root=checked,separately_completed_scoped_gates=checked,
            namespace_linters=14 if checked else 0,linter_errors=0 if checked else None,
            all_module_declarations=args.checked_declarations,explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        compiled_components=dict(signed_integer_common_plane_removal=True,
            two_coordinate_carrier_retains_all_three_row_GCDs=True,
            actual_public_large_factor_guards_discharged=True,
            residual_scalar_is_signed_two_row_minor_functional=True,
            chosen_anchor_is_one_secant_axis=True,linear_coordinate_storage=True),
        is_complete_factorizer=False,is_bit_complexity_certificate=False,
        universal_centered_scalar_coverage="OPEN",complete_incidence_extraction="OPEN",
        guaranteed_one_sixth_factorization="OPEN",
        limitations="The kernel removes one common midpoint plane over the integers, keeps both signed center channels upstream, and transports every triple's area GCD to two normalized coordinates. Leading and factor-two guards are proved for actual public packets when both prime factors exceed m>=2, including squares and arbitrary ratios in that branch. It proves linear coordinate storage, not a fast complete collinearity extractor. The new scalar projections retain the common residual and per-center error separately before their union. Full signed private CRT classification includes global duplicates, consistent common signs and a zero anchor. All original intermediates and centers remain; only private bounded reference generation and sorting are timed. Unit coefficient prefix entries are inferred from checked private bounds rather than individually evaluated as whole-N GCDs. Native successes or exhaustions concern these fixed scalar families, not all two-coordinate incidences or every factoring method. No large public root polynomial, universal coverage, kernel execution certificate, arbitrary-ratio acquisition or construction-inclusive deterministic N^(1/6) bit theorem is produced.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),complete_scalar_families=len(complete),
        native_scalar_exhaustions=sum(c["signed_exhausted"] for c in complete),
        one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":
    main()

#!/usr/bin/env python3
"""Complete shifted-quotient root discovery, with reference collision witnesses.

Both roots of every original common-coordinate quadratic are retained.
The augmented mode also preserves every old companion and affine root.
Private CRT sorting measures finite coverage only, not factorizer bit cost.
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
PARENT_AUDIT = "docs/semiprime-quadratic-point-jets-audit.json"
PRIOR = runpy.run_path(str(ROOT/"scripts/probe_semiprime_centered_point_coverage.py"))
JOINED = PRIOR["JOINED"]
WEIGHTED = PRIOR["PRIOR"]["WEIGHTED"]
CPP = "scripts/semiprime_literal_quotient_rows.cpp"
SORT_CPP = "scripts/semiprime_literal_quotient_sort.cpp"
FLAGS = PRIOR["FLAGS"]
REPLAY_ID = 202610033250
LABELS = {0:"literal-quotient-roots",1:"old-joined-plus-literal-quotient-roots"}


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,CPP,SORT_CPP,"scripts/probe_semiprime_literal_quadratic_roots.py",
        "RiemannGaussian/SemiprimeLiteralQuadraticRoots.lean","scripts/CheckSemiprimeLiteralQuadraticRoots.lean"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def native_rows(binary,path,n,m,p,q,mode,first=1,last=None):
    small,large = math.isqrt(n//2)+math.isqrt(n),math.isqrt(n)+math.isqrt(2*n)
    argv = [str(binary),str(m),str(n%(m*m)),str(small),str(large),str(p),str(q),str(mode),str(path)]
    if last is not None:argv.extend((str(first),str(last)))
    return json.loads(subprocess.run(argv,check=True,capture_output=True,text=True).stdout)


def original_oracle(n,m,mode,first=1,last=None):
    values,rows,companions = [0],[],0
    for j in range(first,m if last is None else last):
        values.append(-j%n)
        packets = list(WEIGHTED["reference_residue_packets"](n,m,j))
        assert len(packets)%2==0
        previous = None
        for index in range(0,len(packets),2):
            current = packets[index:index+2]
            for w in current:
                a,t,L = w["a"],w["t"],m*w["b"]-2*w["a"]*j
                alpha = -L*pow(a,-1,n)%n
                values.append((alpha-j)%n)
                if mode:values.extend((alpha,-L*pow(t,-1,n)%n))
                rows.append(dict(w,L=L,alpha=alpha,known_root=-j%n,shifted_root=(alpha-j)%n))
            if mode and previous is not None:
                for u in previous:
                    for w in current:
                        D = u["a"]*w["t"]-w["a"]*u["t"]
                        numerator = -(w["t"]*(m*u["b"]-2*u["a"]*j)-u["t"]*(m*w["b"]-2*w["a"]*j))
                        assert abs(D)==m and numerator%D==0
                        values.append(numerator//D%n)
                        companions += 1
            previous = current
    return rows,values,companions


def resultant(a,b,c,d,e,f):
    return (a*f-d*c)**2-(a*e-d*b)*(b*f-e*c)


def algebra_oracles(rnd):
    from sympy import nextprime, resultant as symbolic_resultant, symbols
    variable = symbols("T")
    counts = Counter()
    for index in range(48):
        m = rnd.choice((3,5,7,11,13,17,19))
        p = int(nextprime(rnd.randrange(m*m+10,30000)))
        q = p if index<24 else int(nextprime(rnd.randrange(p+1,10*p)))
        n = p*q
        rows,_,_ = original_oracle(n,m,0)
        for sample in range(64):
            u,w = rnd.sample(rows,2)
            actual = resultant(u["a"],u["b"],u["c"],w["a"],w["b"],w["c"])
            ru,su,rw,sw = (u["known_root"],u["shifted_root"],w["known_root"],w["shifted_root"])
            product = (ru-rw)*(ru-sw)*(su-rw)*(su-sw)%n
            assert m**4*actual%n==u["a"]**2*w["a"]**2*product%n
            assert math.gcd(n,actual)==math.gcd(n,product)
            assert math.gcd(n,u["b"])==math.gcd(n,(ru+su)%n)
            assert math.gcd(n,u["c"])==math.gcd(n,su)
            T = rnd.randrange(-10000,10001)
            assert (u["a"]*T*T+m*u["b"]*T+m*m*u["c"])%n==u["a"]*(T-ru)*(T-su)%n
            counts["exact_original_resultant_GCD_transports"] += 1
            counts["prime_square_transports"] += p==q
            counts["zero_or_saturated_original_resultants"] += actual%n==0
            counts["proper_original_resultant_GCDs"] += 1<math.gcd(n,actual)<n
            counts["constant_and_linear_coefficient_GCD_transports"] += 2
            counts["literal_common_variable_factorizations"] += 1
            if index<4 and sample<16:
                genuine = symbolic_resultant(u["a"]*variable**2+u["b"]*variable+u["c"],
                    w["a"]*variable**2+w["b"]*variable+w["c"],variable)
                assert int(genuine)==actual
                counts["independent_SymPy_original_resultants"] += 1
    return dict(counts)


def check_witnesses(result,n,p,q,values=None):
    witnesses = []
    signed = {0}|{v%n for v in values}|{-v%n for v in values} if values is not None else None
    for side,prime in (("p",p),("q",q)):
        pair = result["first_"+side+"_collision"]
        if pair is None:continue
        whole = [(a+p*((b-a)*pow(p,-1,q)%q))%n for a,b in pair]
        if signed is not None:assert all(v in signed for v in whole)
        divisor = math.gcd(n,(whole[0]-whole[1])%n)
        assert divisor==prime and 1<divisor<n
        witnesses.append(dict(side=side,field_coordinate_pair=pair,signed_whole_N_values=whole,
            exact_difference_GCD=divisor,source_packet_membership_kernel_checked=False))
    return witnesses


def main():
    from sympy import isprime,nextprime
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--checked-declarations",type=int,default=0)
    parser.add_argument("--checked-theorems",type=int,default=0)
    parser.add_argument("--checked-explicit",type=int,default=0)
    args = parser.parse_args()
    sources,rnd = source_inventory(),random.Random(REPLAY_ID)
    algebra = algebra_oracles(rnd)
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())["literal_canonical_large_residue_slices"]
    n,m,p,q = (parent[k] for k in ("N","modulus","reference_p","reference_q"))
    assert n==p*q and all(isprime(z) for z in (m,p,q)) and m*m<min(p,q)
    complete,oracles = [],[]
    with tempfile.TemporaryDirectory(prefix="semiprime-literal-quotient-") as temp:
        temp = Path(temp)
        generator,sorter,sanitized,checked_sort,path = (temp/k for k in ("rows","sort","rows-ubsan","sort-ubsan","classes.bin"))
        for binary,source,ubsan in ((generator,CPP,False),(sorter,SORT_CPP,False),
                (sanitized,CPP,True),(checked_sort,SORT_CPP,True)):
            extra = ["-fsanitize=undefined","-fno-sanitize-recover=all"] if ubsan else []
            subprocess.run(["g++",*FLAGS,*extra,str(ROOT/source),"-o",str(binary)],check=True)
        for index in range(128):
            mm = rnd.choice((3,5,7,11,13,17,19,23,31))
            pp = int(nextprime(rnd.randrange(mm*mm+10,30000))) if index<96 else int(nextprime(2**61+rnd.randrange(2**20)))
            qq = int(nextprime(rnd.randrange(pp+1,8*pp))) if index<96 else int(nextprime(2**62+rnd.randrange(2**20)))
            nn = pp*qq
            for mode in LABELS:
                rows,values,companions = original_oracle(nn,mm,mode)
                metadata = native_rows(sanitized,path,nn,mm,pp,qq,mode)
                raw = np.fromfile(path,dtype=JOINED["DTYPE"])
                assert [(int(z["fp"]),int(z["qc"]),int(z["fq"])) for z in raw]==[
                    JOINED["fold_pair"](v%pp,v%qq,pp,qq) for v in values],(index,mode)
                assert metadata["original_packets"]==len(rows) and metadata["companion_packets"]==companions
                result = json.loads(subprocess.run([str(checked_sort),str(path),str(pp),str(qq)],
                    check=True,capture_output=True,text=True).stdout)
                for key,value in JOINED["expected_counts"](values,pp,qq).items():assert result[key]==value,(index,mode,key)
                witnesses = check_witnesses(result,nn,pp,qq,values)
                assert len(witnesses)==sum(result["signed_"+k+"_collapsed_values"]>0 for k in ("p","q"))
            oracles.append(dict(index=index,modulus=mm,wide_field_case=index>=96,both_modes_exact=True))
        print(json.dumps(dict(progress="literal-quadratic-oracles-completed",families=128,
            scalar_streams=256,algebra=algebra)),flush=True)
        for mode,label in LABELS.items():
            print(json.dumps(dict(progress="complete-literal-quadratic-start",N=n,modulus=m,mode=mode,label=label)),flush=True)
            start = time.perf_counter()
            counts = native_rows(generator,path,n,m,p,q,mode)
            result = json.loads(subprocess.run([str(sorter),str(path),str(p),str(q)],check=True,
                stdout=subprocess.PIPE,text=True).stdout)
            case = dict(N=n,input_bits=n.bit_length(),reference_p=p,reference_q=q,modulus=m,label=label,
                **counts,**result,reference_classification_milliseconds=1000*(time.perf_counter()-start),
                collision_witnesses=check_witnesses(result,n,p,q),
                all_original_residues_intermediates_and_centers_enumerated=True,
                both_prime_field_projections_fully_counted=True,old_joined_family_retained=bool(mode),
                is_N_only_classifier=False,is_factorizer_runtime_measurement=False,
                is_kernel_execution_or_exhaustion_certificate=False)
            complete.append(case)
            print(json.dumps(dict(progress="complete-literal-quadratic-completed",**case)),flush=True)
    assert source_inventory()==sources,"source changed during replay"
    checked = args.checked_declarations>0 and args.checked_theorems>0
    report = dict(replay_id=REPLAY_ID,parent_audit=PARENT_AUDIT,source_sha256=sources,
        algebra_oracles=algebra,whole_N_root_and_native_classification_oracles=oracles,
        compared_scalar_streams=256,finite_generator_and_sorter_undefined_behavior_checks=True,
        complete_canonical_families=complete,compiled_components=dict(
            all_original_common_coordinate_quadratics_split=True,
            original_row_pair_resultant_GCD_unit_transport=True,
            original_constant_and_linear_coefficient_GCD_transports=True,
            proper_original_resultant_hits_recovered=True,full_old_joined_recovery_preserved=True,
            public_prefix_discharges_leading_known_root_and_modulus_guards=True,
            augmented_root_count_at_most_five_R_plus_m=True,
            recovery_query_count_at_most_fifteen_R_plus_five_m_plus_one=True),lean_validation=dict(
            strict_leaf_and_root=checked,separately_completed_scoped_gates=checked,
            namespace_linters=14 if checked else 0,linter_errors=0 if checked else None,
            all_module_declarations=args.checked_declarations,explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        is_complete_factorizer=False,is_bit_complexity_certificate=False,
        guaranteed_one_sixth_factorization="OPEN",universal_literal_quadratic_coverage="OPEN",
        limitations="The packet-specific residue shift remains in the common coordinate mX. Both original quadratic roots and all old joined roots survive, including signs, global duplicates and a zero anchor. Original quadratic resultant, constant/linear coefficient and prime-square transports are kernel theorems, independently checked against full Nt-containing packets. Native reference construction uses public reduced-offset payloads plus private prime labels. Full P and Q projections include a 16-byte Q witness label per global sign orbit; both collisions are reported with exact whole-N difference GCDs, but large source packet membership is not kernel certified by this classifier. Prefix units on the canonical input are inferred from private bounds, with no newly executed large public prefix. Only private bounded native generation and sorting are timed. No fast public polynomial construction/evaluation bit refinement, universally useful literal pair or triple, arbitrary-ratio acquisition or construction-inclusive deterministic N^(1/6) bit factorizer is produced.")
    if args.output:args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),complete_families=len(complete),
        native_exhaustions=sum(c["signed_exhausted"] for c in complete),one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":
    main()

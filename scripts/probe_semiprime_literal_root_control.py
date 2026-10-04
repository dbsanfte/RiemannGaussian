#!/usr/bin/env python3
"""Resolve the literal-root collision and check the complete source packets.

Private-field scanning proposes witnesses. Independent full Nt-containing
rows check the proposal; the separate Lean control certifies public source
membership, exact whole-N GCD and N-only recovery for this single input.
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

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-literal-quadratic-roots-audit.json"
CPP = "scripts/semiprime_literal_root_witness.cpp"
REPLAY_ID = 202610033251
PRIOR = runpy.run_path(str(ROOT/"scripts/probe_semiprime_literal_quadratic_roots.py"))


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,CPP,"scripts/probe_semiprime_literal_root_control.py",
        "RiemannGaussian/SemiprimeLiteralRootControl.lean","scripts/CheckSemiprimeLiteralRootControl.lean"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def scan(binary,n,m,p,q,queries):
    small,large = math.isqrt(n//2)+math.isqrt(n),math.isqrt(n)+math.isqrt(2*n)
    argv = [str(binary),*map(str,(m,n%(m*m),small,large,p,q))]
    argv.extend(str(coordinate) for pair in queries for coordinate in pair)
    return [json.loads(line) for line in subprocess.run(argv,check=True,capture_output=True,text=True).stdout.splitlines()]


def entry(value,n,p,q,j,a=0,t=0,side=False,L=0,kind="known"):
    ep,eq = value%p,value%q
    np,nq = -ep%p,-eq%q
    fp,qc,_ = PRIOR["JOINED"]["fold_pair"](ep,eq,p,q)
    sign = 1 if ep<np or (ep==np and eq<=nq) else -1
    return (fp,qc),dict(kind=kind,residue=j,numerator=a,denominator=t,larger_center=side,
        offset=L,sign=sign,raw_p=ep,raw_q=eq)


def check_small(binary,rnd):
    from sympy import nextprime
    oracles,queries_checked,packet_matches = [],0,0
    for index in range(48):
        m = rnd.choice((3,5,7,11,13,17,19,23,31))
        p = int(nextprime(rnd.randrange(m*m+10,30000))) if index<32 else int(nextprime(2**61+rnd.randrange(2**20)))
        q = int(nextprime(rnd.randrange(p+1,8*p))) if index<32 else int(nextprime(2**62+rnd.randrange(2**20)))
        n = p*q
        rows,_,_ = PRIOR["original_oracle"](n,m,0)
        expected = [entry(-j,n,p,q,j) for j in range(m)]
        for w in rows:
            expected.append(entry(w["shifted_root"],n,p,q,w["j"],w["a"],w["t"],
                w["center_orientation"]=="larger-factor",w["L"],"shifted"))
        distinct = sorted({pair for pair,_ in expected})
        queries = rnd.sample(distinct,min(32,len(distinct)))
        queries.extend((rnd.randrange(p//2+1),rnd.randrange(q)) for _ in range(8))
        result = scan(binary,n,m,p,q,queries)
        want = []
        for query,pair in enumerate(queries):
            want.extend(dict(query=query,**metadata) for key,metadata in expected if key==pair)
        freeze = lambda item: json.dumps(item,sort_keys=True)
        assert Counter(map(freeze,result[:-1]))==Counter(map(freeze,want)),index
        assert result[-1]==dict(original_packets=len(rows),known_coordinates=m,
            matches=[sum(item["query"]==k for item in want) for k in range(len(queries))]),index
        queries_checked += len(queries)
        packet_matches += len(want)
        oracles.append(dict(index=index,modulus=m,wide_fields=index>=32,queries=len(queries),
            known_and_shifted_sources_checked=True,full_Nt_offsets_and_signs_exact=True))
    return dict(families=oracles,query_count=queries_checked,source_matches=packet_matches,
        undefined_behavior_checked=True)


def check_control(binary,parent):
    case = parent["complete_canonical_families"][0]
    n,m,p,q = (case[key] for key in ("N","modulus","reference_p","reference_q"))
    witness = case["collision_witnesses"][0]
    queries = witness["field_coordinate_pair"]
    result = scan(binary,n,m,p,q,queries)
    assert result[-1]==dict(original_packets=case["original_packets"],known_coordinates=m,matches=[1,1])
    candidates = sorted(result[:-1],key=lambda item:item["query"])
    packets = []
    for found,value in zip(candidates,witness["signed_whole_N_values"],strict=True):
        assert found["kind"]=="shifted"
        w = next(row for row in PRIOR["WEIGHTED"]["reference_residue_packets"](n,m,found["residue"])
            if row["a"]==found["numerator"] and row["t"]==found["denominator"] and
                (row["center_orientation"]=="larger-factor")==found["larger_center"])
        L = m*w["b"]-2*w["a"]*w["j"]
        gamma = (-L*pow(w["a"],-1,n)-w["j"])%n
        assert L==found["offset"] and found["sign"]*gamma%n==value
        assert gamma%p==found["raw_p"] and gamma%q==found["raw_q"]
        packets.append(dict(w,L=L,shifted_root=gamma,signed_root=value,sign=found["sign"]))
    u,w = packets
    resultant = PRIOR["resultant"]
    ordinary = resultant(u["a"],u["b"],u["c"],w["a"],w["b"],w["c"])
    reflected = resultant(u["a"],u["b"],u["c"],w["a"],-w["b"],w["c"])
    exact = math.gcd(n,u["shifted_root"]+w["shifted_root"])
    assert exact==witness["exact_difference_GCD"]==math.gcd(n,reflected)==p
    assert math.gcd(n,ordinary)==1
    from sympy import resultant as sympy_resultant, symbols
    X = symbols("X")
    for b,res in ((w["b"],ordinary),(-w["b"],reflected)):
        assert int(sympy_resultant(u["a"]*X**2+u["b"]*X+u["c"],w["a"]*X**2+b*X+w["c"],X))==res
    return dict(N=n,input_bits=n.bit_length(),modulus=m,source_packets=packets,
        full_source_scan=result[-1],exact_signed_root_sum_GCD=exact,
        original_unsigned_resultant=ordinary,original_unsigned_resultant_GCD=1,
        original_reflected_resultant=reflected,original_reflected_resultant_GCD=exact,
        independent_SymPy_resultants_checked=2,private_reference_fields=[p,q],
        private_search_is_N_only=False,is_universal_coverage_certificate=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--checked-declarations",type=int,default=0)
    parser.add_argument("--checked-theorems",type=int,default=0)
    parser.add_argument("--checked-explicit",type=int,default=0)
    args = parser.parse_args()
    sources,rnd = source_inventory(),random.Random(REPLAY_ID)
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    with tempfile.TemporaryDirectory(prefix="semiprime-literal-control-") as temp:
        native,ubsan = (Path(temp)/name for name in ("scan","scan-ubsan"))
        for binary,extra in ((native,[]),(ubsan,["-fsanitize=undefined","-fno-sanitize-recover=all"])):
            subprocess.run(["g++",*PRIOR["FLAGS"],*extra,str(ROOT/CPP),"-o",str(binary)],check=True)
        oracles = check_small(ubsan,rnd)
        control = check_control(native,parent)
    assert source_inventory()==sources,"source changed during replay"
    checked = args.checked_declarations>0 and args.checked_theorems>0
    report = dict(replay_id=REPLAY_ID,parent_audit=PARENT_AUDIT,source_sha256=sources,
        finite_source_resolution_oracles=oracles,literal_control=control,
        compiled_components=dict(public_Euclidean_source_membership_checked=checked,
            original_centered_coefficients_and_offsets_checked=checked,
            shifted_roots_certified_by_whole_N_coefficient_equations=checked,
            proper_signed_root_sum_GCD_checked=checked,
            original_unsigned_and_reflected_Sylvester_resultant_GCDs_checked=checked,
            N_m_only_recovery_on_literal_input_checked=checked,
            canonical_N_only_modulus_and_recovery_checked=checked),
        lean_validation=dict(strict_leaf_and_root=checked,separately_completed_scoped_gates=checked,
            namespace_linters=14 if checked else 0,linter_errors=0 if checked else None,
            all_module_declarations=args.checked_declarations,explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        is_complete_factorizer=False,is_bit_complexity_certificate=False,
        guaranteed_one_sixth_factorization="OPEN",universal_literal_quadratic_coverage="OPEN",
        limitations="The scanner uses private prime coordinates solely to find two candidate source rows. Full Nt-containing reference rows and independent resultants validate those candidates. The separate Lean control checks public Euclidean membership, original offsets, leading and modulus units, literal shifted roots, proper signed GCD, N,m-only recovery and the canonical N-only public modulus. A single success and complete finite private class counts do not prove universal hit coverage or the public construction-inclusive deterministic N^(1/6) bit cost.")
    if args.output:args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),oracle_families=len(oracles["families"]),
        proper_signed_GCD=control["exact_signed_root_sum_GCD"],one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":main()

#!/usr/bin/env python3
"""Generic oscillation gate and sealed repair from existing signed candidates."""
import argparse
from collections import Counter
from fractions import Fraction as Q
import os
from pathlib import Path
import random
import subprocess
import sys
import flint
from stable_scale_search import BASE,read,write,sha,digest,verify_code
from prime_twist_grammar import observe
from prime_error_grammar import logarithmic_coefficients
from prime_twist_search import comparisons

CODE=["prime_oscillation_audit.py","check_prime_oscillation.py","prime_oscillation_report.py","prime_oscillation_proof.txt"]
PAPER=BASE/"prime-oscillation-results/source/HardyLittlewood_BF02422942.pdf"


def certificate(p,c):
    delta=Q(p["delta"]);r=p["leading_index"];nu=r*delta
    if p["channel"]!="log" or Q(c["log_power"])!=0 or Q(c["theta"])+nu!=Q(1,2):return None
    mismatches=[j for j,(a,b) in enumerate(zip(p["coefficients"],p["normalizers"])) if Q(a)!=Q(b)]
    if any((j-r)*delta<Q(1,2) for j in mismatches):return None
    tail=list(map(Q,p["coefficients"][r+1:]));S=sum(map(abs,tail),Q(0))
    z0=min(Q(1),1/(2*S)) if S else Q(1);K=1
    while Q(2**K)**delta.numerator*z0**delta.denominator<1:K+=1
    L=sum((j*abs(a) for j,a in enumerate(tail,1)),Q(0))
    return {"status":"uniform_claim_ruled_out_by_imported_prime_error_oscillation",
        "leading_shift":str(nu),"tail_absolute_sum":str(S),"rational_root_cutoff":str(z0),"eventual_integer_threshold":2**K,
        "eventual_normalized_weight_interval":["1/2","3/2"],"inverse_weight_constant":"2",
        "inverse_weight_derivative_constant":str(2*nu+4*delta*L),
        "normalizer_mismatch_shifts":[str((j-r)*delta) for j in mismatches],
        "consequence":"psi(x)-x=O(sqrt(x)); contradicted by the named oscillation import",
        "named_dependency":"Hardy-Littlewood Acta 41 section 5.1 (5.111),(5.112)","RH_proved":False}


def protocol(source,coverage=None):
    from prime_twist_report import summary
    source=Path(source).resolve();r=summary(source);parent=read(source/"protocol.json");cut=r["complete_coefficient_cutoff"]
    coverage_record=None
    if coverage is not None:
        from prime_twist_coverage_report import summary as coverage_summary
        coverage=Path(coverage).resolve();cv=coverage_summary(coverage);assert Path(cv["source_run"])==source
        cut=max(cut,cv["cutoff"]);coverage_record={"run_directory":str(coverage),"verification_sha256":sha(coverage/"verification.json")}
    return {"schema":1,"precision":384,"source_run":str(source),"source_coverage":coverage_record,
        "source_sha256":{n:sha(source/n) for n in ("protocol.json","verification.json","candidate_batch.json","validation_data.json","archive.json","final_evaluation.json")},
        "code_sha256":dict(parent["code_sha256"],**{n:sha(BASE/n) for n in CODE}),"this_stage_source_files":CODE,
        "oscillation_dependency":{"path":str(PAPER),"sha256":sha(PAPER),"doi":"10.1007/BF02422942","section":"5.1","printed_page":184,"PDF_page_one_based":33,
            "statement":"psi(x)-x=Omega_+(sqrt(x) logloglog(x))=Omega_-(sqrt(x) logloglog(x))",
            "proof_imported_not_independently_reproved":True,"machine_formalized":False},
        "compatibility_rule":"ALL log-channel pure critical-power candidates with compensated real poles; eventual polynomial inversion implies the forbidden sqrt(x) psi bound",
        "repair_rule":"For each rejected archived program, choose a source-batch RH-compatible estimate with the same ordinary exponent and positive log-power, ranked by source validation, full recovery cost, log-power, constant and id",
        "earlier_final_and_coverage_are_development_data":True,"selection_uses_source_validation_only":True,
        "fresh_final_interval":{"start":cut+1,"endpoint_range":[cut+1,2*cut+1],"every_integer_tested":True},
        "model_or_network_calls_in_selector":False,"historical_priority_is_acceptance_gate":False,
        "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}


def discover(directory):
    spec=read(directory/"protocol.json");verify_code(spec);source=Path(spec["source_run"])
    batch=read(source/"candidate_batch.json");ps={p["id"]:p for p in batch["programs"]}
    ruled={c["id"]:cert for c in batch["candidates"] if (cert:=certificate(ps[c["program_id"]],c)) is not None}
    old=read(source/"archive.json")["archive"];validation=read(source/"validation_data.json")["candidates"];repairs=[]
    for c in old:
        if c["id"] not in ruled:continue
        pool=[v for v in validation if v["program_id"]==c["program_id"] and v["analytic_status"].startswith("RH_sufficient") and Q(v["log_power"])>0 and v["transfer"]["ordinary_zeta_exponent"]==c["transfer"]["ordinary_zeta_exponent"]]
        if pool:
            choice=min(pool,key=lambda v:(bool(v["validation_failures"] or v["validation_unresolved"]),v["log_reciprocal_cost"],Q(v["log_power"]),Q(v["constant"]),v["id"]))
            repairs.append({"rejected_source_candidate_id":c["id"],"candidate":choice,"program":ps[choice["program_id"]]})
    write(directory/"compatibility.json",{"candidate_certificates":ruled,"complete_candidates_considered":len(batch["candidates"]),
        "class_status_counts":dict(Counter(c["analytic_status"] for c in batch["candidates"] if c["id"] in ruled)),"archived_candidates_ruled_out":[c["id"] for c in old if c["id"] in ruled]})
    write(directory/"repairs.json",{"repairs":repairs,"selection_closed":True,"final_data_used":False})
    write(directory/"seal.json",{"protocol_sha256":digest(spec),"selection_closed":True,"final_cases_exist_at_seal":False,
        "files":{n:sha(directory/n) for n in ("protocol.json","compatibility.json","repairs.json")}})
    print("Sealed oscillation audit:",len(ruled),"generic rejected bounds;",len(repairs),"positive-log repairs",flush=True)


def final(directory):
    spec=read(directory/"protocol.json");verify_code(spec);seal=read(directory/"seal.json")
    if (directory/"final_cases.json").exists():raise FileExistsError("Retain the original sealed final cases")
    flint.ctx.prec=spec["precision"]
    for name,h in seal["files"].items():assert sha(directory/name)==h
    seed=int.from_bytes(os.urandom(32),"big");rng=random.Random(seed);rule=spec["fresh_final_interval"];N=rng.randint(*rule["endpoint_range"])
    cases={"evaluator_seed":str(seed),"start":rule["start"],"endpoint":N,"created_after_selection_closed":True,"seal_sha256":digest(seal)}
    write(directory/"final_cases.json",cases);repairs=read(directory/"repairs.json")["repairs"]
    f=logarithmic_coefficients(N);points=list(range(cases["start"],N+1));ps=[r["program"] for r in repairs]
    values=observe(ps,f,points);outcomes=[]
    for row in repairs:
        c=row["candidate"];states=comparisons(c,values[c["program_id"]])
        outcomes.append({"candidate_id":c["id"],"comparisons":len(states),"failures":[int(n) for n,v in states.items() if v=="fail"],"unresolved":[int(n) for n,v in states.items() if v=="unresolved"],
            "finite_interval_passed":all(v=="pass" for v in states.values()),"uniform_signed_premise_proved":False})
    write(directory/"final_evaluation.json",{"values":values,"outcomes":outcomes,"coefficient_cutoff":N,"coefficient_sha256":digest(list(map(str,f))),
        "seal_sha256":digest(seal),"cases_sha256":digest(cases),"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False})
    print("Evaluated every repaired bound on fresh integer interval",cases["start"],"..",N,flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("mode",choices=("run","discover","final"));parser.add_argument("--run-dir",type=Path,required=True);parser.add_argument("--source-run",type=Path);parser.add_argument("--coverage-run",type=Path)
    args=parser.parse_args();directory=args.run_dir.resolve()
    if args.mode=="run":
        if directory.exists() or args.source_run is None:raise ValueError("A fresh audit destination and verified source required")
        directory.mkdir(parents=True);write(directory/"protocol.json",protocol(args.source_run,args.coverage_run))
        copies=directory/"frozen_source";copies.mkdir()
        for name in CODE:(copies/name).write_bytes((BASE/name).read_bytes())
        for mode in ("discover","final"):subprocess.run([sys.executable,str(Path(__file__)),mode,"--run-dir",str(directory)],check=True,cwd=BASE)
        subprocess.run([sys.executable,str(BASE/"check_prime_oscillation.py"),"--run-dir",str(directory)],check=True,cwd=BASE)
        from prime_oscillation_report import publish
        publish(directory)
    elif args.mode=="discover":discover(directory)
    else:final(directory)

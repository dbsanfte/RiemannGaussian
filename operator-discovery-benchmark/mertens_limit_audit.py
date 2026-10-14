#!/usr/bin/env python3
"""Generic small-order inverse-norm gate and sealed source-batch repairs."""
import argparse
from fractions import Fraction as Q
from pathlib import Path
import os,random,subprocess,sys
import flint
from stable_scale_search import BASE,read,write,sha,digest,verify_code
from estimate_grammar import inverse_one_prefix
from fractional_remainder_grammar import primitive_tables,response,order,serialize,real,power
from fractional_remainder_search import comparisons

CODE=["mertens_limit_audit.py","check_mertens_limits.py","mertens_limit_report.py","mertens_limit_proof.txt"]
PAPER=BASE/"mertens-limit-results/source/Hurst_1610.08551v2.pdf"


def certificate(p,c):
    if not p["positive_orders_compensated"] or Q(c["theta"])!=Q(1,2) or Q(c["parameter_power"])!=0 or Q(c["log_power"])!=0:return None
    S=sum(map(Q,p["coefficients"]),Q(0));B=sum(map(Q,p["normalizers"]),Q(0))
    if not S:return None
    ratio=B/S
    if ratio==Q(1,2):return None
    K=1/abs(S) if not B else (1+abs(ratio)/abs(ratio-Q(1,2)))/abs(S)
    if Q(c["constant"])*K>Q(7,4):return None
    return {"status":"ruled_out_by_exact_small_order_inverse_and_named_Mertens_extremum",
        "coefficient_sum":str(S),"normalizer_sum":str(B),"inverse_real_pole":str(1-ratio),
        "inverse_asymptotic_norm_constant":str(K),"implied_Mertens_lim_abs_upper":str(Q(c["constant"])*K),
        "imported_strict_Mertens_lower_threshold":"7/4","inverse_direction":"exact_Mertens_affine" if not B else "forward_Volterra" if ratio>Q(1,2) else "tail_Volterra_with_Mellin_cancellation",
        "named_dependency":"Hurst arXiv:1610.08551v2 Theorem 6.1; rational weakening only",
        "imported_numerical_theorem_independently_reproduced":False,"RH_proved":False}


def protocol(source):
    from fractional_remainder_report import summary
    source=Path(source).resolve();parent=summary(source);old=read(source/"protocol.json");cut=parent["complete_coefficient_cutoff"];failed=[]
    for path in sorted((BASE/"mertens-limit-results").glob("*/failure.json")):
        run=path.parent;cases=read(run/"final_cases.json");prior=read(run/"protocol.json");cut=max(cut,cases["endpoint"])
        failed.append({"run_directory":str(run),"failure_sha256":sha(path),"protocol_sha256":sha(run/"protocol.json"),"final_sha256":sha(run/"final_evaluation.json"),
            "cases_sha256":sha(run/"final_cases.json"),"cutoff":cases["endpoint"],"excluded_q":cases["fresh_q"],"frozen_source_sha256":{n:prior["code_sha256"][n] for n in prior["this_stage_source_files"]}})
    return {"schema":1,"precision":320,"source_run":str(source),
        "source_sha256":{n:sha(source/n) for n in ["protocol.json","verification.json","candidate_batch.json","validation_data.json","archive.json","final_evaluation.json"]},
        "code_sha256":dict(old["code_sha256"],**{n:sha(BASE/n) for n in CODE}),"this_stage_source_files":CODE,
        "named_external_dependency":{"path":str(PAPER),"sha256":sha(PAPER),"url":"https://arxiv.org/pdf/1610.08551v2","author":"Greg Hurst",
            "theorem":"6.1","printed_page":11,"statement":"liminf M(x)/sqrt(x)<-1.837625","used_rational_weaker_consequence":"limsup |M(x)|/sqrt(x)>7/4",
            "imported_not_independently_reproduced":True,"machine_formalized":False},
        "rule":"every compensated pure critical-power source candidate with kappa=0, nonzero limit coefficient sum and supported real inverse; C*K<=7/4 contradicts the named import",
        "repair_rule":"same source program, theta and kappa; positive logarithmic loss; source validation then full conditional cost; no refitting",
        "fresh_final":{"start":cut+1,"endpoint_range":[cut+64,2*cut+1],
            "higher_degree_point_count":6,"fresh_q_count":2,"fresh_q_range":[101,197],"degree_zero_every_integer":True},
        "source_final_is_development":True,"selector_uses_source_validation_only":True,"selector_model_network_calls":False,
        "retained_failed_runs_are_development":failed,
        "historical_priority_is_acceptance_gate":False,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}


def discover(directory):
    spec=read(directory/"protocol.json");verify_code(spec);source=Path(spec["source_run"]);batch=read(source/"candidate_batch.json");ps={p["id"]:p for p in batch["ablation_programs"]+batch["programs"]}
    certs={c["id"]:cert for c in batch["candidates"] if (cert:=certificate(ps[c["program_id"]],c)) is not None}
    archived=read(source/"archive.json")["archive"];validation=read(source/"validation_data.json")["candidates"];repairs=[]
    for c in archived:
        if c["id"] not in certs:continue
        pool=[v for v in validation if v["program_id"]==c["program_id"] and v["theta"]==c["theta"] and v["parameter_power"]==c["parameter_power"] and Q(v["log_power"])>0 and v["transfer"]["RH_sufficient_if_uniform"]]
        if pool:
            choice=min(pool,key=lambda v:(bool(v["validation"]["failures"] or v["validation"]["unresolved"]),v["log_reciprocal_cost"] if v.get("log_reciprocal_cost") is not None else 1e100,Q(v["log_power"]),v["id"]))
            repairs.append({"rejected_candidate_id":c["id"],"program":ps[c["program_id"]],"candidate":choice})
    write(directory/"compatibility.json",{"complete_candidates_considered":len(batch["candidates"]),"certificates":certs,"archived_candidates_ruled_out":[c["id"] for c in archived if c["id"] in certs]})
    write(directory/"repairs.json",{"repairs":repairs,"selection_closed":True,"final_data_used":False})
    write(directory/"seal.json",{"protocol_sha256":digest(spec),"selection_closed":True,"final_cases_exist_at_seal":False,
        "files":{n:sha(directory/n) for n in ["protocol.json","compatibility.json","repairs.json"]}})
    print("Sealed Mertens limit gate:",len(certs),"rejections,",len(repairs),"source-batch log repairs",flush=True)


def final(directory):
    spec=read(directory/"protocol.json");verify_code(spec);seal=read(directory/"seal.json");flint.ctx.prec=spec["precision"]
    for n,h in seal["files"].items():assert sha(directory/n)==h
    if (directory/"final_cases.json").exists():raise FileExistsError("Retain final cases")
    seed=int.from_bytes(os.urandom(32),"big");rng=random.Random(seed);rule=spec["fresh_final"];N=rng.randint(*rule["endpoint_range"])
    points=sorted(rng.sample(range(rule["start"],N+1),min(rule["higher_degree_point_count"],N-rule["start"]+1)))
    excluded={q for row in spec["retained_failed_runs_are_development"] for q in row["excluded_q"]}
    qs=sorted(rng.sample([q for q in range(rule["fresh_q_range"][0],rule["fresh_q_range"][1]+1) if q not in excluded],rule["fresh_q_count"]))
    cases={"seed":str(seed),"start":rule["start"],"endpoint":N,"higher_degree_points":points,"fresh_q":qs,"seal_sha256":digest(seal),"created_after_selection_closed":True}
    write(directory/"final_cases.json",cases);repairs=read(directory/"repairs.json")["repairs"];mu=inverse_one_prefix(N);M=[0]*(N+1);m=[Q(0)]*(N+1)
    for n in range(1,N+1):M[n]=M[n-1]+mu[n];m[n]=m[n-1]+Q(mu[n],n)
    responses={};tables={}
    for row in repairs:
        p,c=row["program"],row["candidate"]
        if p["degree"]==0:
            cc,bb=map(Q,(p["coefficients"][0],p["normalizers"][0]));values={f"2:{n}":serialize(real(cc-bb*n*m[n]+(bb-cc)*M[n])) for n in range(rule["start"],N+1)}
        else:
            alphas=sorted({order(p,q,j) for q in qs for j in range(p["degree"]+1)});data=primitive_tables(mu,alphas,points);tables[p["id"]]=data;values=response(p,data,qs,points)
        responses[p["id"]]=values
    outcomes=[dict(comparisons(row["program"],row["candidate"],responses[row["program"]["id"]]),candidate_id=row["candidate"]["id"],
        program_id=row["program"]["id"],complete_point_comparisons=len(responses[row["program"]["id"]]),every_integer_checked=row["program"]["degree"]==0,RH_proved=False) for row in repairs]
    write(directory/"final_evaluation.json",{"protocol_sha256":digest(spec),"seal_sha256":digest(seal),"cases_sha256":digest(cases),
        "complete_coefficient_cutoff":N,"inverse_coefficient_sha256":digest(mu),"Mertens_prefix_sha256":digest(M),"program_responses":responses,"higher_degree_tables":tables,
        "outcomes":outcomes,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False})
    print("Fresh repairs checked through",N,"; uniform proofs still missing",flush=True)


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--run-dir",default="mertens-limit-results/audit-001");ap.add_argument("--source",default="fractional-remainder-results/pilot-002");ap.add_argument("--phase",choices=["run","discover","final"],default="run");a=ap.parse_args();directory=(BASE/a.run_dir).resolve()
    if a.phase=="run":
        directory.mkdir(parents=True,exist_ok=False);write(directory/"protocol.json",protocol(BASE/a.source));frozen=directory/"frozen_source";frozen.mkdir()
        for n in CODE:(frozen/n).write_bytes((BASE/n).read_bytes())
        for phase in ["discover","final"]:subprocess.run([sys.executable,str(BASE/"mertens_limit_audit.py"),"--run-dir",str(directory),"--phase",phase],check=True)
        subprocess.run([sys.executable,str(BASE/"check_mertens_limits.py"),"--run-dir",str(directory)],check=True)
        from mertens_limit_report import publish
        publish(directory)
    elif a.phase=="discover":discover(directory)
    else:final(directory)


if __name__=="__main__":main()

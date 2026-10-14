#!/usr/bin/env python3
"""Signed search ranked by direct ordinary-zeta moment control."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import subprocess
import sys
import flint

from estimate_grammar import inverse_one_prefix
from signed_control_grammar import prefix
from signed_control_search import cell_cases, known_zero_dependency
from stable_scale_search import (protocol as scale_protocol, generate, evaluate,
    restrict, verify_code, final_evaluation, read, write, sha, digest, BASE)
from signed_mellin_transfer import certificate, known_zero_rectangle, reciprocal_bound, real

CODE=["mellin_search.py","check_mellin_search.py","mellin_search_report.py",
      "signed_mellin_transfer.py","check_signed_mellin_transfer.py","signed_mellin_proof.txt"]


def protocol():
    spec=scale_protocol(); spec["schema"]=2; spec["seed"]=2026100787
    spec["code_sha256"].update({name:sha(BASE/name) for name in CODE})
    spec.update({"objective":"Find signed all-scale moment proof obligations sufficient for ordinary-zeta zero exclusion, toward RH",
                 "primary_transfer":"Direct Holder-Mellin exponent eta=(beta-1)/q; a single beta=q/2+1 premise suffices for RH",
                 "primary_obstruction":"A certified actual critical zero with nonzero multiplier rules out eta<1/2",
                 "selection":"baseline and construction-family coverage; otherwise least viable Mellin exponent then quantitative reciprocal cost, including multiplier and interpolation corrections",
                 "primary_cost_line":"sigma=eta+1/8; include the dyadic geometric series and compact interpolation correction",
                 "pointwise_transfer":"retained for comparison, not the primary rank",
                 "finite_final_data_from_prior_pilots":"development evidence only; this run has new evaluator-owned final cases"})
    return spec


def add_direct_transfer(row,zero):
    program=row["program"]; operator=program["operator_certificate"]; atoms=operator["atoms"]
    F=1-sum((real(Q(a))*(-zero*real(d).log()).exp() for d,a in atoms),flint.acb(0))
    nonzero=bool(F.abs_lower()>0); all_height=operator["all_height_critical_multiplier_certified"]
    delta=Q(operator["selected_schur_certificate"]["uniform_multiplier_lower_bound"]) if all_height else None
    scores=[]
    for e in row["estimates"]:
        q,beta,C=e["order"],Q(e["beta"]),Q(e["constant"]); cert=certificate(q,beta,C); eta=Q(cert["mellin_exponent"])
        impossible=nonzero and eta<Q(1,2)
        if impossible: status="ruled_out_by_actual_zeta_zero"
        elif e["sampled_validation_failure_windows"]: status="failed_sampled_validation"
        elif not all_height: status="numerical_lead_missing_global_multiplier_and_uniform_proof"
        else: status="numerical_lead_missing_uniform_signed_moment_proof"
        extra={"certificate":cert,"status":status,"critical_zero_multiplier_nonzero":nonzero,
               "global_multiplier_lower_bound":str(delta) if delta else None}
        if status=="numerical_lead_missing_uniform_signed_moment_proof":
            sigma=eta+Q(1,8); bound=reciprocal_bound(atoms,delta,q,beta,C,sigma)
            cost=float(bound.upper().log())
            extra.update({"cost_line":str(sigma),"conditional_reciprocal_bound_ball":bound.str(35),"log_cost":cost})
            scores.append((eta,cost,q))
        e["direct_mellin_transfer"]=extra
    row["primary_mellin_score"]=[str(scores[0][0]),scores[0][1],scores[0][2]] if scores else None
    if scores:
        best=min(scores); row["primary_mellin_score"]=[str(best[0]),best[1],best[2]]
    row["known_zero_multiplier_lower_ball"]=F.abs_lower().str(35)
    return row


def choose(records,spec):
    def key(r):
        score=r["primary_mellin_score"]
        if score is None: return Q(100),1e100,len(r["program"]["polynomial"]),r["program"]["id"]
        return Q(score[0]),score[1],len(r["program"]["polynomial"]),r["program"]["id"]
    selected=[]
    for family in ("baseline","polynomial_fit","unrestricted_signed","signed_products","learned_compositions"):
        pool=[r for r in records if r["program"]["family"]==family]
        if pool: selected.append(min(pool,key=key))
    for predicate in (lambda r:r["program"]["operator_certificate"].get("outside_triangle_domain_certified") and r["primary_mellin_score"] is not None,
                      lambda r:any(e["direct_mellin_transfer"]["status"]=="numerical_lead_missing_global_multiplier_and_uniform_proof" for e in r["estimates"])):
        pool=[r for r in records if predicate(r)]
        if pool:
            r=min(pool,key=key)
            if r not in selected: selected.append(r)
    for r in sorted(records,key=key):
        if len(selected)>=spec["archive_size"]: break
        if r not in selected: selected.append(r)
    return selected


def discover(directory):
    spec=read(directory/"protocol.json"); verify_code(spec); denied=restrict(directory); flint.ctx.prec=spec["precision"]
    mu=inverse_one_prefix(2*max(spec["validation_scales"])); M=prefix(mu)
    train_cells=cell_cases(spec["training_scales"],spec["development_cells_per_window"],spec["seed"]+1)
    write(directory/"discovery_data.json",{"cells":train_cells,"coefficient_cutoff":len(mu)-1,"inverse_coefficient_sha256":digest(mu)})
    programs,rejected,promotions=generate(mu,M,spec)
    write(directory/"candidate_batch.json",{"programs":programs,"rejected":rejected,"promotions":promotions,
          "frozen_before_validation":True,"protocol_sha256":digest(spec),"discovery_sha256":sha(directory/"discovery_data.json")})
    val_cells=cell_cases(spec["validation_scales"],spec["development_cells_per_window"],spec["seed"]+2)
    dependency=known_zero_dependency(); zero,zero_audit=known_zero_rectangle(dependency)
    records=[]
    for i,p in enumerate(programs):
        r=evaluate(p,mu,M,spec,train_cells,val_cells); records.append(add_direct_transfer(r,zero))
        if i%40==0: print("Direct Mellin development",i,"/",len(programs),flush=True)
    write(directory/"validation_data.json",{"cells":val_cells,"records":records,"moment_observations_are_sampled":True})
    batch=read(directory/"candidate_batch.json")
    archive={"archive":choose(records,spec),"batch_sha256":digest(batch),"worker_access_denials":denied,
             "known_zero_dependency":dependency,"direct_zero_audit":zero_audit,
             "final_data_used":False,"historical_priority_used":False,"uniform_signed_estimate_proved":False}
    write(directory/"archive.json",archive)
    write(directory/"seal.json",{"protocol_sha256":digest(spec),"selection_closed":True,"final_cases_exist_at_seal":False,
          "files":{name:sha(directory/name) for name in ("protocol.json","discovery_data.json","candidate_batch.json","validation_data.json","archive.json")}})
    print("Sealed direct-Mellin archive",len(archive["archive"]),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("mode",choices=("run","discover","final"))
    parser.add_argument("--run-dir",type=Path,required=True); args=parser.parse_args(); directory=args.run_dir.resolve()
    if args.mode=="run":
        if directory.exists(): raise ValueError("A fresh run directory is required")
        directory.mkdir(parents=True); write(directory/"protocol.json",protocol())
        for mode in ("discover","final"):
            subprocess.run([sys.executable,str(Path(__file__)),mode,"--run-dir",str(directory)],check=True,cwd=BASE)
        subprocess.run([sys.executable,str(BASE/"check_mellin_search.py"),"--run-dir",str(directory)],check=True,cwd=BASE)
        from mellin_search_report import publish
        publish(directory)
    elif args.mode=="discover": discover(directory)
    else: final_evaluation(directory)

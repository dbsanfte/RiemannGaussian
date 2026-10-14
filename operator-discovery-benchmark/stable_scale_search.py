#!/usr/bin/env python3
"""Frozen signed scale-polynomial search with unrestricted coefficients."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
import math
import os
from pathlib import Path
import random
import socket
import subprocess
import sys
import flint

from estimate_grammar import inverse_one_prefix
from signed_control_grammar import (prefix, residual, sampled_moments,
    complete_window_moments, positive_control_moment)
from signed_control_search import solve, fit_growth, cell_cases, known_zero_dependency
from stable_scale_grammar import (polynomial, multiply, operator_certificate,
    transfer_certificate, real)

BASE = Path(__file__).resolve().parent
CODE = ["stable_scale_search.py", "stable_scale_grammar.py", "check_stable_scale.py",
        "stable_scale_report.py", "stable_scale_proof.txt", "signed_control_grammar.py",
        "signed_control_search.py", "estimate_grammar.py", "check_signed_control.py"]


def read(path): return json.loads(Path(path).read_text())
def write(path,data): Path(path).write_text(json.dumps(data,indent=2)+"\n")
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def digest(data): return hashlib.sha256(json.dumps(data,sort_keys=True,separators=(",", ":"),allow_nan=False).encode()).hexdigest()


def protocol():
    return {"schema":1,"seed":2026100753,
            "objective":"RH-relevant signed arithmetic operators and full recovery costs, without triangle-contraction projection",
            "code_sha256":{name:sha(BASE/name) for name in CODE},
            "bases":[2,3,4,5,7,9],"maximum_degree":4,"orders":[2,4,6,8],
            "training_scales":list(range(1,16))+[16,24,32,48,64,96,128,192,256,384,512,768,1024,1536,2048,3072,4096],
            "validation_scales":[6144,8192,12289,16384,24577,32768,49157,65536],
            "random_rational_budget":128,"signed_product_budget":96,"learned_composition_budget":24,
            "coefficient_rounding_denominator":256,"coefficient_resource_cap":32,
            "development_cells_per_window":24,
            "generation":"exact weighted least squares; unrestricted signed rationals; products of sampled signed factors; reuse low training-energy polynomials",
            "promotion":"within each base, choose four polynomials of least training response energy; seeded products form reusable compositions before validation",
            "no_stability_projection":True,"unsupported_candidates_retained":True,
            "inverse_prefix_length":64,"certificate":"exact rational Schur disk recursion at four predetermined outer radii, reciprocal prefix plus a Cauchy tail",
            "growth_inference":"training OLS slopes plus declared margin, rational upward rounding; no nominated exponent formula",
            "score_anchor":1073741824,
            "selection":"baseline; best full-cost candidate in each construction family; one outside triangle domain if available; one unsupported candidate; fill by full-cost score",
            "archive_size":8,"precision":352,
            "final_cases":{"large_count":4,"large_range":[131073,499999],"intermediate_count":3,"intermediate_range":[17,8191],"boundary":[1,2,3,15]},
            "negative_control_cells_per_window":24,"maximum_final_cutoff":999998,
            "final_scope":"actual Mobius moments are exact complete windows; delayed-positive controls are labelled sampled cells; all-positive moments are analytic exact integrals",
            "coefficient_source":"constant-one Dirichlet inversion, no prime or factor oracle",
            "generator_model_literature_network_access":False,"historical_priority_is_acceptance_gate":False,
            "remaining_assumptions":["constant-coefficient linear scale polynomials of degree<=4", "six integer bases", "moments through order eight", "available disk certificate backend"],
            "uniform_sublinear_estimate_proved":False}


def verify_code(spec):
    for name,expected in spec["code_sha256"].items():
        if sha(BASE/name)!=expected: raise ValueError("Frozen source changed: "+name)


def restrict(directory):
    allowed={str((BASE/name).resolve()) for name in CODE}
    allowed|={str((directory/name).resolve()) for name in
              ("protocol.json","discovery_data.json","candidate_batch.json","validation_data.json","archive.json","seal.json")}
    allowed|={str((BASE/name).resolve()) for name in
              ("shift-ratio-results/shift_ratio_analytic_verification.json","shift-ratio-results/shift_ratio_analytic.json")}
    def audit(event,args):
        if event=="open" and not isinstance(args[0],int) and str(Path(args[0]).resolve()) not in allowed:
            raise PermissionError("Discovery file access denied")
        if event.startswith("socket.") or event in ("subprocess.Popen","os.system","os.posix_spawn","os.posix_spawnp"):
            raise PermissionError("Discovery external access denied")
    sys.addaudithook(audit)
    denied={}
    for label,action in (("private_final",lambda:open(directory/"final_evaluation.json")),
                         ("network",lambda:socket.socket()),
                         ("subprocess",lambda:subprocess.run([sys.executable,"-c","pass"]))):
        try: action()
        except PermissionError: denied[label]=True
        else: raise AssertionError("Access denial failed")
    return denied


def generate(mu,M,spec):
    rng=random.Random(spec["seed"]); proposals=[("baseline",2,[Q(1)],"unfiltered cumulative signed sum")]
    rejected=[]; scales=[X for X in spec["training_scales"] if X>=16]
    for b in spec["bases"]:
        columns={k:[residual(mu,M,[[b**k,"-1"]],X)-M[X] for X in scales]
                 for k in range(1,spec["maximum_degree"]+1)}
        for degree in range(1,spec["maximum_degree"]+1):
            gram=[[sum((columns[j][i]*columns[k][i]/X for i,X in enumerate(scales)),Q(0))
                   for k in range(1,degree+1)] for j in range(1,degree+1)]
            rhs=[-sum((columns[j][i]*M[X]/X for i,X in enumerate(scales)),Q(0))
                 for j in range(1,degree+1)]
            coefficients=solve(gram,rhs)
            if coefficients is None:
                rejected.append({"base":b,"degree":degree,"reason":"singular exact response matrix"}); continue
            unit=spec["coefficient_rounding_denominator"]
            p=[Q(1)]+[Q(round(c*unit),unit) for c in coefficients]
            proposals.append(("polynomial_fit",b,p,"exact weighted least squares and rational quantization; no stability projection"))
    for _ in range(spec["random_rational_budget"]):
        b=rng.choice(spec["bases"]); degree=rng.randint(1,spec["maximum_degree"])
        p=[Q(1)]+[Q(rng.randint(-64,64),16) for _ in range(degree)]
        proposals.append(("unrestricted_signed",b,p,"seeded signed rational coefficient exploration"))
    for _ in range(spec["signed_product_budget"]):
        b=rng.choice(spec["bases"]); degree=rng.randint(2,spec["maximum_degree"])
        p=[Q(1)]
        for j in range(degree): p=multiply(p,[1,Q(rng.randint(-16,16),8)])
        proposals.append(("signed_products",b,p,"composition of sampled signed scale filters"))
    admissible=[]
    for family,b,p,method in proposals:
        p=polynomial(p)
        if any(abs(c)>spec["coefficient_resource_cap"] for c in p):
            rejected.append({"base":b,"polynomial":[str(c) for c in p],"reason":"declared coefficient resource cap"}); continue
        energy=sum((residual(mu,M,[[b**k,str(-c)] for k,c in enumerate(p) if k and c],X)**2/X for X in scales),Q(0))
        admissible.append((family,b,p,method,energy))
    pools={b:sorted((row for row in admissible if row[1]==b),key=lambda row:(row[4],len(row[2]),str(row[2])))[:4]
           for b in spec["bases"]}
    promotions=[]
    for _ in range(spec["learned_composition_budget"]):
        b=rng.choice(spec["bases"]); pool=pools[b]
        if not pool: continue
        left,right=rng.choice(pool),rng.choice(pool); p=multiply(left[2],right[2])
        if len(p)-1>spec["maximum_degree"] or any(abs(c)>spec["coefficient_resource_cap"] for c in p):
            rejected.append({"base":b,"polynomial":[str(c) for c in p],"reason":"composition resource cap"}); continue
        promotions.append({"base":b,"left":[str(c) for c in left[2]],"right":[str(c) for c in right[2]],"result":[str(c) for c in p]})
        admissible.append(("learned_compositions",b,p,"automatic reuse of low training-energy polynomials",None))
    programs=[]; seen=set()
    for family,b,p,method,energy in admissible:
        encoded=[str(c) for c in p]; key=digest({"base":b,"polynomial":encoded})
        if key in seen:
            rejected.append({"base":b,"polynomial":encoded,"reason":"exact duplicate"}); continue
        seen.add(key); cert=operator_certificate(b,p)
        programs.append({"id":key,"family":family,"base":b,"polynomial":encoded,
                         "method":method,"operator_certificate":cert})
    return programs,rejected,promotions


def evaluate(program,mu,M,spec,train_cells,validation_cells):
    cert=program["operator_certificate"]; rows=cert["atoms"]
    training=sampled_moments(mu,M,rows,spec["training_scales"],spec["orders"],train_cells)
    validation=sampled_moments(mu,M,rows,spec["validation_scales"],spec["orders"],validation_cells)
    estimates=[]; scores=[]
    for q in spec["orders"]:
        e=fit_growth({X:r[q] for X,r in training.items()},q)
        beta,C=Q(e["beta"]),Q(e["constant"]); theta=beta/(q+1)
        failures=[X for X,r in validation.items() if not real(r[q])<=real(C)*real(X)**real(beta)]
        transfer=transfer_certificate(cert,q,beta,C)
        impossible=cert["all_height_critical_multiplier_certified"] and theta<Q(1,2)
        if impossible: status="ruled_out_by_ordinary_zero"
        elif failures: status="failed_sampled_validation"
        elif not transfer["inverse_transfer_certified"]: status="numerical_lead_without_available_global_transfer"
        else: status="numerical_lead_missing_uniform_signed_moment_proof"
        e.update({"sampled_validation_failure_windows":failures,"status":status,"transfer":transfer})
        if status=="numerical_lead_missing_uniform_signed_moment_proof":
            B=flint.arb(transfer["original_M_pointwise_constant_upper_ball"])
            score=B*real(spec["score_anchor"])**real(theta-Q(1,2))
            logarithm=float(score.upper().log())
            e["full_cost_log_score"]=logarithm; scores.append(logarithm)
        estimates.append(e)
    return {"program":program,"sampled_training_moments":{str(X):{str(q):str(v) for q,v in r.items()} for X,r in training.items()},
            "sampled_validation_moments":{str(X):{str(q):str(v) for q,v in r.items()} for X,r in validation.items()},
            "estimates":estimates,"best_full_cost_log_score":min(scores) if scores else None,
            "minimum_fitted_pointwise_exponent":str(min(Q(e["beta"])/(e["order"]+1) for e in estimates))}


def choose(records,spec):
    def key(row):
        s=row["best_full_cost_log_score"]
        return (s if s is not None else 1e100,len(row["program"]["polynomial"]),row["program"]["id"])
    chosen=[]
    for family in ("baseline","polynomial_fit","unrestricted_signed","signed_products","learned_compositions"):
        pool=[r for r in records if r["program"]["family"]==family]
        if pool: chosen.append(min(pool,key=key))
    pool=[r for r in records if r["program"]["operator_certificate"].get("outside_triangle_domain_certified")]
    if pool:
        r=min(pool,key=key)
        if r not in chosen: chosen.append(r)
    pool=[r for r in records if not r["program"]["operator_certificate"]["all_height_critical_multiplier_certified"]]
    if pool:
        # An unsupported lead remains discoverable even when no global inverse
        # certificate is available. This is a separate coverage slot.
        r=min(pool,key=lambda r:(sum(len(e["sampled_validation_failure_windows"]) for e in r["estimates"]),
                                Q(r["minimum_fitted_pointwise_exponent"]),len(r["program"]["polynomial"]),r["program"]["id"]))
        if r not in chosen: chosen.append(r)
    for r in sorted(records,key=key):
        if len(chosen)>=spec["archive_size"]: break
        if r not in chosen: chosen.append(r)
    return chosen


def discover(directory):
    spec=read(directory/"protocol.json"); verify_code(spec); denied=restrict(directory); flint.ctx.prec=spec["precision"]
    mu=inverse_one_prefix(2*max(spec["validation_scales"])); M=prefix(mu)
    train_cells=cell_cases(spec["training_scales"],spec["development_cells_per_window"],spec["seed"]+1)
    write(directory/"discovery_data.json",{"cells":train_cells,"coefficient_cutoff":len(mu)-1,"inverse_coefficient_sha256":digest(mu)})
    programs,rejected,promotions=generate(mu,M,spec)
    batch={"programs":programs,"rejected":rejected,"promotions":promotions,"frozen_before_validation":True,
           "protocol_sha256":digest(spec),"discovery_sha256":sha(directory/"discovery_data.json")}
    write(directory/"candidate_batch.json",batch)
    validation_cells=cell_cases(spec["validation_scales"],spec["development_cells_per_window"],spec["seed"]+2)
    records=[]
    for i,p in enumerate(programs):
        records.append(evaluate(p,mu,M,spec,train_cells,validation_cells))
        if i%40==0: print("Stable scale development",i,"/",len(programs),flush=True)
    write(directory/"validation_data.json",{"cells":validation_cells,"records":records,"moment_observations_are_sampled":True})
    archive={"archive":choose(records,spec),"batch_sha256":digest(batch),"worker_access_denials":denied,
             "known_zero_dependency":known_zero_dependency(),"final_data_used":False,
             "historical_priority_used":False,"uniform_signed_estimate_proved":False}
    write(directory/"archive.json",archive)
    write(directory/"seal.json",{"protocol_sha256":digest(spec),"selection_closed":True,"final_cases_exist_at_seal":False,
           "files":{name:sha(directory/name) for name in ("protocol.json","discovery_data.json","candidate_batch.json","validation_data.json","archive.json")}})
    print("Sealed stable-scale archive",len(archive["archive"]),"operators",flush=True)


def verify_seal(directory):
    spec,seal=read(directory/"protocol.json"),read(directory/"seal.json"); verify_code(spec)
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"]
    for name,expected in seal["files"].items(): assert sha(directory/name)==expected
    return spec,seal


def final_evaluation(directory):
    spec,seal=verify_seal(directory); archive=read(directory/"archive.json"); flint.ctx.prec=spec["precision"]
    path=directory/"final_cases.json"
    if path.exists(): cases=read(path)
    else:
        seed=int.from_bytes(os.urandom(32),"big"); rng=random.Random(seed); rule=spec["final_cases"]
        large=sorted(rng.sample(range(rule["large_range"][0],rule["large_range"][1]+1),rule["large_count"]))
        intermediate=sorted(rng.sample(range(rule["intermediate_range"][0],rule["intermediate_range"][1]+1),rule["intermediate_count"]))
        scales=sorted(rule["boundary"]+intermediate+large)
        cases={"evaluator_seed":str(seed),"large":large,"intermediate":intermediate,"scales":scales,
               "control_cells":cell_cases(large,spec["negative_control_cells_per_window"],seed+1),
               "seal_sha256":digest(seal),"created_after_selection_closed":True}
        write(path,cases)
    assert cases["seal_sha256"]==digest(seal) and cases["created_after_selection_closed"]
    mu=inverse_one_prefix(2*max(cases["scales"])); M=prefix(mu)
    assert len(mu)-1<=spec["maximum_final_cutoff"]
    delayed=mu[:4097]+[1]*(len(mu)-4097); delayed_M=prefix(delayed)
    records=[]
    for i,row in enumerate(archive["archive"]):
        p=row["program"]; path=directory/("final_program_"+p["id"]+".json")
        fingerprint={"archive_sha256":digest(archive),"cases_sha256":digest(cases),"code_sha256":spec["code_sha256"]}
        old=read(path) if path.exists() else {}
        if old.get("fingerprint")==fingerprint:
            records.append(old["record"]); print("Reused stable final",i,flush=True); continue
        rows=p["operator_certificate"]["atoms"]
        exact=complete_window_moments(mu,M,rows,cases["scales"],spec["orders"])
        delay=sampled_moments(delayed,delayed_M,rows,cases["large"],spec["orders"],cases["control_cells"])
        slope=sum((Q(c)/p["base"]**k for k,c in enumerate(p["polynomial"])),Q(0))
        outcomes=[]
        for e in row["estimates"]:
            q,beta,C=e["order"],Q(e["beta"]),Q(e["constant"])
            failures=[X for X,r in exact.items() if not real(r[q])<=real(C)*real(X)**real(beta)]
            positive={X:positive_control_moment(rows,X,q) for X in cases["large"]}
            positive_failures=[X for X,v in positive.items() if not real(v)<=real(C)*real(X)**real(beta)]
            delay_failures=[X for X,r in delay.items() if not real(r[q])<=real(C)*real(X)**real(beta)]
            outcomes.append({"order":q,"complete_final_failure_windows":failures,"finite_windows_passed":not failures,
                             "positive_control_exact_moments":{str(X):str(v) for X,v in positive.items()},
                             "positive_control_failure_windows":positive_failures,
                             "delayed_positive_sampled_moments":{str(X):str(v[q]) for X,v in delay.items()},
                             "delayed_positive_sample_failure_windows":delay_failures,
                             "both_positive_controls_uniform_sublinear_claim_false":bool(slope and beta<q+1),
                             "uniform_moment_premise_proved":False,"reselected":False})
        record={"program_id":p["id"],"exact_complete_window_moments":{str(X):{str(q):str(v) for q,v in r.items()} for X,r in exact.items()},
                "outcomes":outcomes,"every_unit_interval_included":True}
        write(path,{"fingerprint":fingerprint,"record":record}); records.append(record)
        print("Complete stable final",i,p["family"],flush=True)
    write(directory/"final_evaluation.json",{"records":records,"coefficient_cutoff":len(mu)-1,"inverse_coefficient_sha256":digest(mu),
           "seal_sha256":digest(seal),"cases_sha256":digest(cases),"selection_closed_before_final_data":True,
           "uniform_sublinear_signed_controls_verified":[],"RH_proved":False})


def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("mode",choices=("run","discover","final"))
    parser.add_argument("--run-dir",type=Path,required=True); args=parser.parse_args(); directory=args.run_dir.resolve()
    if args.mode=="run":
        if directory.exists(): raise ValueError("A new search requires a fresh destination")
        directory.mkdir(parents=True); write(directory/"protocol.json",protocol())
        for mode in ("discover","final"):
            subprocess.run([sys.executable,str(Path(__file__)),mode,"--run-dir",str(directory)],check=True,cwd=BASE)
        subprocess.run([sys.executable,str(BASE/"check_stable_scale.py"),"--run-dir",str(directory)],check=True,cwd=BASE)
        from stable_scale_report import publish
        publish(directory)
    elif args.mode=="discover": discover(directory)
    else: final_evaluation(directory)


if __name__=="__main__": main()

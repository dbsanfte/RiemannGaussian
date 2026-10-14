#!/usr/bin/env python3
"""Learn signed global-moment recurrences from exact arithmetic windows."""
import argparse
from fractions import Fraction as Q
import json
import math
import os
from pathlib import Path
import random
import subprocess
import sys
import flint

from estimate_grammar import inverse_one_prefix
from signed_control_grammar import prefix,complete_window_moments,positive_control_moment
from stable_scale_search import read,write,sha,digest,restrict,verify_code,BASE
from signed_mellin_transfer import known_zero_rectangle,compact_correction_bound,real
from signed_recurrence_transfer import certificate,mellin_majorant

CODE=["signed_defect_search.py","check_signed_defects.py","signed_defect_report.py",
      "signed_recurrence_transfer.py","signed_recurrence_proof.txt"]


def protocol(source):
    from mellin_search_report import summary
    source=Path(source).resolve(); summary(source)
    archive=read(source/"archive.json"); previous=read(source/"protocol.json")
    hashes=dict(previous["code_sha256"]); hashes.update({name:sha(BASE/name) for name in CODE})
    return {"schema":1,"seed":2026100823,"precision":352,"python_runtime":sys.version,
            "objective":"Infer signed moment defect bounds over every integer scale, targeting an RH-sufficient uniform recurrence",
            "code_sha256":hashes,"source_run":str(source),"source_archive_sha256":sha(source/"archive.json"),
            "source_verification_sha256":sha(source/"verification.json"),
            "input_operators":[r["program"] for r in archive["archive"]],
            "known_zero_dependency":archive["known_zero_dependency"],
            "prior_source_final_data":"previously inspected development evidence; never claimed fresh in this run",
            "orders":[2,4],"training_scales":sorted(set([2**j for j in range(14)]+[3,5,7,11,17,29,47,97,193,389,769,1543,3079,6151])),
            "validation_scales":[16384,16391,24593,32768,32771,49157,65536,65537],
            "moment_data":"exact complete window integrals, including both X and 2X for each defect",
            "coefficient_source":"constant-one Dirichlet inversion; no prime or factor oracle",
            "rho_inference":"median and weighted least-squares response ratios; quantize to 1/64; include signed rescalings, neighbouring powers of two and seeded signed rationals",
            "rho_rounding_denominator":64,"random_rhos_per_program_order":10,
            "gamma_inference":"OLS log positive defects vs log X; nonnegative positive-part majorant; margins 0,1/8,1/4,1/2, rounded upwards to 1/16",
            "gamma_margin_grid":["0","1/8","1/4","1/2"],
            "B_inference":"maximum positive training defect/X^gamma, factor two and upward 1/1024 rounding",
            "zero_positive_defects":"infer gamma=0,B=0 as an explicitly unproved contraction lead",
            "selection":"baseline at each order; construction-family coverage; then RH-sufficient global-bridge recurrences of least complete reciprocal cost; retain one unsupported bridge lead",
            "archive_size":12,"generic_certificate_backend":"|R(t)|<=L*t gives a universal X^(q+1) defect majorant; retain it as calibration, not RH progress",
            "final_cases":{"large_count":4,"large_range":[131073,249999],"intermediate_count":3,"intermediate_range":[17,8191],"boundary":[1,2,3,15]},
            "maximum_final_cutoff":999996,"final_domain":"all integer scales; this is stronger than the dyadic premise needed for RH",
            "final_evaluation":"after sealing, separate process with OS-owned entropy, every unit interval included",
            "negative_controls":["all positive, exact analytic moments","actual Mobius through 4096, then positive, complete exact moments"],
            "model_or_literature_calls":False,"historical_priority_is_acceptance_gate":False,
            "remaining_assumptions":["eight previously sealed scale-polynomial operators","moment orders two and four","bounded linear moment recurrences","stated growth-model alternatives"],
            "finite_success_is_uniform_proof":False}


def pairs(scales): return sorted({x for X in scales for x in (X,2*X)})
def encoded(values): return {str(X):{str(q):str(v) for q,v in r.items()} for X,r in values.items()}


def learned_rhos(values,q,scales,rng,spec):
    ratios=sorted(values[2*X][q]/values[X][q] for X in scales if X>=16 and values[X][q]>0)
    if not ratios: return [(Q(0),"no nonzero responses")]
    median=ratios[len(ratios)//2]
    denominator=sum((values[X][q]**2/X for X in scales if X>=16),Q(0))
    least=sum((values[X][q]*values[2*X][q]/X for X in scales if X>=16),Q(0))/denominator
    unit=spec["rho_rounding_denominator"]
    def quant(x): return Q(round(x*unit),unit)
    proposals=[(Q(0),"zero recurrence coefficient")]
    for x,origin in ((median,"median response ratio"),(least,"weighted least squares"),
                     (ratios[len(ratios)//4],"first-quartile response ratio"),
                     (ratios[3*len(ratios)//4],"third-quartile response ratio")):
        for factor in (Q(-1,2),Q(1,2),Q(1),Q(3,2)):
            proposals.append((quant(x*factor),origin+" times "+str(factor)))
    if median>0:
        exponent=math.floor(math.log2(float(median)))
        power=Q(2)**exponent
        proposals.extend((power*factor,"data-inferred dyadic multiplier") for factor in (Q(1,2),Q(1),Q(2)))
    proposals.extend((Q(rng.randint(-16,64),4),"seeded signed rational exploration")
                     for _ in range(spec["random_rhos_per_program_order"]))
    distinct={}
    for rho,origin in proposals:
        if abs(rho)<=128: distinct.setdefault(rho,origin)
    return sorted(distinct.items())


def slope_of_positive_defects(defects):
    points=[(math.log(X),math.log(float(v))) for X,v in defects.items() if X>=16 and v>0]
    if len(points)<3: return None
    cx=sum(x for x,y in points)/len(points); cy=sum(y for x,y in points)/len(points)
    return sum((x-cx)*(y-cy) for x,y in points)/sum((x-cx)**2 for x,y in points)


def generic_defect_coefficient(program,q,rho):
    L=Q(program["operator_certificate"]["lipschitz_constant"])
    return L**q*Q(4**(q+1)-2**(q+1)+max(-rho,Q(0))*(2**(q+1)-1),q+1)


def infer(program,values,zero,spec,rng):
    operator=program["operator_certificate"]; atoms=operator["atoms"]
    F=1-sum((real(Q(a))*(-zero*real(d).log()).exp() for d,a in atoms),flint.acb(0))
    nonzero=bool(F.abs_lower()>0); all_height=operator["all_height_critical_multiplier_certified"]
    delta=Q(operator["selected_schur_certificate"]["uniform_multiplier_lower_bound"]) if all_height else None
    candidates=[]
    for q in spec["orders"]:
        for rho,origin in learned_rhos(values,q,spec["training_scales"],rng,spec):
            defects={X:values[2*X][q]-rho*values[X][q] for X in spec["training_scales"]}
            positive={X:max(v,Q(0)) for X,v in defects.items()}; slope=slope_of_positive_defects(positive)
            gammas=sorted({min(Q(q+1),max(Q(0),Q(math.ceil(16*(slope+float(Q(m)))),16)))
                           for m in spec["gamma_margin_grid"]}) if slope is not None else [Q(0)]
            for gamma in gammas:
                upper=max((real(v)/real(X)**real(gamma)).upper() for X,v in positive.items())*2*1024
                B=Q(int(upper.ceil().fmpz()),1024)
                transfer=certificate(q,rho,gamma,B,values[1][q])
                elementary=generic_defect_coefficient(program,q,rho)
                generic_proved=gamma>=q+1 and B>=elementary
                transfer["uniform_signed_recurrence_premise_proved"]=generic_proved
                leaf={"program_id":program["id"],"order":q,"rho":str(rho),"gamma":str(gamma),"B":str(B),
                      "rho_origin":origin,"observed_positive_defect_loglog_slope":slope,
                      "positive_training_defects":{str(X):str(v) for X,v in positive.items()},
                      "transfer":transfer,"actual_zero_multiplier_nonzero":nonzero,
                      "all_height_multiplier_nonzero":all_height,
                      "generic_universal_defect_upper_coefficient":str(elementary),
                      "generic_magnitude_premise_proved":generic_proved,
                      "global_multiplier_lower_bound":str(delta) if delta is not None else None}
                if nonzero and transfer["strictly_subcritical_recurrence_ruled_out_if_critical_zero_multiplier_nonzero"]:
                    leaf["analytic_status"]="uniform_recurrence_ruled_out_by_actual_zeta_zero"
                elif not all_height:
                    leaf["analytic_status"]="numerical_lead_missing_all_height_bridge"
                elif transfer["RH_sufficient_with_global_zero_bridge"]:
                    leaf["analytic_status"]="RH_sufficient_recurrence_missing_uniform_arithmetic_proof"
                    sigma=Q(3,4)
                    bound=(mellin_majorant(transfer,sigma)+compact_correction_bound(atoms,sigma))/real(delta)+1/real(sigma)
                    leaf["conditional_reciprocal_bound_ball"]=bound.str(35)
                    leaf["conditional_log_cost"]=float(bound.upper().log())
                elif generic_proved:
                    leaf["analytic_status"]="generic_magnitude_bound_proved_below_RH_strength"
                else: leaf["analytic_status"]="numerical_recurrence_not_at_RH_strength"
                leaf["id"]=digest({k:leaf[k] for k in ("program_id","order","rho","gamma","B")})
                candidates.append(leaf)
    return candidates


def choose(candidates,programs,spec):
    by_id={p["id"]:p for p in programs}
    def key(c):
        status=c["analytic_status"]
        if c["exact_validation_failure_windows"]: level=4
        elif status=="RH_sufficient_recurrence_missing_uniform_arithmetic_proof": level=0
        elif status=="numerical_lead_missing_all_height_bridge": level=2
        elif status=="uniform_recurrence_ruled_out_by_actual_zeta_zero": level=5
        else: level=3
        return level,c.get("conditional_log_cost",1e100),Q(c["gamma"]),abs(Q(c["rho"])),c["id"]
    selected=[]
    baseline=next(p for p in programs if p["family"]=="baseline")
    for q in spec["orders"]:
        pool=[c for c in candidates if c["program_id"]==baseline["id"] and c["order"]==q]
        if pool: selected.append(min(pool,key=key))
    for family in sorted({p["family"] for p in programs}):
        pool=[c for c in candidates if by_id[c["program_id"]]["family"]==family]
        if pool:
            c=min(pool,key=key)
            if c not in selected: selected.append(c)
    pool=[c for c in candidates if c["analytic_status"]=="numerical_lead_missing_all_height_bridge" and not c["exact_validation_failure_windows"]]
    if pool:
        c=min(pool,key=key)
        if c not in selected: selected.append(c)
    for c in sorted(candidates,key=key):
        if len(selected)>=spec["archive_size"]: break
        if c not in selected: selected.append(c)
    return selected


def discover(directory):
    spec=read(directory/"protocol.json"); verify_code(spec); denied=restrict(directory); flint.ctx.prec=spec["precision"]
    train_mu=inverse_one_prefix(4*max(spec["training_scales"])); train_M=prefix(train_mu)
    training={}; candidates=[]; rng=random.Random(spec["seed"])
    zero,zero_audit=known_zero_rectangle(spec["known_zero_dependency"])
    for i,program in enumerate(spec["input_operators"]):
        moments=complete_window_moments(train_mu,train_M,program["operator_certificate"]["atoms"],pairs(spec["training_scales"]),spec["orders"])
        training[program["id"]]=encoded(moments); candidates.extend(infer(program,moments,zero,spec,rng))
        print("Exact defect training operator",i+1,"/",len(spec["input_operators"]),flush=True)
    write(directory/"discovery_data.json",{"moments":training,"coefficient_cutoff":len(train_mu)-1,
          "inverse_coefficient_sha256":digest(train_mu),"every_unit_interval_included":True})
    write(directory/"candidate_batch.json",{"candidates":candidates,"protocol_sha256":digest(spec),
          "training_sha256":sha(directory/"discovery_data.json"),"frozen_before_validation":True,
          "validation_coefficients_not_computed_before_batch_freeze":True})
    mu=inverse_one_prefix(4*max(spec["validation_scales"])); M=prefix(mu); validation={}
    for i,program in enumerate(spec["input_operators"]):
        values=complete_window_moments(mu,M,program["operator_certificate"]["atoms"],pairs(spec["validation_scales"]),spec["orders"])
        validation[program["id"]]=encoded(values)
        for c in candidates:
            if c["program_id"]!=program["id"]: continue
            q,rho,gamma,B=c["order"],Q(c["rho"]),Q(c["gamma"]),Q(c["B"])
            failures=[X for X in spec["validation_scales"] if not real(values[2*X][q]-rho*values[X][q])<=real(B)*real(X)**real(gamma)]
            c["exact_validation_failure_windows"]=failures
        print("Exact defect validation operator",i+1,"/",len(spec["input_operators"]),flush=True)
    write(directory/"validation_data.json",{"moments":validation,"candidates":candidates,"every_unit_interval_included":True,
          "coefficient_cutoff":len(mu)-1,"inverse_coefficient_sha256":digest(mu)})
    write(directory/"archive.json",{"archive":choose(candidates,spec["input_operators"],spec),"worker_access_denials":denied,
          "known_zero_dependency":spec["known_zero_dependency"],"native_zero_audit":zero_audit,
          "final_data_used":False,"historical_priority_used":False,"uniform_RH_sufficient_recurrence_proved":False})
    write(directory/"seal.json",{"protocol_sha256":digest(spec),"selection_closed":True,"final_cases_exist_at_seal":False,
          "files":{name:sha(directory/name) for name in ("protocol.json","discovery_data.json","candidate_batch.json","validation_data.json","archive.json")}})
    print("Sealed signed-defect archive",spec["archive_size"],"from",len(candidates),"learned recurrence estimates",flush=True)


def final(directory):
    spec,seal=read(directory/"protocol.json"),read(directory/"seal.json"); verify_code(spec); flint.ctx.prec=spec["precision"]
    for name,expected in seal["files"].items(): assert sha(directory/name)==expected
    archive=read(directory/"archive.json"); path=directory/"final_cases.json"
    if path.exists(): cases=read(path)
    else:
        seed=int.from_bytes(os.urandom(32),"big"); rng=random.Random(seed); rule=spec["final_cases"]
        large=sorted(rng.sample(range(rule["large_range"][0],rule["large_range"][1]+1),rule["large_count"]))
        intermediate=sorted(rng.sample(range(rule["intermediate_range"][0],rule["intermediate_range"][1]+1),rule["intermediate_count"]))
        cases={"evaluator_seed":str(seed),"large":large,"intermediate":intermediate,"scales":sorted(rule["boundary"]+intermediate+large),
               "seal_sha256":digest(seal),"created_after_selection_closed":True}; write(path,cases)
    assert cases["seal_sha256"]==digest(seal) and cases["created_after_selection_closed"]
    mu=inverse_one_prefix(4*max(cases["scales"])); M=prefix(mu)
    assert len(mu)-1<=spec["maximum_final_cutoff"]
    delayed=mu[:4097]+[1]*(len(mu)-4097); delayed_M=prefix(delayed)
    used={c["program_id"] for c in archive["archive"]}; observed={}; delayed_observed={}
    for i,program in enumerate(p for p in spec["input_operators"] if p["id"] in used):
        checkpoint=directory/("final_program_"+program["id"]+".json")
        fingerprint={"seal_sha256":digest(seal),"cases_sha256":digest(cases),"code_sha256":spec["code_sha256"]}
        old=read(checkpoint) if checkpoint.exists() else {}
        if old.get("fingerprint")==fingerprint:
            observed[program["id"]]=old["actual"]; delayed_observed[program["id"]]=old["delayed"]
            print("Reused final defect operator",i+1,flush=True); continue
        rows=program["operator_certificate"]["atoms"]
        actual=complete_window_moments(mu,M,rows,pairs(cases["scales"]),spec["orders"])
        delay=complete_window_moments(delayed,delayed_M,rows,pairs(cases["large"]),spec["orders"])
        observed[program["id"]]=encoded(actual); delayed_observed[program["id"]]=encoded(delay)
        write(checkpoint,{"fingerprint":fingerprint,"actual":encoded(actual),"delayed":encoded(delay)})
        print("Complete final signed-defect operator",i+1,program["family"],flush=True)
    outcomes=[]; programs={p["id"]:p for p in spec["input_operators"]}
    for c in archive["archive"]:
        q,rho,gamma,B=c["order"],Q(c["rho"]),Q(c["gamma"]),Q(c["B"]); values=observed[c["program_id"]]
        defects={X:Q(values[str(2*X)][str(q)])-rho*Q(values[str(X)][str(q)]) for X in cases["scales"]}
        failures=[X for X,v in defects.items() if not real(v)<=real(B)*real(X)**real(gamma)]
        p=programs[c["program_id"]]; rows=p["operator_certificate"]["atoms"]
        positive={X:positive_control_moment(rows,2*X,q)-rho*positive_control_moment(rows,X,q) for X in cases["large"]}
        delay=delayed_observed[c["program_id"]]
        delay_defects={X:Q(delay[str(2*X)][str(q)])-rho*Q(delay[str(X)][str(q)]) for X in cases["large"]}
        control_failures={name:[X for X,v in values.items() if not real(v)<=real(B)*real(X)**real(gamma)]
                          for name,values in (("all_positive",positive),("delayed_positive",delay_defects))}
        slope=sum((Q(a)/p["base"]**k for k,a in enumerate(p["polynomial"])),Q(0))
        uniform_control_false=bool(slope and rho<2**(q+1) and gamma<q+1)
        outcomes.append({"candidate_id":c["id"],"exact_signed_defects":{str(X):str(v) for X,v in defects.items()},
                         "complete_final_failure_windows":failures,"finite_windows_passed":not failures,
                         "control_exact_defects":{"all_positive":{str(X):str(v) for X,v in positive.items()},
                                                  "delayed_positive":{str(X):str(v) for X,v in delay_defects.items()}},
                         "control_failure_windows":control_failures,"both_positive_control_uniform_claims_false":uniform_control_false,
                         "uniform_signed_recurrence_proved":c["generic_magnitude_premise_proved"],"reselected":False})
    write(directory/"final_evaluation.json",{"seal_sha256":digest(seal),"cases_sha256":digest(cases),"actual_moments":observed,
          "delayed_positive_moments":delayed_observed,"outcomes":outcomes,"coefficient_cutoff":len(mu)-1,
          "inverse_coefficient_sha256":digest(mu),"selection_closed_before_final_data":True,
          "uniform_sublinear_signed_controls_verified":[],"RH_proved":False})


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("mode",choices=("run","discover","final"))
    parser.add_argument("--run-dir",type=Path,required=True); parser.add_argument("--source-run",type=Path)
    args=parser.parse_args(); directory=args.run_dir.resolve()
    if args.mode=="run":
        if directory.exists() or args.source_run is None: raise ValueError("A fresh destination and source run are required")
        directory.mkdir(parents=True); write(directory/"protocol.json",protocol(args.source_run))
        for mode in ("discover","final"):
            subprocess.run([sys.executable,str(Path(__file__)),mode,"--run-dir",str(directory)],check=True,cwd=BASE)
        subprocess.run([sys.executable,str(BASE/"check_signed_defects.py"),"--run-dir",str(directory)],check=True,cwd=BASE)
        from signed_defect_report import publish
        publish(directory)
    elif args.mode=="discover": discover(directory)
    else: final(directory)

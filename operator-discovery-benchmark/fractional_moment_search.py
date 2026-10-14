#!/usr/bin/env python3
"""Frozen rational-root and fractional-moment search toward signed RH control."""
import argparse
from fractions import Fraction as Q
import math
import os
from pathlib import Path
import random
import socket
import subprocess
import sys
import flint

from estimate_grammar import inverse_one_prefix
from exact_arithmetic import normalized_power
from signed_control_grammar import prefix
from stable_scale_search import read, write, sha, digest, verify_code, BASE
from signed_mellin_transfer import known_zero_rectangle, compact_correction_bound
from rational_power_grammar import (VERSION, real, complex_power, power_certificate,
    complete_absolute_moments, unit_absolute_moment, transfer_certificate)

CODE = ["rational_power_grammar.py", "rational_power_proof.txt",
        "fractional_moment_search.py", "check_fractional_moments.py", "fractional_moment_report.py",
        "exact_arithmetic.py"]


def orders(max_denominator, seed):
    rng = random.Random(seed)
    result = {Q(n) for n in range(1,5)} | {Q(1,d) for d in range(1,max_denominator+1)}
    for d in range(2,max_denominator+1):
        choices = [Q(p,d) for p in range(d+1,4*d+1) if math.gcd(p,d)==1]
        result.add(rng.choice(choices))
    return sorted(result)


def protocol(source, max_denominator):
    from mellin_search_report import summary
    source=Path(source).resolve(); summary(source)
    previous=read(source/"protocol.json"); archive=read(source/"archive.json")
    if not 2 <= max_denominator <= 64: raise ValueError("Pilot resource limit: 2..64; semantics allow other denominators")
    hashes=dict(previous["code_sha256"]); hashes.update({name:sha(BASE/name) for name in CODE})
    seed=2026100901
    return {"schema":1,"grammar_version":VERSION,"seed":seed,"precision":320,
        "objective":"Search signed rational-root programs and fractional moments, with audited recovery to the ordinary-zeta obstruction",
        "code_sha256":hashes,"source_run":str(source),"source_archive_sha256":sha(source/"archive.json"),
        "source_verification_sha256":sha(source/"verification.json"),"source_protocol":previous,
        "input_operators":[r["program"] for r in archive["archive"]],"known_zero_dependency":archive["known_zero_dependency"],
        "max_denominator":max_denominator,"semantic_denominator_ceiling":None,
        "orders":[str(q) for q in orders(max_denominator,seed)],
        "root_programs":"For effective q=p/d, use signed S_(1/d)(R) with outer absolute moment p; store inverse S_d and effective order q",
        "additional_language":"composed rational powers, signed sums/products/divisions, absolute powers, declared principal complex powers, exact normalized Dirichlet powers",
        "training_scales":sorted({2**j for j in range(12)}|{3,5,7,11,17,47,97,193,389,769,1543}),
        "validation_scales":[4096,6145,8192,8197,12289,16384,16391],
        "moment_evaluation":"certified algebraic antiderivatives on every unit interval; no quadrature sampling",
        "coefficient_source":"constant-one Dirichlet inversion without a prime or factor oracle",
        "growth_inference":"OLS log midpoint moments at X>=16; margins 0,1/8,1/4; upward grid 1/(16*order denominator); constant factor two with upward 1/1024 rounding",
        "growth_margins":["0","1/8","1/4"],"archive_size":max_denominator+6,
        "selection":"one baseline per root denominator, construction coverage, one order below one and one unsupported multiplier; fill by viable Mellin exponent and reciprocal cost",
        "transfer":"Holder for effective q>=1; Lipschitz peak to L1 for 0<q<1; no root-amplitude shortcut",
        "final_cases":{"large_count":3,"large_range":[32769,65535],"intermediate_count":3,"intermediate_range":[17,2047],"boundary":[1,2,3,15]},
        "maximum_final_cutoff":131070,"delayed_positive_cutoff":2048,
        "negative_controls":"all-positive analytic complete moments; actual inverse through 2048 then positive, complete certified moments",
        "generic_final_sequences":{"count":5,"cutoffs":[17,31,48,65,97],"denominator":13,"integer_range":[-21,21]},
        "zeta_root_calibration":{"cutoff":128,"real_part":4,"height_denominator":17,"height_integer_range":[-1000,1000],"cases":3,"tail_u":2},
        "existing_Dirichlet_power_semantics":"exact_arithmetic.normalized_power already accepted all rational exponents; this stage exposes them to the new search and audits them",
        "prior_final_data_is_development_only":True,"model_or_literature_calls":False,
        "historical_priority_is_acceptance_gate":False,"finite_success_is_uniform_proof":False,
        "remaining_assumptions":["eight previously sealed linear residuals","finite denominator and order sampling budget","power growth models","available linear Mellin and Lipschitz proof backends"]}


def restrict(directory, spec):
    allowed={str((BASE/name).resolve()) for name in spec["code_sha256"]}
    allowed|={str((directory/name).resolve()) for name in ("protocol.json","discovery_data.json","candidate_batch.json","validation_data.json","archive.json","seal.json")}
    allowed|={str((BASE/name).resolve()) for name in ("shift-ratio-results/shift_ratio_analytic_verification.json","shift-ratio-results/shift_ratio_analytic.json")}
    def audit(event,args):
        if event=="open" and not isinstance(args[0],int) and str(Path(args[0]).resolve()) not in allowed:
            raise PermissionError("Fractional discovery file access denied")
        if event.startswith("socket.") or event in ("subprocess.Popen","os.system","os.posix_spawn","os.posix_spawnp"):
            raise PermissionError("Fractional discovery external access denied")
    sys.addaudithook(audit)
    denied={}
    for label,action in (("private_final",lambda:open(directory/"final_evaluation.json")),("network",lambda:socket.socket()),("subprocess",lambda:subprocess.run([sys.executable,"-c","pass"]))):
        try: action()
        except PermissionError: denied[label]=True
        else: raise AssertionError("Discovery isolation failed")
    return denied


def encoded(values):
    # A declared outward audit margin also covers exact-point outputs when
    # the independent logarithm-based evaluation has a tiny nonzero radius.
    def enclosure(v):
        return (v+flint.arb(0,real(Q(1,2**200))*(1+abs(v)))).str(45)
    return {str(X):{str(q):enclosure(v) for q,v in row.items()} for X,row in values.items()}


def slope(values,q,scales):
    points=[(math.log(X),float(values[X][q].mid().log())) for X in scales if X>=16 and values[X][q]>0]
    if len(points)<3: return 0.0
    cx=sum(x for x,y in points)/len(points); cy=sum(y for x,y in points)/len(points)
    return sum((x-cx)*(y-cy) for x,y in points)/sum((x-cx)**2 for x,y in points)


def infer(program,values,zero,spec):
    operator=program["operator_certificate"]; rows=operator["atoms"]
    F=1-sum((real(a)*(-zero*real(d).log()).exp() for d,a in rows),flint.acb(0))
    nonzero=bool(F.abs_lower()>0); all_height=operator["all_height_critical_multiplier_certified"]
    delta=Q(operator["selected_schur_certificate"]["uniform_multiplier_lower_bound"]) if all_height else None
    result=[]
    for q in map(Q,spec["orders"]):
        growth=slope(values,q,spec["training_scales"]); grid=16*q.denominator
        exponents=sorted({max(Q(0),min(q+1,Q(math.ceil(grid*(growth+float(Q(m)))),grid))) for m in spec["growth_margins"]})
        for beta in exponents:
            top=max((values[X][q]/real(X)**real(beta)).upper() for X in spec["training_scales"])
            C=Q(int((top*2048).ceil().fmpz()),1024)
            if C<=0: C=Q(1,1024)
            transfer=transfer_certificate(q,beta,C,operator["lipschitz_constant"])
            eta=Q(transfer["mellin_exponent"])
            if nonzero and eta<Q(1,2): status="uniform_estimate_ruled_out_by_actual_zeta_zero"
            elif not all_height: status="numerical_lead_missing_all_height_multiplier"
            elif eta<=Q(1,2): status="RH_sufficient_obligation_missing_uniform_signed_proof"
            else: status="numerical_signed_obligation_above_RH_threshold"
            candidate={"program_id":program["id"],"effective_order":str(q),"root_exponent":str(Q(1,q.denominator)),
                "outer_moment_order":q.numerator,"inverse_exponent":str(q.denominator),
                "root_certificate":power_certificate(Q(1,q.denominator),"signed"),
                "beta":str(beta),"constant":str(C),"observed_loglog_slope":growth,"transfer":transfer,
                "analytic_status":status,"actual_zero_multiplier_nonzero":nonzero,"all_height_multiplier_nonzero":all_height,
                "global_multiplier_lower_bound":str(delta) if delta else None}
            if all_height and eta>=Q(1,2):
                sigma=eta+Q(1,8)
                coeff=flint.arb(transfer["mellin_bound_coefficient_ball"])
                integral=coeff/(1-real(2)**real(eta-sigma))
                bound=(integral+compact_correction_bound(rows,sigma))/real(delta)+1/real(sigma)
                candidate.update({"cost_line":str(sigma),"conditional_reciprocal_bound_ball":bound.str(45),"log_cost":float(bound.upper().log())})
            candidate["id"]=digest({k:candidate[k] for k in ("program_id","effective_order","beta","constant")})
            result.append(candidate)
    return result


def choose(candidates,spec):
    by_id={p["id"]:p for p in spec["input_operators"]}
    def key(c):
        status=c["analytic_status"]; eta=Q(c["transfer"]["mellin_exponent"])
        rank=0 if status=="RH_sufficient_obligation_missing_uniform_signed_proof" else (1 if status=="numerical_signed_obligation_above_RH_threshold" else 2)
        if status=="uniform_estimate_ruled_out_by_actual_zeta_zero": rank=4
        if c["validation_failures"] or c["validation_unresolved"]: rank=5
        return rank,eta,c.get("log_cost",1e100),c["id"]
    selected=[]
    def add(pool):
        if pool:
            pick=min(pool,key=key)
            if pick not in selected: selected.append(pick)
    baseline=next(p for p in spec["input_operators"] if p["family"]=="baseline")
    for d in range(1,spec["max_denominator"]+1):
        add([c for c in candidates if c["program_id"]==baseline["id"] and Q(c["effective_order"]).denominator==d])
    for family in sorted({p["family"] for p in spec["input_operators"]}):
        add([c for c in candidates if by_id[c["program_id"]]["family"]==family])
    add([c for c in candidates if Q(c["effective_order"])<1])
    add([c for c in candidates if not c["all_height_multiplier_nonzero"]])
    for c in sorted(candidates,key=key):
        if len(selected)>=spec["archive_size"]: break
        if c not in selected: selected.append(c)
    return selected


def comparison(value, bound):
    if value <= bound: return "pass"
    if value > bound: return "fail"
    return "unresolved"


def discover(directory):
    spec=read(directory/"protocol.json"); verify_code(spec); denied=restrict(directory,spec)
    flint.ctx.prec=spec["precision"]; qs=list(map(Q,spec["orders"]))
    mu=inverse_one_prefix(2*max(spec["training_scales"])); M=prefix(mu)
    training={}; candidates=[]
    zero,zero_audit=known_zero_rectangle(spec["known_zero_dependency"])
    for i,p in enumerate(spec["input_operators"]):
        values=complete_absolute_moments(mu,M,p["operator_certificate"]["atoms"],spec["training_scales"],qs)
        training[p["id"]]=encoded(values); candidates.extend(infer(p,values,zero,spec))
        print("Fractional training",i+1,"/",len(spec["input_operators"]),flush=True)
    write(directory/"discovery_data.json",{"moments":training,"coefficient_cutoff":len(mu)-1,"inverse_coefficient_sha256":digest(mu)})
    write(directory/"candidate_batch.json",{"candidates":candidates,"frozen_before_validation":True,"protocol_sha256":digest(spec),"discovery_sha256":sha(directory/"discovery_data.json")})
    mu=inverse_one_prefix(2*max(spec["validation_scales"])); M=prefix(mu); validation={}
    for i,p in enumerate(spec["input_operators"]):
        values=complete_absolute_moments(mu,M,p["operator_certificate"]["atoms"],spec["validation_scales"],qs)
        validation[p["id"]]=encoded(values)
        for c in candidates:
            if c["program_id"]!=p["id"]: continue
            q,beta,C=map(Q,(c["effective_order"],c["beta"],c["constant"]))
            states={X:comparison(row[q],real(C)*real(X)**real(beta)) for X,row in values.items()}
            c["validation_failures"]=[X for X,s in states.items() if s=="fail"]
            c["validation_unresolved"]=[X for X,s in states.items() if s=="unresolved"]
        print("Fractional validation",i+1,flush=True)
    write(directory/"validation_data.json",{"moments":validation,"candidates":candidates})
    write(directory/"archive.json",{"archive":choose(candidates,spec),"worker_access_denials":denied,"native_zero_audit":zero_audit,
          "batch_sha256":sha(directory/"candidate_batch.json"),"final_data_used":False,"uniform_signed_arithmetic_proof":False})
    write(directory/"seal.json",{"protocol_sha256":digest(spec),"selection_closed":True,"final_cases_exist_at_seal":False,
          "files":{name:sha(directory/name) for name in ("protocol.json","discovery_data.json","candidate_batch.json","validation_data.json","archive.json")}})
    print("Sealed fractional archive",len(choose(candidates,spec)),"from",len(candidates),flush=True)


def final(directory):
    spec,seal=read(directory/"protocol.json"),read(directory/"seal.json"); verify_code(spec); flint.ctx.prec=spec["precision"]
    for name,expected in seal["files"].items(): assert sha(directory/name)==expected
    archive=read(directory/"archive.json"); path=directory/"final_cases.json"
    if path.exists(): cases=read(path)
    else:
        seed=int.from_bytes(os.urandom(32),"big"); rng=random.Random(seed); rule=spec["final_cases"]
        large=sorted(rng.sample(range(rule["large_range"][0],rule["large_range"][1]+1),rule["large_count"]))
        intermediate=sorted(rng.sample(range(rule["intermediate_range"][0],rule["intermediate_range"][1]+1),rule["intermediate_count"]))
        generic_rule=spec["generic_final_sequences"]
        generic=[["1"]+[str(Q(rng.randint(*generic_rule["integer_range"]),generic_rule["denominator"])) for _ in range(N-1)] for N in generic_rule["cutoffs"]]
        zr=spec["zeta_root_calibration"]
        heights=[str(Q(rng.randint(*zr["height_integer_range"]),zr["height_denominator"])) for _ in range(zr["cases"])]
        cases={"evaluator_seed":str(seed),"large":large,"intermediate":intermediate,"scales":sorted(set(rule["boundary"]+intermediate+large)),
               "generic_normalized_sequences":generic,"zeta_heights":heights,"seal_sha256":digest(seal),"created_after_selection_closed":True}
        write(path,cases)
    assert cases["seal_sha256"]==digest(seal)
    mu=inverse_one_prefix(2*max(cases["scales"])); M=prefix(mu)
    cutoff=spec["delayed_positive_cutoff"]; delayed=mu[:cutoff+1]+[1]*(len(mu)-cutoff-1); delayed_M=prefix(delayed)
    used={c["program_id"] for c in archive["archive"]}; moments={}; delayed_moments={}
    for i,p in enumerate(p for p in spec["input_operators"] if p["id"] in used):
        qs=sorted({Q(c["effective_order"]) for c in archive["archive"] if c["program_id"]==p["id"]})
        path=directory/("final_program_"+p["id"]+".json")
        fingerprint={"seal_sha256":digest(seal),"cases_sha256":digest(cases),"code_sha256":spec["code_sha256"]}
        old=read(path) if path.exists() else {}
        if old.get("fingerprint")==fingerprint:
            actual,delay=old["actual"],old["delayed"]
        else:
            actual=encoded(complete_absolute_moments(mu,M,p["operator_certificate"]["atoms"],cases["scales"],qs))
            delay=encoded(complete_absolute_moments(delayed,delayed_M,p["operator_certificate"]["atoms"],cases["large"],qs))
            write(path,{"fingerprint":fingerprint,"actual":actual,"delayed":delay})
        moments[p["id"]]=actual; delayed_moments[p["id"]]=delay
        print("Complete fractional final operator",i+1,p["family"],"orders",list(map(str,qs)),flush=True)
    by_id={p["id"]:p for p in spec["input_operators"]}; outcomes=[]
    for c in archive["archive"]:
        q,beta,C=map(Q,(c["effective_order"],c["beta"],c["constant"])); pid=c["program_id"]
        states={X:comparison(flint.arb(moments[pid][str(X)][str(q)]),real(C)*real(X)**real(beta)) for X in cases["scales"]}
        p=by_id[pid]; slope=sum((Q(a)/p["base"]**k for k,a in enumerate(p["polynomial"])),Q(0))
        positive={X:unit_absolute_moment(X*slope,2*X*slope,q)*X for X in cases["large"]}
        delay={X:flint.arb(delayed_moments[pid][str(X)][str(q)]) for X in cases["large"]}
        control_states={name:{str(X):comparison(v,real(C)*real(X)**real(beta)) for X,v in values.items()} for name,values in (("positive",positive),("delayed",delay))}
        outcomes.append({"candidate_id":c["id"],"window_comparisons":{str(X):v for X,v in states.items()},
            "finite_windows_passed":all(v=="pass" for v in states.values()),"positive_control_moment_balls":{str(X):v.str(45) for X,v in positive.items()},
            "control_comparisons":control_states,"both_positive_control_uniform_claims_false":bool(slope and beta<q+1),
            "uniform_signed_moment_premise_proved":False,"reselected":False})
    roots=[]
    for d in range(2,spec["max_denominator"]+1):
        for a in (Q(1,d),Q(-1,d)):
            generic=[list(map(str,normalized_power([Q(0)]+list(map(Q,f)),a)[1:])) for f in cases["generic_normalized_sequences"]]
            zr=spec["zeta_root_calibration"]; N=zr["cutoff"]
            coeff=normalized_power([Q(0)]+[Q(1)]*N,a)
            native=[]
            for height in cases["zeta_heights"]:
                s=flint.acb(zr["real_part"],real(height)); value=complex_power(s.zeta(),a)
                partial=sum((real(coeff[n])*(-s*real(n).log()).exp() for n in range(1,N+1)),flint.acb(0))
                tail=real(N)**real(-zr["tail_u"])*(real(zr["real_part"]-zr["tail_u"]).zeta())**real(abs(a))
                assert abs(value-partial).upper()<tail.lower()
                native.append({"height":height,"value":[value.real.str(45),value.imag.str(45)],"partial":[partial.real.str(45),partial.imag.str(45)],"tail_bound_ball":tail.str(45)})
            roots.append({"exponent":str(a),"generic_exact_coefficients":generic,"zeta_exact_coefficients":list(map(str,coeff[1:])),"native_zeta_checks":native})
    write(directory/"final_evaluation.json",{"seal_sha256":digest(seal),"cases_sha256":digest(cases),"actual_moments":moments,
        "delayed_positive_moments":delayed_moments,"outcomes":outcomes,"Dirichlet_root_calibrations":roots,
        "coefficient_cutoff":len(mu)-1,"inverse_coefficient_sha256":digest(mu),"selection_closed_before_final_data":True,
        "uniform_sublinear_signed_controls_verified":[],"RH_proved":False})


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("mode",choices=("run","discover","final"))
    parser.add_argument("--run-dir",type=Path,required=True); parser.add_argument("--source-run",type=Path)
    parser.add_argument("--max-denominator",type=int,default=12)
    args=parser.parse_args(); directory=args.run_dir.resolve()
    if args.mode=="run":
        if directory.exists() or args.source_run is None: raise ValueError("Fresh destination and a verified source run are required")
        directory.mkdir(parents=True); write(directory/"protocol.json",protocol(args.source_run,args.max_denominator))
        for mode in ("discover","final"):
            subprocess.run([sys.executable,str(Path(__file__)),mode,"--run-dir",str(directory)],check=True,cwd=BASE)
        subprocess.run([sys.executable,str(BASE/"check_fractional_moments.py"),"--run-dir",str(directory)],check=True,cwd=BASE)
        from fractional_moment_report import publish
        publish(directory)
    elif args.mode=="discover": discover(directory)
    else: final(directory)

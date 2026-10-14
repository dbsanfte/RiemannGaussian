#!/usr/bin/env python3
"""Frozen empirical family search with generic parameter-pole proof backends."""
import argparse
from collections import Counter
from fractions import Fraction as Q
import itertools
import math
import os
from pathlib import Path
import random
import socket
import subprocess
import sys

import flint
from estimate_grammar import inverse_one_prefix
from fractional_prime_grammar import forward
from prime_error_grammar import real,serialize
from stable_scale_search import BASE,read,write,sha,digest,verify_code
from signed_control_search import known_zero_dependency
from fractional_remainder_grammar import (VERSION,canonical,order,primitive_tables,response,
    cauchy_boxes,global_certificate,transfer,power,recovery_cost,complex_ball)
from fractional_remainder_analytic import numerator

CODE=["fractional_remainder_grammar.py","fractional_remainder_analytic.py","fractional_remainder_search.py",
      "check_fractional_remainders.py","fractional_remainder_report.py","fractional_remainder_proof.txt"]


def protocol(source):
    from prime_oscillation_report import summary
    source=Path(source).resolve();parent=summary(source);spec=read(source/"protocol.json")
    zero=known_zero_dependency();failed=[]
    for path in sorted((BASE/"fractional-remainder-results").glob("*/failure.json")):
        run=path.parent;old=read(run/"protocol.json");cases=read(run/"final_cases.json")
        failed.append({"run_directory":str(run),"failure_sha256":sha(path),"protocol_sha256":sha(run/"protocol.json"),
            "final_sha256":sha(run/"final_evaluation.json"),"final_cases_sha256":sha(run/"final_cases.json"),
            "excluded_integer_scales":cases["integers"],"excluded_fresh_q":cases["fresh_q"],"original_source_sha256":{n:old["code_sha256"][n] for n in old["this_stage_source_files"]}})
    return {"schema":1,"grammar_version":VERSION,"precision":288,"seed":2026100831,
        "source_run":str(source),"source_sha256":{n:sha(source/n) for n in ("protocol.json","verification.json","summary.json")},
        "code_sha256":dict(spec["code_sha256"],**{n:sha(BASE/n) for n in CODE+["fractional_prime_grammar.py","fractional_prime_proof.txt"]}),
        "this_stage_source_files":CODE,"known_critical_zero_dependency":zero,
        "fixed_baseline":{"maximum_degree":3,"enum_coefficients":[-1,0,1],"enum_per_degree":12,
            "random_budget":24,"product_budget":24,"normalizer_mutation_budget":12,"coefficient_resource_cap":16},
        "adaptive_mode":{"least_squares_rounding_denominator":64,"moment_nullspaces":True,"promotion_budget":12,"promotion_pool":4,
            "promotion_rule":"take four low training-energy compensated programs per degree after dividing by their exact parameter order; sample degree-admissible products; preserve dependency expressions",
            "ablation":"same baseline and learned fits; replace the 12 promotion proposal slots by frozen-seed random proposals"},
        "training_points":[1,2,3,4,8,12,16,24,32,48,64,96,128,192,256,384,512,768,1024],
        "validation_points":[1536,1793,2048,2561,3072,4096],"training_q":[2,3,6,12],"validation_new_q":[5,10,17],
        "growth_grid":["0","1/4","1/2","3/4","1"],"parameter_grid":["0","1/2","1","3/2","2","5/2","3","7/2"],
        "log_grid":["0","1/2","1","2"],"fitted_exponents":"two-feature OLS on log(n), log(a); theta rounded upward to 1/16 with 1/16 margin; kappa nearest 1/16; exact vanishing order also admitted",
        "constant_rule":"training interval maximum, factor 3/2, upward 1/1024 quantization; minimum 1/1024",
        "certificate_radii":["1/4","1/2","3/4"],"certificate_mesh":8,
        "cost_query":["5/8","16"],"native_numerator_parameters":{"K":80,"U":64,"terms":16},
        "archive_size":12,"selection":"baseline; best RH-compatible full-cost candidate per generation family and exact parameter order; fill by validation failures and charged cost; retain above-threshold numerical lead",
        "final_cases":{"integer_count":4,"integer_range":[4097,8192],"fresh_q_count":3,"fresh_q_range":[19,97],"boundary":[1,2,3],"real_offset":"1/3","generic_unit_count":6,"generic_cutoff":24},
        "analytic_scope":"bounds require every n>=1 AND every q>=2; finite order grids never supply the universal premise",
        "coefficient_source":"constant-one triangular logarithm and Dirichlet inversion; no prime labels or index-factor oracle",
        "final_freshness_scope":"new observables, points and order parameters; Mobius coefficients overlap prior research data",
        "development_before_freeze":"implementation preflight exercised the training generator and scalar enclosures; preflight overlaps are development, not fresh final evidence; no archive or actual full-cost outcome was inspected",
        "retained_failed_runs_are_development":failed,
        "supplied_backends":["fractional discrete/continuous Mellin identity","parameter-pole identity-theorem bridge","exact parameter rate","reciprocal-gamma Cauchy cover","weak signed parameter and unit bounds"],
        "not_autonomous_proof_invention":True,"generator_model_literature_network_access":False,
        "historical_priority_is_acceptance_gate":False,"imported_prime_distribution_estimate":False,
        "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}


def restrict(directory):
    allowed={str((BASE/n).resolve()) for n in read(directory/"protocol.json")["code_sha256"]}
    allowed|={str((directory/n).resolve()) for n in ("protocol.json","discovery_data.json","candidate_batch.json","validation_data.json","archive.json","seal.json","backend_certificates.json","numerator_data.json")}
    def audit(event,args):
        if event=="open" and not isinstance(args[0],int) and str(Path(args[0]).resolve()) not in allowed:
            raise PermissionError("Discovery file access denied")
        if event.startswith("socket.") or event in ("subprocess.Popen","os.system","os.posix_spawn","os.posix_spawnp"):
            raise PermissionError("Discovery external access denied")
    sys.addaudithook(audit);denied={}
    for key,action in (("private_final",lambda:open(directory/"final_evaluation.json")),("network",lambda:socket.socket()),
                       ("subprocess",lambda:subprocess.run([sys.executable,"-c","pass"]))):
        try:action()
        except PermissionError:denied[key]=True
        else:raise AssertionError("Expected evaluator isolation")
    return denied


def solve(A,b):
    A=[list(row)+[rhs] for row,rhs in zip(A,b)];N=len(b)
    for k in range(N):
        pivot=next((j for j in range(k,N) if A[j][k]),None)
        if pivot is None:return None
        A[k],A[pivot]=A[pivot],A[k];v=A[k][k];A[k]=[x/v for x in A[k]]
        for j in range(N):
            if j!=k:
                v=A[j][k];A[j]=[x-v*y for x,y in zip(A[j],A[k])]
    return [row[-1] for row in A]


def multiply(c,d):
    out=[Q(0)]*(len(c)+len(d)-1)
    for j,v in enumerate(c):
        for k,w in enumerate(d):out[j+k]+=v*w
    return out


def alpha_set(max_degree,qs,anchor=False):
    out={Q(j,D*q) for D in range(1,max_degree+1) for q in qs for j in range(D+1)}
    if anchor:out.add(Q(1))
    return sorted(out)


def generate(spec,data):
    rule=spec["fixed_baseline"];adapt=spec["adaptive_mode"];Dmax=rule["maximum_degree"];rng=random.Random(spec["seed"])
    proposals=[];rejections=[]
    def add(family,c,b=None,method=None):proposals.append((family,c,b,method or family))
    add("baseline",[1],[1],"supplied zero-order anchor; discovery may select other families")
    for b in [-1,0,2]:add("independent_zero_normalizer",[1],[b])
    for D in range(1,Dmax+1):
        rows=[]
        for c in itertools.product(rule["enum_coefficients"],repeat=D+1):
            if not c[-1] or not any(c):continue
            p=canonical(c);rows.append(p["coefficients"])
        unique={tuple(c) for c in rows}
        for c in sorted(unique,key=lambda c:(sum(abs(Q(v)) for v in c),c))[:rule["enum_per_degree"]]:add("enumerated",c)
    def random_row(rng):
        D=rng.randint(1,Dmax);return [Q(1)]+[Q(rng.randint(-8,8),4) for _ in range(D)]
    for _ in range(rule["random_budget"]):add("signed_rational",random_row(rng))
    for _ in range(rule["product_budget"]):
        c=[Q(1)]
        for j in range(rng.randint(1,Dmax)):c=multiply(c,[Q(1),Q(rng.randint(-4,4),2)])
        add("signed_products",c,method="composition of sampled rational two-term parameter-label polynomials")
    # Generic moment-nullspace production; no nominated winning stencil.
    for D in range(1,Dmax+1):
        for r in range(1,D+1):
            free=[Q(rng.randint(-4,4),2) for _ in range(D-r)]
            A=[[Q(j**k) for j in range(1,r+1)] for k in range(r)]
            b=[-Q(0**k)-sum((v*j**k for j,v in enumerate(free,r+1)),Q(0)) for k in range(r)]
            tail=solve(A,b)
            if tail is not None:add("moment_nullspace",[Q(1)]+tail+free,method=f"exact nullspace of {r} integer-label moments; free coordinates seeded")
    # Learn coefficient combinations from observed primitive responses.
    for D in range(1,Dmax+1):
        rows=[]
        for q in spec["training_q"]:
            for n in spec["training_points"]:
                if n<16:continue
                row=[Q(round(float(flint.arb(data[str(Q(j,D*q))][str(n)]["remainder"]).mid())*2**40),2**40) for j in range(D+1)]
                rows.append((n,row))
        gram=[[sum((row[j]*row[k]/n for n,row in rows),Q(0)) for k in range(1,D+1)] for j in range(1,D+1)]
        rhs=[-sum((row[j]*row[0]/n for n,row in rows),Q(0)) for j in range(1,D+1)]
        c=solve(gram,rhs)
        if c is not None:add("learned_linear_relation",[Q(1)]+[Q(round(v*adapt["least_squares_rounding_denominator"]),adapt["least_squares_rounding_denominator"]) for v in c],method="exact least squares on quantized anonymous remainder columns")
    baseline=[];seen=set()
    def admit(family,c,b,method,pool):
        if not any(map(Q,list(c)+(list(b) if b is not None else []))):
            rejections.append({"family":family,"reason":"zero program","c":list(map(str,c))});return
        p=canonical(c,b);key=digest(p)
        if max(map(abs,map(Q,p["coefficients"]+p["normalizers"])))>rule["coefficient_resource_cap"] or p["degree"]>Dmax:
            rejections.append({"family":family,"program":p,"reason":"declared coefficient/degree resource cap"});return
        if key in seen:
            rejections.append({"family":family,"program":p,"reason":"exact duplicate"});return
        seen.add(key);pool.append(dict(p,id=key,family=family,method=method))
    for row in proposals:admit(*row,baseline)
    for _ in range(rule["normalizer_mutation_budget"]):
        p=rng.choice(baseline);c=list(map(Q,p["coefficients"]));b=list(map(Q,p["normalizers"]))
        j=rng.randrange(len(b));b[j]+=rng.choice([-2,-1,1,2])
        admit("normalizer_mutation",c,b,"seeded independent arithmetic/continuous normalizer mutation",baseline)
    energy=[]
    for p in baseline:
        if p["coefficients"]!=p["normalizers"] or p["degree"]<1:continue
        values=response(p,data,spec["training_q"],spec["training_points"]);r=p["parameter_vanishing_order"]
        e=sum(float(flint.arb(v).mid())**2/n/float(Q(1,max(1,p["degree"])*int(key.split(':')[0])))**(2*r)
              for key,v in values.items() if (n:=int(key.split(':')[1]))>=16)
        energy.append((e,p))
    pool=[p for D in range(1,Dmax+1) for e,p in sorted((row for row in energy if row[1]["degree"]==D),
        key=lambda z:(z[0],z[1]["id"]))[:adapt["promotion_pool"]]]
    pairs=[(left,right) for left in pool for right in pool if left["degree"]+right["degree"]<=Dmax]
    primary=baseline.copy();promotions=[];ablation=baseline.copy();base_seen=seen.copy()
    for _ in range(adapt["promotion_budget"]):
        if not pairs:break
        left,right=rng.choice(pairs);c=multiply(list(map(Q,left["coefficients"])),list(map(Q,right["coefficients"])))
        before=len(primary);admit("promoted_composition",c,None,{"left":left["id"],"right":right["id"],"production":"parameter-label polynomial product"},primary)
        promotions.append({"left":left["id"],"right":right["id"],"result_coefficients":list(map(str,c)),"admitted":len(primary)>before})
    seen=base_seen;arng=random.Random(spec["seed"]+901)
    for _ in range(adapt["promotion_budget"]):admit("ablation_random_slot",random_row(arng),None,"promotion-disabled resource slot",ablation)
    return primary,ablation,rejections,promotions


def fitted(p,values):
    points=[]
    for key,text in values.items():
        q,n=map(int,key.split(':'))
        if n<16:continue
        v=abs(flint.arb(text)).upper()
        if not v>real(Q(1,2**100)):continue
        points.append((math.log(n),math.log(float(Q(1,max(1,p["degree"])*q))),math.log(float(v))))
    if not points:return Q(1),Q(0),None
    means=[sum(row[k] for row in points)/len(points) for k in range(3)]
    A=sum((x-means[0])**2 for x,z,y in points);B=sum((x-means[0])*(z-means[1]) for x,z,y in points);D=sum((z-means[1])**2 for x,z,y in points)
    e=sum((x-means[0])*(y-means[2]) for x,z,y in points);f=sum((z-means[1])*(y-means[2]) for x,z,y in points);det=A*D-B*B
    if det<=0:return Q(1),Q(0),None
    theta=(e*D-f*B)/det;kappa=(f*A-e*B)/det
    th=min(Q(3,2),max(Q(-1,2),Q(math.ceil(16*theta)+1,16)))
    ka=min(Q(4),max(Q(-1),Q(round(16*kappa),16)))
    return th,ka,{"theta_slope":theta,"parameter_slope":kappa}


def envelope(p,theta,kappa,ell,q,n):
    a=real(Q(1,max(1,p["degree"])*q))
    return power(a,kappa)*power(real(n),theta)*power((flint.arb.const_e()+n).log(),ell)


def comparisons(p,c,values):
    bad=[];unresolved=[];ratios=[]
    for key,txt in values.items():
        q,n=map(int,key.split(':'));bound=real(c["constant"])*envelope(p,Q(c["theta"]),Q(c["parameter_power"]),Q(c["log_power"]),q,n);v=abs(flint.arb(txt))
        if not v<=bound:
            (bad if v>bound else unresolved).append(key)
        ratios.append((float((v/bound).upper()),key))
    worst,key=max(ratios,default=(0,None))
    return {"failures":bad,"unresolved":unresolved,"maximum_ratio":worst,"maximum_ratio_case":key,
            "finite_points_passed":not bad and not unresolved,"uniform_signed_premise_proved":False}


def estimates(p,values,spec,cert,numerators):
    theta,kappa,fit=fitted(p,values);thetas=sorted(set(map(Q,spec["growth_grid"]))|{theta});ks=set(map(Q,spec["parameter_grid"]))|{kappa}
    if p["parameter_vanishing_order"] is not None:ks.add(Q(p["parameter_vanishing_order"]))
    records=[]
    for theta,kappa,ell in itertools.product(thetas,sorted(ks),map(Q,spec["log_grid"])):
        maximum=max((abs(flint.arb(v))/envelope(p,theta,kappa,ell,*map(int,key.split(':')))).upper() for key,v in values.items())
        C=Q(max(1,int((maximum*real(Q(3,2))*1024).ceil().fmpz())),1024)
        tr=transfer(p,theta,kappa,ell,C);semantic={"program_id":p["id"],"theta":str(theta),"parameter_power":str(kappa),"log_power":str(ell),"constant":str(C)}
        r=dict(semantic,id=digest(semantic),transfer=tr,analytic_status=tr["analytic_status"],training_fit=fit)
        if tr["RH_sufficient_if_uniform"]:
            cost=recovery_cost(p,tr,cert,numerators,*map(Q,spec["cost_query"]),spec["training_q"])
            r["recovery_cost"]=cost;v=cost["best_conditional_reciprocal_zeta_bound_ball"]
            r["log_reciprocal_cost"]=float(flint.arb(v).upper().log()) if v else None
        records.append(r)
    return records


def select(programs,candidates,spec):
    ps={p["id"]:p for p in programs};chosen=[]
    def key(c):return (bool(c["validation"]["failures"] or c["validation"]["unresolved"]),
        c["log_reciprocal_cost"] if c.get("log_reciprocal_cost") is not None else 1e100,c["validation"]["maximum_ratio"],c["id"])
    eligible=[c for c in candidates if c["transfer"]["RH_sufficient_if_uniform"]]
    def include(pool):
        if pool:
            c=min(pool,key=key)
            if c not in chosen:chosen.append(c)
    include([c for c in eligible if ps[c["program_id"]]["family"]=="baseline"])
    for rate in range(spec["fixed_baseline"]["maximum_degree"]+1):include([c for c in eligible if ps[c["program_id"]]["parameter_vanishing_order"]==rate])
    # Preserve an above-threshold empirical lead independently of RH ranking.
    above=[c for c in candidates if c["analytic_status"]=="infinite_family_signed_obligation_above_RH_threshold"]
    if above:
        c=min(above,key=lambda c:(bool(c["validation"]["failures"] or c["validation"]["unresolved"]),Q(c["theta"]),c["validation"]["maximum_ratio"],c["id"]))
        if c not in chosen:chosen.append(c)
    for family in sorted({p["family"] for p in programs}):
        if len(chosen)>=spec["archive_size"]:break
        include([c for c in eligible if ps[c["program_id"]]["family"]==family])
    for c in sorted(eligible,key=key):
        if len(chosen)>=spec["archive_size"]:break
        if c not in chosen:chosen.append(c)
    return chosen[:spec["archive_size"]]


def discover(directory):
    spec=read(directory/"protocol.json");verify_code(spec);denials=restrict(directory);flint.ctx.prec=spec["precision"]
    D=spec["fixed_baseline"]["maximum_degree"];qs=spec["training_q"];points=spec["training_points"]
    mu=inverse_one_prefix(max(points));data=primitive_tables(mu,alpha_set(D,qs,anchor=True),points)
    programs,ablation,rejected,promotions=generate(spec,data)
    allps={p["id"]:p for p in ablation+programs}
    write(directory/"discovery_data.json",{"protocol_sha256":digest(spec),"complete_coefficient_cutoff":len(mu)-1,
        "inverse_coefficient_sha256":digest(mu),"primitive_tables":data,"worker_access_denials":denials})
    covers=[cauchy_boxes(Q(rho),spec["certificate_mesh"],spec["precision"]) for rho in spec["certificate_radii"]]
    certs={pid:global_certificate(p,covers) for pid,p in allps.items()}
    write(directory/"backend_certificates.json",{"covers":covers,"global_certificates":certs,
        "supplied_proof_backend":True,"RH_sufficient":False,"RH_proved":False})
    nums={};native=[]
    for alpha in alpha_set(D,qs,anchor=True):
        v,m=numerator(alpha,*map(Q,spec["cost_query"]),**spec["native_numerator_parameters"])
        nums[str(alpha)]=v;native.append(m)
        print("Entire numerator",alpha,"enclosed",flush=True)
    # Separate checks at Re(s)>1 and at s=1 test the initial identity and deflation.
    calibrations=[]
    for a,s,t in [(Q(1,2),Q(2),Q(0)),(Q(1,6),Q(1),Q(0))]:
        v,m=numerator(a,s,t,**spec["native_numerator_parameters"]);calibrations.append(dict(m,numerator_ball=complex_ball(v)))
    write(directory/"numerator_data.json",{"query":spec["cost_query"],"values":{k:complex_ball(v) for k,v in nums.items()},"certificates":native,"calibrations":calibrations})
    train={pid:response(p,data,qs,points) for pid,p in allps.items()};candidates=[]
    for pid,p in allps.items():candidates.extend(estimates(p,train[pid],spec,certs[pid],nums))
    batch={"protocol_sha256":digest(spec),"programs":programs,"ablation_programs":ablation,"rejected_proposals":rejected,"promotions":promotions,
        "candidates":candidates,"frozen_before_validation":True,"generation_uses_training_only":True}
    write(directory/"candidate_batch.json",batch)
    vqs=sorted(set(qs+spec["validation_new_q"]));vpoints=spec["validation_points"];mu=inverse_one_prefix(max(vpoints));vdata=primitive_tables(mu,alpha_set(D,vqs),vpoints)
    validation={pid:response(p,vdata,vqs,vpoints) for pid,p in allps.items()}
    validated=[dict(c,validation=comparisons(allps[c["program_id"]],c,validation[c["program_id"]])) for c in candidates]
    write(directory/"validation_data.json",{"candidate_batch_sha256":sha(directory/"candidate_batch.json"),"primitive_tables":vdata,
        "complete_coefficient_cutoff":len(mu)-1,"inverse_coefficient_sha256":digest(mu),"program_responses":validation,"candidates":validated})
    ids={p["id"] for p in programs};aids={p["id"] for p in ablation};archive=select(programs,[c for c in validated if c["program_id"] in ids],spec)
    aarchive=select(ablation,[c for c in validated if c["program_id"] in aids],spec)
    controls=[]
    for label,rule in [("excess_parameter_rate",lambda c:c["analytic_status"]=="ruled_out_by_exact_parameter_vanishing_order"),
                       ("subcritical_family",lambda c:c["analytic_status"]=="ruled_out_by_actual_critical_zero_and_infinite_parameter_family"),
                       ("uncompensated_branch",lambda c:c["analytic_status"]=="ruled_out_by_uncompensated_fractional_pole_at_one")]:
        pool=[c for c in validated if c["program_id"] in ids and rule(c)]
        if pool:controls.append({"label":label,"candidate":min(pool,key=lambda c:(bool(c["validation"]["failures"] or c["validation"]["unresolved"]),c["validation"]["maximum_ratio"],c["id"]))})
    write(directory/"archive.json",{"archive":archive,"ablation_archive":aarchive,"negative_controls":controls,
        "ablation_comparison":{"equal_promotion_slot_budgets":True,"primary_programs":len(programs),"ablation_programs":len(ablation),
            "admitted_promotions":sum(p["admitted"] for p in promotions),"promoted_programs":sum(p["family"]=="promoted_composition" for p in programs),
            "best_primary_log_cost":min((c["log_reciprocal_cost"] for c in archive if c.get("log_reciprocal_cost") is not None),default=None),
            "best_ablation_log_cost":min((c["log_reciprocal_cost"] for c in aarchive if c.get("log_reciprocal_cost") is not None),default=None)},
        "selection_closed":True,"final_data_used":False})
    sealed=["protocol.json","discovery_data.json","candidate_batch.json","backend_certificates.json","numerator_data.json","validation_data.json","archive.json"]
    write(directory/"seal.json",{"protocol_sha256":digest(spec),"selection_closed":True,"final_cases_exist_at_seal":False,"files":{n:sha(directory/n) for n in sealed}})
    print("Sealed",len(programs),"primary programs,",len(candidates),"estimates,",len(archive),"archive slots",flush=True)


def final(directory):
    spec=read(directory/"protocol.json");verify_code(spec);seal=read(directory/"seal.json");flint.ctx.prec=spec["precision"]
    for n,h in seal["files"].items():assert sha(directory/n)==h
    if (directory/"final_cases.json").exists():raise FileExistsError("Retain sealed final cases")
    seed=int.from_bytes(os.urandom(32),"big");rng=random.Random(seed);rule=spec["final_cases"]
    oldn={n for r in spec["retained_failed_runs_are_development"] for n in r["excluded_integer_scales"]}
    oldq={q for r in spec["retained_failed_runs_are_development"] for q in r["excluded_fresh_q"]}
    integers=sorted(rng.sample([n for n in range(rule["integer_range"][0],rule["integer_range"][1]+1) if n not in oldn],rule["integer_count"]))
    freshqs=sorted(rng.sample([q for q in range(rule["fresh_q_range"][0],rule["fresh_q_range"][1]+1) if q not in oldq],rule["fresh_q_count"]))
    points=sorted(set(map(Q,integers+rule["boundary"]))|{Q(n)+Q(rule["real_offset"]) for n in integers})
    qs=sorted(set(spec["training_q"]+freshqs));generic=[]
    for _ in range(rule["generic_unit_count"]):
        generic.append({"input":["0","1"]+[str(Q(rng.randint(-9,9),rng.randint(1,7))) for j in range(rule["generic_cutoff"]-1)],
            "alpha":str(Q(1,rng.randint(2,113)))})
    cases={"seed":str(seed),"integers":integers,"boundary":rule["boundary"],"points":list(map(str,points)),"qs":qs,"fresh_q":freshqs,
        "generic_units":generic,"seal_sha256":digest(seal),"created_after_selection_closed":True}
    write(directory/"final_cases.json",cases)
    archive=read(directory/"archive.json");batch=read(directory/"candidate_batch.json");allps={p["id"]:p for p in batch["ablation_programs"]+batch["programs"]}
    selected=archive["archive"]+[r["candidate"] for r in archive["negative_controls"]];ps={c["program_id"]:allps[c["program_id"]] for c in selected}
    alphas=sorted({order(p,q,j) for p in ps.values() for q in qs for j in range(p["degree"]+1)}|{Q(1)})
    N=max(x.numerator//x.denominator for x in points);mu=inverse_one_prefix(N);data=primitive_tables(mu,alphas,points)
    responses={pid:response(p,data,qs,integers+rule["boundary"]) for pid,p in ps.items()};outcomes=[]
    for c in selected:
        p=ps[c["program_id"]];o=comparisons(p,c,responses[p["id"]]);outcomes.append(dict(o,candidate_id=c["id"],program_id=p["id"],
            analytic_status=c["analytic_status"],RH_sufficient_if_uniform=c["transfer"]["RH_sufficient_if_uniform"],point_comparisons=len(responses[p["id"]]),RH_proved=False))
    backend=read(directory/"backend_certificates.json");increments=[];weak=[]
    for pid,p in ps.items():
        cert=backend["global_certificates"][pid];vals=response(p,data,qs,points)
        for q in qs:
            a=real(Q(1,max(1,p["degree"])*q));r=cert["parameter_power"];ell=cert["log_power"]
            for n in integers:
                diff=abs(flint.arb(vals[f"{q}:{Q(n)+Q(rule['real_offset'])}"])-flint.arb(vals[f"{q}:{n}"]))
                inc=flint.arb(cert["unit_increment_constant_ball"])*power(a,r)*power((flint.arb.const_e()+n+1).log(),ell)
                increments.append({"program_id":pid,"q":q,"n":n,"difference_ball":serialize(diff),"bound_ball":serialize(inc),"passed":bool(diff<=inc)})
            for x in points:
                value=abs(flint.arb(vals[f"{q}:{x}"]));B=flint.arb(cert["constant_ball"])*power(a,r)*real(x)*power((flint.arb.const_e()+real(x)).log(),ell)
                weak.append({"program_id":pid,"q":q,"x":str(x),"passed":bool(value<=B)})
    generic_rows=[]
    for case in generic:
        f=list(map(real,case["input"]));L,_=forward(f,Q(case["alpha"]));generic_rows.append({"case":case,"arithmetic_logarithm":list(map(serialize,L))})
    write(directory/"final_evaluation.json",{"protocol_sha256":digest(spec),"seal_sha256":digest(seal),"cases_sha256":digest(cases),
        "complete_coefficient_cutoff":N,"inverse_coefficient_sha256":digest(mu),"primitive_tables":data,"program_responses":responses,
        "outcomes":outcomes,"unit_increment_checks":increments,"weak_bound_checks":weak,"generic_input_responses":generic_rows,
        "final_scope_is_finite":True,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False})
    print("Fresh final:",N,"complete coefficients;",len(qs),"order parameters; all-scale premise remains unproved",flush=True)


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--run-dir",default="fractional-remainder-results/pilot-001");ap.add_argument("--source",default="prime-oscillation-results/audit-001")
    ap.add_argument("--phase",choices=["run","discover","final"],default="run");args=ap.parse_args();directory=(BASE/args.run_dir).resolve()
    if args.phase=="run":
        directory.mkdir(parents=True,exist_ok=False);write(directory/"protocol.json",protocol(BASE/args.source))
        frozen=directory/"frozen_source";frozen.mkdir()
        for n in CODE:(frozen/n).write_bytes((BASE/n).read_bytes())
        for phase in ["discover","final"]:subprocess.run([sys.executable,str(BASE/"fractional_remainder_search.py"),"--run-dir",str(directory),"--phase",phase],check=True)
        subprocess.run([sys.executable,str(BASE/"check_fractional_remainders.py"),"--run-dir",str(directory)],check=True)
        from fractional_remainder_report import publish
        publish(directory)
    elif args.phase=="discover":discover(directory)
    else:final(directory)


if __name__=="__main__":main()

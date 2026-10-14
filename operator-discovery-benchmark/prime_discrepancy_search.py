#!/usr/bin/env python3
"""Sealed floor-carry discovery and signed prime-discrepancy correlation search."""
import argparse
from collections import Counter
from fractions import Fraction as Q
from itertools import product
import math
import os
from pathlib import Path
import random
import subprocess
import sys
import flint
from stable_scale_search import BASE,read,write,sha,digest,verify_code
from fractional_moment_search import restrict
from prime_error_grammar import logarithmic_coefficients,real,serialize
from prime_discrepancy_grammar import (VERSION,carry_certificate,psi_prefix,
    density_certificate,integer_error_values,increments,discrepancy_density,
    complete_energy,square_prefix,diagonal,off_diagonal_transfer)

CODE=["prime_discrepancy_grammar.py","prime_discrepancy_search.py",
      "check_prime_discrepancy.py","prime_discrepancy_report.py","prime_discrepancy_proof.txt"]


def protocol(source):
    from prime_error_report import summary
    source=Path(source).resolve();summary(source)
    parent=read(source/"protocol.json")
    # Every generated parent program is available; prior final survivors do
    # not select the input language of this stage.
    ps=read(source/"candidate_batch.json")["programs"]
    return {"schema":1,"grammar_version":VERSION,"seed":2026101101,"precision":384,
        "objective":"Prove arithmetic prime-density inputs from discovered floor certificates; independently search the missing signed pair bound",
        "source_run":str(source),"source_verification_sha256":sha(source/"verification.json"),
        "source_batch_sha256":sha(source/"candidate_batch.json"),
        "code_sha256":dict(parent["code_sha256"],**{n:sha(BASE/n) for n in CODE}),
        "known_zero_dependency":parent["known_zero_dependency"],"input_programs":ps,
        "carry_grammar":{"delays":list(range(1,7)),"unit_coefficient":"1","free_integer_range":[-3,3],
            "certificate":"exact zero drift and nonnegative cells of the full integer period; every real input, not sampled inputs",
            "tail_index":14,"selection":"least proved global psi constant, then coefficient cost, then lexicographic coefficients"},
        "factorial_trace_points":[1,2,3,7,16,31,64,127,257,521,1024,2048,4096,8192],
        "coefficient_density_thresholds":[128,256,512,1024,2048],
        "training_scales":[1,2,4,8,16,32,64,128],"validation_scales":[193,257,389,521],
        "rho_inference":"OLS C_off versus D, no intercept, at X>=16; clipped to [-2,2], rounded to 1/64, with 0,1/16,1/8 margins; union generic grid",
        "rho_grid":["-2","-1","-1/2","0","1/2","1","2"],
        "gamma_inference":"OLS positive residual C_off-rho*D at X>=16; upward 1/32 rounding with 0,1/8,1/4 margins; union quarter powers zero through three",
        "constant_inference":"twice the positive part of the largest training ratio, rounded upward to 1/1024, minimum 1/1024",
        "archive_size":24,"score_anchor":1024,
        "selection":"baseline for every beta; actual-zero and pole-log diagnostic; multiplier-zero coverage; negative-association and bounded-off-diagonal coverage; fill by validation, ordinary-zeta relevance and total conditional energy bound, at most two fill entries per program",
        "final_cases":{"dyadic_exponents":[10,14],"dyadic_count":3,
            "irregular_range":[2049,8191],"irregular_count":3,"boundary":[1,2,3,15]},
        "delayed_support_cutoff":128,
        "observables":"zero-centered piecewise linear interpolation of li(n)-beta*sum_(m<n)lambda(m); complete A2, same-increment Gram diagonal D, and signed C_off=A2-D",
        "moment_scope":"every polynomial cell in each full window [X,2X]; no sampled quadrature",
        "diagonal_proof_scope":"actual prime-power increments only; never applied to positive-support controls",
        "coefficient_producer":"factor-free Dirichlet logarithm; no prime or factor oracle",
        "prior_final_data_is_development_only":True,"input_programs_selected_by_prior_final_outcomes":False,
        "generator_model_literature_network_calls":False,"historical_priority_is_acceptance_gate":False,
        "imported_prime_distribution_estimate":False,"uniform_signed_correlation_premise_proved":False,"RH_proved":False,
        "remaining_assumptions":["floor-carry certificate template, integer coefficient/delay budget and unit-delay normalization",
            "all parent finite first-jet filters; no new filter coefficients are generated in this stage",
            "quadratic ramp Gram representation; rho*D plus a pure power defect",
            "written elementary factorial, monotonic tail and logarithmic Mellin proofs; not machine-formalized",
            "finite scale and archive budgets; learned cancellation is conjectural"]}


def enumerate_carries(spec,psi):
    rule=spec["carry_grammar"];records=[];proved=[]
    for tail in product(range(rule["free_integer_range"][0],rule["free_integer_range"][1]+1),repeat=len(rule["delays"])-1):
        coefficients=[1]+list(tail)
        c=carry_certificate(coefficients)
        row={"coefficients":list(map(str,coefficients)),"certificate":c}
        row["id"]=digest(row["coefficients"])
        if c["status"]=="proved_nonnegative_periodic_carry":
            row["density"]=density_certificate(c,psi,rule["tail_index"]);proved.append(row)
        records.append(row)
    if not proved:raise ArithmeticError("No universal positive floor certificate in this budget")
    chosen=min(proved,key=lambda r:(Q(r["density"]["constant"]),Q(r["certificate"]["coefficient_cost"]),tuple(map(Q,r["coefficients"]))))
    return {"all_proposals":records,"statuses":dict(Counter(r["certificate"]["status"] for r in records)),
            "selected_id":chosen["id"],"selected":chosen,"expected_named_formula_supplied":False}


def densities(f,psi_C,spec):
    result={}
    for beta in sorted({p["beta"] for p in spec["input_programs"]},key=Q):
        a=increments(integer_error_values(f,beta))
        proposals=[discrepancy_density(a,beta,psi_C,n) for n in spec["coefficient_density_thresholds"]]
        chosen=min(proposals,key=lambda r:(Q(r["constant"]),r["initial_cutoff"]))
        result[beta]={"proposals":proposals,"selected":chosen}
    return result


def observations(ps,f,scales):
    tables={}
    for beta in {p["beta"] for p in ps}:
        values=integer_error_values(f,beta);a=increments(values);count,weighted=square_prefix(a)
        tables[beta]=(values,a,count,weighted)
    out={}
    for p in ps:
        values,a,count,weighted=tables[p["beta"]];rows={}
        for X in scales:
            A=complete_energy(p["atoms"],values,X)
            D=diagonal(p["atoms"],a,count,weighted,X)
            rows[str(X)]={"A2":serialize(A),"D":serialize(D),"C_off":serialize(A-D)}
        out[p["id"]]=rows
    return out


def ols(points):
    if len(points)<3:return 0.0
    mx=sum(x for x,y in points)/len(points);my=sum(y for x,y in points)/len(points)
    return sum((x-mx)*(y-my) for x,y in points)/sum((x-mx)**2 for x,y in points)


def infer(p,observed,density,spec):
    rows={int(X):{k:flint.arb(v) for k,v in r.items()} for X,r in observed.items()}
    tail=[r for X,r in rows.items() if X>=16]
    den=sum(float(r["D"].mid())**2 for r in tail)
    learned=0 if not den else sum(float(r["D"].mid())*float(r["C_off"].mid()) for r in tail)/den
    base=Q(round(max(-2,min(2,learned))*64),64)
    rhos=set(map(Q,spec["rho_grid"]))|{base+Q(m) for m in (0,Q(1,16),Q(1,8))}
    out=[]
    for rho in sorted(rhos):
        residual={X:r["C_off"]-real(rho)*r["D"] for X,r in rows.items()}
        slope=ols([(math.log(X),float(v.mid().log())) for X,v in residual.items() if X>=16 and v>0])
        gammas={Q(j,4) for j in range(13)}|{max(Q(0),min(Q(4),Q(math.ceil(32*(slope+m)),32))) for m in (0,1/8,1/4)}
        for gamma in sorted(gammas):
            top=max([real(0)]+[(v/real(X)**real(gamma)).upper() for X,v in residual.items()])
            B=max(Q(1,1024),Q(int((top*2048).ceil().fmpz()),1024))
            transfer=off_diagonal_transfer(p,rho,gamma,B,density)
            c={"program_id":p["id"],"rho":str(rho),"gamma":str(gamma),"constant":str(B),
                "observed_rho":learned,"positive_residual_growth_slope":slope,"transfer":transfer,
                "analytic_status":transfer["analytic_status"]}
            c["id"]=digest({k:c[k] for k in ("program_id","rho","gamma","constant")});out.append(c)
    return out


def state(value,bound):return "pass" if value<=bound else ("fail" if value>bound else "unresolved")


def comparisons(c,observed):
    rho,gamma,B=map(Q,(c[k] for k in ("rho","gamma","constant")))
    return {X:state(flint.arb(row["C_off"]),real(rho)*flint.arb(row["D"])+real(B)*real(X)**real(gamma)) for X,row in observed.items()}


def choose(cs,ps,spec):
    lookup={p["id"]:p for p in ps};out=[];used=set();per_program=Counter()
    def key(c):
        rank=0 if c["analytic_status"].startswith("RH_sufficient") else (1 if c["analytic_status"].startswith("signed_correlation") else 3)
        eta=Q(c["transfer"]["mellin_exponent"]);rho=Q(c["rho"]);gamma=Q(c["gamma"])
        X=real(spec["score_anchor"])
        conditional=real(max(Q(0),1+rho))*real(c["transfer"]["diagonal_coefficient"])*X**2/(flint.arb.const_e()+X).log()+real(c["constant"])*X**real(gamma)
        return (bool(c["validation_failures"] or c["validation_unresolved"]),rank,eta,float(conditional.upper()),gamma,c["id"])
    def add(pool):
        pool=[c for c in pool if c["id"] not in used]
        if pool:
            c=min(pool,key=key);out.append(c);used.add(c["id"]);per_program[c["program_id"]]+=1
    for beta in sorted({p["beta"] for p in ps},key=Q):
        add([c for c in cs if lookup[c["program_id"]]["beta"]==beta and len(lookup[c["program_id"]]["atoms"])==1])
    add([c for c in cs if c["analytic_status"].startswith("uniform_claim_ruled_out_by_actual")])
    add([c for c in cs if c["analytic_status"].startswith("uniform_claim_ruled_out_by_pole")])
    add([c for c in cs if lookup[c["program_id"]]["beta"]=="1" and lookup[c["program_id"]]["multiplier_at_one"]=="0"])
    add([c for c in cs if lookup[c["program_id"]]["beta"]=="1" and -1<Q(c["rho"])<0])
    add([c for c in cs if lookup[c["program_id"]]["beta"]=="1" and Q(c["rho"])==0 and Q(c["gamma"])==0])
    for c in sorted(cs,key=key):
        if len(out)>=spec["archive_size"]:break
        if c["id"] not in used and per_program[c["program_id"]]<2:
            out.append(c);used.add(c["id"]);per_program[c["program_id"]]+=1
    return out


def factorial_traces(f,selected,points):
    c=list(map(Q,selected["coefficients"]));out=[]
    for N in points:
        lhs=sum((real(f[n])*real(n).log()*real(sum((v*(N//(n*(j+1))) for j,v in enumerate(c)),Q(0))) for n in range(1,N+1) if f[n]),real(0))
        rhs=sum((real(v)*real(math.factorial(N//(j+1))).log() for j,v in enumerate(c) if v),real(0))
        assert lhs.overlaps(rhs)
        out.append({"N":N,"prime_weighted_carry_ball":serialize(lhs),"factorial_combination_ball":serialize(rhs)})
    return out


def discover(directory):
    spec=read(directory/"protocol.json");verify_code(spec);denied=restrict(directory,spec)
    flint.ctx.prec=spec["precision"]
    N=max(2**(spec["carry_grammar"]["tail_index"]-1),max(spec["coefficient_density_thresholds"]),2*max(spec["training_scales"]))
    f=logarithmic_coefficients(N);carries=enumerate_carries(spec,psi_prefix(f))
    density=densities(f,carries["selected"]["density"]["constant"],spec)
    ps=spec["input_programs"];observed=observations(ps,f,spec["training_scales"])
    candidates=[c for p in ps for c in infer(p,observed[p["id"]],density[p["beta"]]["selected"],spec)]
    write(directory/"discovery_data.json",{"complete_moments":observed,"carry_search":carries,"coefficient_densities":density,
        "factorial_traces":factorial_traces(f,carries["selected"],spec["factorial_trace_points"]),
        "coefficient_cutoff":N,"coefficient_sha256":digest(list(map(str,f)))})
    write(directory/"candidate_batch.json",{"programs":ps,"candidates":candidates,"frozen_before_validation":True,
        "protocol_sha256":digest(spec),"discovery_sha256":sha(directory/"discovery_data.json")})
    f=logarithmic_coefficients(2*max(spec["validation_scales"]));validation=observations(ps,f,spec["validation_scales"])
    for c in candidates:
        states=comparisons(c,validation[c["program_id"]])
        c["validation_failures"]=[X for X,v in states.items() if v=="fail"]
        c["validation_unresolved"]=[X for X,v in states.items() if v=="unresolved"]
    write(directory/"validation_data.json",{"complete_moments":validation,"candidates":candidates,
        "coefficient_cutoff":len(f)-1,"coefficient_sha256":digest(list(map(str,f)))})
    selected=choose(candidates,ps,spec)
    write(directory/"archive.json",{"archive":selected,"worker_access_denials":denied,"final_data_used":False,
        "uniform_signed_correlation_premise_proved":False,"RH_proved":False})
    write(directory/"seal.json",{"protocol_sha256":digest(spec),"selection_closed":True,"final_cases_exist_at_seal":False,
        "files":{n:sha(directory/n) for n in ("protocol.json","discovery_data.json","candidate_batch.json","validation_data.json","archive.json")}})
    print("Sealed",len(selected),"signed correlation bounds from",len(ps),"programs /",len(candidates),"estimates; proved",carries["statuses"].get("proved_nonnegative_periodic_carry",0),"floor certificates",flush=True)


def fresh_cases(spec,seal):
    seed=int.from_bytes(os.urandom(32),"big");rng=random.Random(seed);rule=spec["final_cases"]
    exponents=sorted(rng.sample(range(rule["dyadic_exponents"][0],rule["dyadic_exponents"][1]+1),rule["dyadic_count"]))
    irregular=sorted(rng.sample(range(rule["irregular_range"][0],rule["irregular_range"][1]+1),rule["irregular_count"]))
    large=sorted(set([2**j for j in exponents]+irregular))
    return {"evaluator_seed":str(seed),"dyadic_exponents":exponents,"irregular":irregular,"large":large,
        "scales":sorted(set(rule["boundary"]+large)),"created_after_selection_closed":True,"seal_sha256":digest(seal)}


def final(directory):
    spec=read(directory/"protocol.json");verify_code(spec);seal=read(directory/"seal.json")
    for n,h in seal["files"].items():assert sha(directory/n)==h
    flint.ctx.prec=spec["precision"];path=directory/"final_cases.json"
    if not path.exists():write(path,fresh_cases(spec,seal))
    cases=read(path);assert cases["seal_sha256"]==digest(seal)
    arc=read(directory/"archive.json");used={c["program_id"] for c in arc["archive"]}
    ps=[p for p in spec["input_programs"] if p["id"] in used]
    N=2*max(cases["scales"]);f=logarithmic_coefficients(N)
    actual=observations(ps,f,cases["scales"]);controls={}
    cut=spec["delayed_support_cutoff"]
    for name,coefs in (("positive_support",[Q(0),Q(0)]+[Q(1)]*(N-1)),("delayed_support",f[:cut+1]+[Q(1)]*(N-cut))):
        controls[name]=observations(ps,coefs,cases["large"])
    outcomes=[]
    for c in arc["archive"]:
        states=comparisons(c,actual[c["program_id"]])
        negative={name:comparisons(c,values[c["program_id"]]) for name,values in controls.items()}
        outcomes.append({"candidate_id":c["id"],"window_comparisons":states,"finite_windows_passed":all(v=="pass" for v in states.values()),
            "support_control_comparisons":negative,"support_controls_are_actual_prime_density_inputs":False,
            "reselected":False,"uniform_signed_correlation_premise_proved":False,"RH_proved":False})
    write(directory/"final_evaluation.json",{"actual_moments":actual,"support_control_moments":controls,"outcomes":outcomes,
        "coefficient_cutoff":N,"coefficient_sha256":digest(list(map(str,f))),"seal_sha256":digest(seal),"cases_sha256":digest(cases),
        "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False})
    print("Evaluated complete signed correlation windows through coefficient",N,flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("mode",choices=("run","discover","final"))
    parser.add_argument("--run-dir",type=Path,required=True);parser.add_argument("--source-run",type=Path)
    args=parser.parse_args();directory=args.run_dir.resolve()
    if args.mode=="run":
        if directory.exists() or args.source_run is None:raise ValueError("A fresh directory and verified prime-error source are required")
        directory.mkdir(parents=True);write(directory/"protocol.json",protocol(args.source_run))
        for mode in ("discover","final"):
            subprocess.run([sys.executable,str(Path(__file__)),mode,"--run-dir",str(directory)],check=True,cwd=BASE)
        subprocess.run([sys.executable,str(BASE/"check_prime_discrepancy.py"),"--run-dir",str(directory)],check=True,cwd=BASE)
        from prime_discrepancy_report import publish
        publish(directory)
    elif args.mode=="discover":discover(directory)
    else:final(directory)

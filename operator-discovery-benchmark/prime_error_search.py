#!/usr/bin/env python3
"""Frozen signed first-jet filter and power/logarithm estimate search."""
import argparse
from fractions import Fraction as Q
import math
from math import comb
import os
from pathlib import Path
import random
import subprocess
import sys
import flint
from stable_scale_search import BASE,read,write,sha,digest,verify_code
from fractional_moment_search import restrict
from prime_error_grammar import (VERSION,real,logarithmic_coefficients,prefix,
    canonical_atoms,response,transfer,cost,multiplier,serialize)

CODE = ["prime_error_grammar.py","prime_error_search.py","check_prime_error.py",
        "prime_error_report.py","prime_error_proof.txt"]


def protocol(source):
    from parameter_jet_report import summary
    source=Path(source).resolve()
    summary(source)
    parent=read(source/"protocol.json")
    pole=Path(parent["source_run"])
    return {"schema":1,"grammar_version":VERSION,"seed":2026101003,"precision":384,
            "source_run":str(source),"source_verification_sha256":sha(source/"verification.json"),
            "source_data_sha256":sha(source/"jet_data.json"),
            "code_sha256":dict(parent["code_sha256"],**{n:sha(BASE/n) for n in CODE}),
            "known_zero_dependency":read(pole/"protocol.json")["known_zero_dependency"],
            "betas":["0","1/2","1","3/2"],"bases":[2,3,5],"maximum_degree":4,
            "mixed_delays":[["1","3/2","2","5/2"],["1","2","3","5"],["1","3/2","3","9/2"]],
            "random_draws":32,"random_denominators":[1,2,4,8,16,32],"random_numerator_range":[-32,32],
            "least_squares":"weighted complete response least squares, ridge 1/1024, coefficients rounded to 1/64 and clipped to [-16,16]",
            "training_points":[1,2,3,4,5,8,12,16,24,32,48,64,96,128],
            "validation_points":[193,257,389,521,769],
            "log_powers":["0","1/2","1","2","3"],
            "theta_inference":"OLS after subtracting log-power term; upward 1/32 quantization plus 0,1/8,1/4 margins; quarter-power grid zero through 3/2",
            "offset_inference":"zero, mean and median of n>=16 training responses, rounded to 1/256",
            "constant_inference":"twice maximum training ratio, rounded upward to 1/1024",
            "archive_size":12,
            "selection":"unfiltered matched baseline; matched multiplier-zero-at-one filter; a known-zero-impossible and a pole-log-impossible diagnostic; fill distinct programs by validation, RH relevance, charged reciprocal logarithmic cost",
            "final_cases":{"large_count":5,"large_range":[2049,32767],"intermediate_count":4,"intermediate_range":[17,127],"boundary":[1,2,3,4,5,8,15]},
            "delayed_support_cutoff":128,
            "native_logarithmic_bridge":{"real_part":4,"heights":["0","7/3","19"],"tail_h":2},
            "native_zero_residue_calibration":{"multiplier":"((s-1)zeta(s))^k, k=1,2,3; it vanishes at the actual enclosed zero","precision":768},
            "all_height_multiplier_nonvanishing_required":False,
            "data_scope":"complete signed point values and complete logarithmic coefficient prefixes; no complete-window moment claim",
            "coefficient_producer":"factor-free inverse and finite Dirichlet logarithm, no prime/factor oracle",
            "model_or_literature_calls":False,"historical_priority_is_acceptance_gate":False,
            "uniform_signed_premise_proved":False,"RH_proved":False,
            "remaining_assumptions":["first-jet li/count representation and finite dilation language","degree/delay/coefficient budgets","pure power times logarithmic point-bound models","written meromorphic residue proof backend","fixed-point quantitative cost does not certify all-height division"]}


def least_squares(rows):
    m=len(rows[0][2])
    matrix=[[sum(z[i]*z[j]/n for n,y,z in rows)+(1/1024 if i==j else 0)
             for j in range(m)] for i in range(m)]
    rhs=[-sum(y*z[i]/n for n,y,z in rows) for i in range(m)]
    for i in range(m):
        pivot=max(range(i,m),key=lambda k:abs(matrix[k][i]))
        matrix[i],matrix[pivot]=matrix[pivot],matrix[i]
        rhs[i],rhs[pivot]=rhs[pivot],rhs[i]
        divisor=matrix[i][i]
        if abs(divisor)<1e-14:
            return [Q(0)]*m
        matrix[i]=[v/divisor for v in matrix[i]]
        rhs[i]/=divisor
        for j in range(m):
            if j==i:continue
            factor=matrix[j][i]
            matrix[j]=[a-factor*b for a,b in zip(matrix[j],matrix[i])]
            rhs[j]-=factor*rhs[i]
    return [Q(round(max(-16,min(16,v))*64),64) for v in rhs]


def programs(spec,counts):
    out={}
    def add(atoms,beta,origin):
        atoms=canonical_atoms(atoms)
        p={"atoms":atoms,"beta":str(Q(beta))}
        pid=digest(p)
        if pid not in out:
            p.update({"id":pid,"origins":[origin],"multiplier_at_one":str(sum((Q(c)/Q(d) for d,c in atoms),Q(0)))})
            out[pid]=p
        elif origin not in out[pid]["origins"]:
            out[pid]["origins"].append(origin)
    rng=random.Random(spec["seed"])
    random_atoms=[]
    for _ in range(spec["random_draws"]):
        b=rng.choice(spec["bases"])
        degree=rng.randint(1,spec["maximum_degree"])
        cs=[Q(rng.randint(*spec["random_numerator_range"]),rng.choice(spec["random_denominators"])) for j in range(degree)]
        random_atoms.append([[1,1]]+[[b**(j+1),c] for j,c in enumerate(cs)])
    for beta in map(Q,spec["betas"]):
        add([[1,1]],beta,"unfiltered")
        delays=[]
        for b in spec["bases"]:
            for degree in range(1,spec["maximum_degree"]+1):
                add([[b**j,Q((-b)**j*comb(degree,j))] for j in range(degree+1)],beta,"finite_differences")
                delays.append([Q(b**j) for j in range(degree+1)])
        for atoms in random_atoms:
            add(atoms,beta,"unrestricted_rational")
        delays.extend([list(map(Q,v)) for v in spec["mixed_delays"]])
        for ds in delays:
            rows=[]
            for n in spec["training_points"]:
                values=[float(response({"atoms":[["1","1"]],"beta":str(beta)},counts,[Q(n)/d])[str(Q(n)/d)].mid()) for d in ds]
                rows.append((n,values[0],values[1:]))
            learned=least_squares(rows)
            add([[ds[0],1]]+list(zip(ds[1:],learned)),beta,"least_squares")
    return [out[k] for k in sorted(out)]


def observe(ps,counts,points):
    return {p["id"]:{n:serialize(v) for n,v in response(p,counts,points).items()} for p in ps}


def infer(p,observations,spec):
    values={int(n):flint.arb(v) for n,v in observations.items()}
    tail=[v for n,v in sorted(values.items()) if n>=16]
    ordered=sorted(tail,key=lambda v:float(v.mid()))
    offsets=sorted({Q(0),Q(round(float(ordered[len(ordered)//2].mid())*256),256),
                    Q(round(sum(float(v.mid()) for v in tail)*256/len(tail)),256)})
    out=[]
    for A in offsets:
        for ell in map(Q,spec["log_powers"]):
            pairs=[(math.log(n),float(abs(v-real(A)).mid().log())-
                    float(ell)*math.log(float((flint.arb.const_e()+n).log().mid())))
                   for n,v in values.items() if n>=16 and abs(v-real(A))>0]
            growth=0.0
            if len(pairs)>=3:
                mx=sum(x for x,y in pairs)/len(pairs);my=sum(y for x,y in pairs)/len(pairs)
                growth=sum((x-mx)*(y-my) for x,y in pairs)/sum((x-mx)**2 for x,y in pairs)
            thetas={Q(j,4) for j in range(7)}|{max(Q(0),min(Q(2),Q(math.ceil(32*(growth+m)),32))) for m in (0,1/8,1/4)}
            for theta in sorted(thetas):
                maximum=max((abs(v-real(A))/real(n)**real(theta)/(flint.arb.const_e()+n).log()**real(ell)).upper() for n,v in values.items())
                C=max(Q(1,1024),Q(int((maximum*2048).ceil().fmpz()),1024))
                cert=transfer(p,theta,ell,C,A)
                if cert["uncancelled_pole_logarithm_at_one"]:
                    status="uniform_claim_ruled_out_by_uncancelled_pole_logarithm"
                elif Q(p["beta"])==1 and theta<Q(1,2):
                    status="uniform_claim_ruled_out_by_actual_critical_zero_even_if_multiplier_vanishes"
                elif cert["RH_sufficient_if_uniform"]:
                    status="RH_sufficient_signed_prime_error_obligation_missing_uniform_proof"
                else:
                    status="signed_growth_obligation_above_RH_threshold"
                row={"program_id":p["id"],"theta":str(theta),"log_power":str(ell),"constant":str(C),"offset":str(A),
                     "observed_growth_slope":growth,"transfer":cert,"analytic_status":status}
                if Q(p["beta"])==1 and theta>=Q(1,2):
                    sigma=theta+Q(1,8)
                    bound=cost(p,cert,sigma,16)
                    row.update({"cost_sigma":str(sigma),"cost_height":"16",
                                "conditional_log_reciprocal_bound_ball":None if bound is None else serialize(bound),
                                "log_reciprocal_cost":1e100 if bound is None else float(bound.upper()),
                                "cost_is_all_height_certificate":False})
                row["id"]=digest({k:row[k] for k in ("program_id","theta","log_power","constant","offset")})
                out.append(row)
    return out


def state(value,bound):
    return "pass" if value<=bound else ("fail" if value>bound else "unresolved")


def comparisons(c,observations):
    A,theta,ell,C=map(Q,(c[k] for k in ("offset","theta","log_power","constant")))
    return {n:state(abs(flint.arb(v)-real(A)),real(C)*real(n)**real(theta)*(flint.arb.const_e()+real(n)).log()**real(ell)) for n,v in observations.items()}


def choose(cs,ps,spec):
    lookup={p["id"]:p for p in ps}
    out=[];used=set()
    def key(c):
        good=not c["validation_failures"] and not c["validation_unresolved"]
        rank=0 if c["analytic_status"].startswith("RH_sufficient") else (1 if c["analytic_status"].startswith("signed_growth") else 3)
        return (not good,rank,Q(c["theta"]),c.get("log_reciprocal_cost",1e100),Q(c["log_power"]),Q(c["constant"]),c["id"])
    def add(pool):
        pool=[c for c in pool if c["program_id"] not in used]
        if not pool:return
        c=min(pool,key=key)
        if c["program_id"] not in used:
            out.append(c);used.add(c["program_id"])
    add([c for c in cs if lookup[c["program_id"]]["beta"]=="1" and len(lookup[c["program_id"]]["atoms"])==1])
    add([c for c in cs if lookup[c["program_id"]]["beta"]=="1" and lookup[c["program_id"]]["multiplier_at_one"]=="0"])
    add([c for c in cs if c["analytic_status"].startswith("uniform_claim_ruled_out_by_actual")])
    add([c for c in cs if c["analytic_status"].startswith("uniform_claim_ruled_out_by_uncancelled")])
    for c in sorted(cs,key=key):
        if len(out)>=spec["archive_size"]:break
        if c["program_id"] not in used:
            out.append(c);used.add(c["program_id"])
    return out


def discover(directory):
    spec=read(directory/"protocol.json");verify_code(spec)
    denied=restrict(directory,spec);flint.ctx.prec=spec["precision"]
    f=logarithmic_coefficients(max(spec["training_points"]))
    ps=programs(spec,prefix(f))
    observed=observe(ps,prefix(f),spec["training_points"])
    candidates=[c for p in ps for c in infer(p,observed[p["id"]],spec)]
    write(directory/"discovery_data.json",{"complete_values":observed,"coefficient_sha256":digest(list(map(str,f)))})
    write(directory/"candidate_batch.json",{"programs":ps,"candidates":candidates,"frozen_before_validation":True,
                                           "protocol_sha256":digest(spec),"discovery_sha256":sha(directory/"discovery_data.json")})
    f=logarithmic_coefficients(max(spec["validation_points"]))
    validation=observe(ps,prefix(f),spec["validation_points"])
    for c in candidates:
        states=comparisons(c,validation[c["program_id"]])
        c["validation_failures"]=[n for n,v in states.items() if v=="fail"]
        c["validation_unresolved"]=[n for n,v in states.items() if v=="unresolved"]
    write(directory/"validation_data.json",{"complete_values":validation,"coefficient_sha256":digest(list(map(str,f))),"candidates":candidates})
    selected=choose(candidates,ps,spec)
    write(directory/"archive.json",{"archive":selected,"worker_access_denials":denied,"final_data_used":False,"uniform_signed_premise_proved":False})
    write(directory/"seal.json",{"protocol_sha256":digest(spec),"selection_closed":True,"final_cases_exist_at_seal":False,
                                  "files":{n:sha(directory/n) for n in ("protocol.json","discovery_data.json","candidate_batch.json","validation_data.json","archive.json")}})
    print("Sealed",len(selected),"prime-error bounds from",len(ps),"programs /",len(candidates),"estimates",flush=True)


def final(directory):
    spec=read(directory/"protocol.json");verify_code(spec);seal=read(directory/"seal.json")
    for n,h in seal["files"].items():assert sha(directory/n)==h
    flint.ctx.prec=spec["precision"]
    path=directory/"final_cases.json"
    if path.exists():cases=read(path)
    else:
        seed=int.from_bytes(os.urandom(32),"big");rng=random.Random(seed);rule=spec["final_cases"]
        large=sorted(rng.sample(range(rule["large_range"][0],rule["large_range"][1]+1),rule["large_count"]))
        intermediate=sorted(rng.sample(range(rule["intermediate_range"][0],rule["intermediate_range"][1]+1),rule["intermediate_count"]))
        cases={"evaluator_seed":str(seed),"large":large,"intermediate":intermediate,"points":sorted(set(rule["boundary"]+intermediate+large)),
               "created_after_selection_closed":True,"seal_sha256":digest(seal)}
        write(path,cases)
    assert cases["seal_sha256"]==digest(seal)
    N=max(cases["points"]);f=logarithmic_coefficients(N)
    positive=[Q(0),Q(0)]+[Q(1)]*(N-1)
    cut=spec["delayed_support_cutoff"]
    delayed=f[:cut+1]+[Q(1)]*(N-cut)
    arc=read(directory/"archive.json");ps={p["id"]:p for p in read(directory/"candidate_batch.json")["programs"]}
    used=sorted({c["program_id"] for c in arc["archive"]})
    actual={};controls={}
    for pid in used:
        p=ps[pid]
        actual[pid]={n:serialize(v) for n,v in response(p,prefix(f),cases["points"]).items()}
        controls[pid]={name:{n:serialize(v) for n,v in response(p,prefix(coeffs),cases["large"]).items()}
                       for name,coeffs in (("positive_support",positive),("delayed_support",delayed))}
    outcomes=[]
    for c in arc["archive"]:
        states=comparisons(c,actual[c["program_id"]])
        control={name:comparisons(c,v) for name,v in controls[c["program_id"]].items()}
        outcomes.append({"candidate_id":c["id"],"point_comparisons":states,"finite_points_passed":all(v=="pass" for v in states.values()),
                         "support_control_comparisons":control,"support_control_uniform_claims_ruled_out":Q(c["theta"])<1,
                         "reselected":False,"uniform_signed_premise_proved":False})
    native=[];rule=spec["native_logarithmic_bridge"]
    for height in rule["heights"]:
        s=flint.acb(rule["real_part"],real(height))
        value=s.zeta().log()
        partial=sum((real(f[n])*(-s*real(n).log()).exp() for n in range(2,N+1) if f[n]),flint.acb(0))
        tail=real(N)**(-rule["tail_h"])*real(rule["real_part"]-rule["tail_h"]).zeta().log()
        assert abs(value-partial).upper()<tail.lower()
        native.append({"height":height,"log_zeta_ball":[serialize(value.real),serialize(value.imag)],
                       "partial_ball":[serialize(partial.real),serialize(partial.imag)],"proved_tail_ball":serialize(tail),
                       "scope":"native logarithmic coefficient bridge, not a full truncated-error Mellin quadrature"})
    write(directory/"final_evaluation.json",{"seal_sha256":digest(seal),"cases_sha256":digest(cases),"actual_values":actual,
        "support_control_values":controls,"outcomes":outcomes,"coefficient_cutoff":N,"coefficient_sha256":digest(list(map(str,f))),
        "native_logarithmic_checks":native,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False})
    print("Evaluated complete prime-error prefixes through",N,flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode",choices=("run","discover","final"));parser.add_argument("--run-dir",type=Path,required=True)
    parser.add_argument("--source-run",type=Path)
    args=parser.parse_args();directory=args.run_dir.resolve()
    if args.mode=="run":
        if directory.exists() or args.source_run is None:raise ValueError("A fresh directory and verified jet source are required")
        directory.mkdir(parents=True);write(directory/"protocol.json",protocol(args.source_run))
        for mode in ("discover","final"):
            subprocess.run([sys.executable,str(Path(__file__)),mode,"--run-dir",str(directory)],check=True,cwd=BASE)
        subprocess.run([sys.executable,str(BASE/"check_prime_error.py"),"--run-dir",str(directory)],check=True,cwd=BASE)
        from prime_error_report import publish
        publish(directory)
    elif args.mode=="discover":discover(directory)
    else:final(directory)

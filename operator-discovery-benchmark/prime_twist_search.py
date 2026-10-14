#!/usr/bin/env python3
"""Frozen fractional-twist search, including negative signed decay exponents."""
import argparse
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
from prime_twist_grammar import (VERSION,canonical,semantics_digest,twist,polynomial_range,normalizer,
    tables,observe,offset_value,finite_part_center,weak_uniform_bound,transfer,recovery_cost)
from prime_discrepancy_grammar import square_prefix,diagonal,complete_energy

CODE=["prime_twist_grammar.py","prime_twist_search.py","check_prime_twists.py","prime_twist_report.py","prime_twist_proof.txt"]


def protocol(source):
    from prime_discrepancy_report import summary
    source=Path(source).resolve();r=summary(source);parent=read(source/"protocol.json")
    obligations=[row["candidate"] for row in r["surviving_uniform_proof_obligations"] if row["program"]["atoms"]==[["1","1"]]]
    return {"schema":1,"grammar_version":VERSION,"precision":384,"seed":2026101201,
        "objective":"Learn signed prime-error decay with fractional arithmetic twists, exact centers, all-scale signed calibrations and charged recovery to ordinary zeta",
        "source_run":str(source),"source_verification_sha256":sha(source/"verification.json"),
        "source_archive_sha256":sha(source/"archive.json"),"source_final_sha256":sha(source/"final_evaluation.json"),
        "code_sha256":dict(parent["code_sha256"],**{n:sha(BASE/n) for n in CODE}),
        "this_stage_source_files":CODE,
        "known_zero_dependency":parent["known_zero_dependency"],
        "prime_density_constant":r["selected_prime_density_certificate"]["density"]["constant"],
        "source_coefficient_square_certificate":r["all_scale_coefficient_density_certificates"]["1"],
        "source_unfiltered_moment_obligations":obligations,
        "deltas":["1/6","1/4","1/3","1/2","2/3","1","3/2"],"semantic_denominator_ceiling":None,
        "channels":["weighted","log"],"enumerated_degree":2,"integer_range":[-2,2],"monomial_degrees":[0,1,2,3],
        "random_draws":12,"random_denominators":[1,2,4,8],"maximum_degree":3,
        "normalizer_constructions":["same coefficients","leading coefficient only","least squares for random polynomials"],
        "least_squares":"leading normalizer fixed at one; fit later normalizers with ridge 1/1024, round to 1/64 and clip to [-16,16]",
        "training_points":[1,2,3,4,5,8,12,16,24,32,48,64,96,128],"validation_points":[193,257,389,521,769],
        "offset_constructions":["zero","exact compiled Mellin finite part at zero"],
        "log_powers":["0","1"],"theta_grid":["-1","-1/2","0","1/2","1","3/2"],
        "theta_inference":"OLS absolute centered responses at n>=16, with log-power removed; upward 1/32 quantization with margins 0,1/8,1/4; union generic grid, charged critical target and weak bound exponent",
        "constant_inference":"twice maximum training ratio, upward 1/1024 rounding, minimum 1/1024",
        "archive_size":20,"cost_height":"16","cost_line_margin":"1/8","recovery_terminal_real_part":"9/8",
        "selection":"unfiltered baseline at theta=1/2 and log power zero; best program per channel; RH-compatible shifted program per delta; one inverse-shift-loss example, one negative decay lead, actual-zero diagnostic and density-matched pole diagnostics; fill distinct programs by validation and full recovery cost",
        "final_cases":{"large_count":3,"large_range":[16385,32767],"irregular_point_count":3,"irregular_point_range":[2049,8191],"boundary":[1,2,3,4,15]},
        "generic_response_calibration":{"cutoff":17,"points":[1,2,3,5,9,17],"numerator_range":[-3,3],"denominators":[1,2,3,4,5,6],
            "scope":"unrelated signed rational coefficient prefixes; finite semantics only, no ordinary-zeta identity asserted"},
        "density_matched_delayed_controls":{"deltas":["1/6","1/4","1/3"],"actual_prefix_cutoff":8192,
            "tail":"actual lambda(n)*(1-n^(-delta)); actual prime-power locations retained at every index",
            "same_all_scale_psi_and_coefficient_diagonal_bounds":True,
            "original_exact_prime_power_weights_preserved":False,"pole_obstruction":"1-delta"},
        "native_shift_log_bridge":{"real_part":4,"heights":["0","7/3","19"],"tail_h":2},
        "native_kernel_points":["7/3","19/2","127/3"],
        "signed_harmonic_calibration":"factorial fractional-part remainder gives -1<=sum_(p^k<x)log(p)/p^k-log x<=C_psi; partial summation gives uniform reciprocal-prime signed tails",
        "coefficient_producer":"factor-free Dirichlet logarithm; real positive qth roots for rational twists; no prime or factor oracle",
        "prior_final_data_is_development_only":True,"model_literature_network_calls":False,
        "historical_priority_is_acceptance_gate":False,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False,
        "remaining_assumptions":["finite rational shift/delay and coefficient budgets","two cumulative channels with independently chosen smooth normalizers",
            "pure power/logarithmic point bounds; negative exponents use exact center certificates",
            "written factorial/Stieltjes and right-shift residue proof backends, not machine-formalized",
            "finite holdout windows; all RH-strength decay hypotheses remain conjectural"]}


def coefficient_vectors(spec):
    out={}
    def add(c,origin):
        c=list(map(Q,c))
        while len(c)>1 and not c[-1]:c.pop()
        key=tuple(c);out.setdefault(key,set()).add(origin)
    for r in spec["monomial_degrees"]:add([0]*r+[1],"monomial")
    values=range(spec["integer_range"][0],spec["integer_range"][1]+1)
    for cs in product(values,repeat=spec["enumerated_degree"]):add([1]+list(cs),"enumerated")
    for v in values:add([0,1,v],"enumerated_leading_shift")
    rng=random.Random(spec["seed"])
    for _ in range(spec["random_draws"]):
        r=rng.randrange(2);degree=rng.randint(r+1,spec["maximum_degree"])
        c=[0]*r+[1]+[Q(rng.randint(*spec["integer_range"]),rng.choice(spec["random_denominators"])) for j in range(r+1,degree+1)]
        add(c,"random")
    return [(list(c),sorted(origins)) for c,origins in sorted(out.items())]


def solve(rows):
    if not rows or not rows[0][1]:return []
    m=len(rows[0][1]);matrix=[[sum(z[i]*z[j]/n for n,z,y in rows)+(1/1024 if i==j else 0) for j in range(m)] for i in range(m)]
    rhs=[sum(y*z[i]/n for n,z,y in rows) for i in range(m)]
    for i in range(m):
        pivot=max(range(i,m),key=lambda j:abs(matrix[j][i]));matrix[i],matrix[pivot]=matrix[pivot],matrix[i];rhs[i],rhs[pivot]=rhs[pivot],rhs[i]
        if abs(matrix[i][i])<1e-14:return [Q(0)]*m
        v=matrix[i][i];matrix[i]=[a/v for a in matrix[i]];rhs[i]/=v
        for j in range(m):
            if j==i:continue
            v=matrix[j][i];matrix[j]=[a-v*b for a,b in zip(matrix[j],matrix[i])];rhs[j]-=v*rhs[i]
    return [Q(round(max(-16,min(16,v))*64),64) for v in rhs]


def programs(spec,f):
    out={};pre=[]
    for channel in spec["channels"]:
        for delta in spec["deltas"]:
            for cs,origins in coefficient_vectors(spec):
                p=canonical(delta,cs,cs,channel);p["origins"]=origins;pre.append(p)
    prefixes,kernels=tables(f,pre,spec["training_points"])
    def add(p,origins):
        pid=digest({k:p[k] for k in canonical(p["delta"],p["coefficients"],p["normalizers"],p["channel"])})
        if pid not in out:
            p.update({"id":pid,"origins":sorted(origins),"coefficient_range_certificate":polynomial_range(p["coefficients"]),
                "weak_uniform_bound":weak_uniform_bound(p,spec["prime_density_constant"]),"exact_center":finite_part_center(p)})
            out[pid]=p
        else:out[pid]["origins"]=sorted(set(out[pid]["origins"])|set(origins))
    for p in pre:
        cs=list(map(Q,p["coefficients"]));r=p["leading_index"];origins=p["origins"]
        add(canonical(p["delta"],cs,cs,p["channel"]),origins+["coupled_normalizer"])
        leading=[Q(0)]*len(cs);leading[r]=1
        add(canonical(p["delta"],cs,leading,p["channel"]),origins+["leading_normalizer"])
        if "random" in origins and r<len(cs)-1:
            rows=[];delta=Q(p["delta"])
            for n in spec["training_points"]:
                target=sum((float((real(c)*prefixes[p["channel"],j*delta][n-1]).mid()) for j,c in enumerate(cs)),0.0)
                target-=float(kernels[p["channel"],Q(p["normalizer_exponents"][r])][str(n)].mid())
                z=[float(kernels[p["channel"],Q(alpha)][str(n)].mid()) for alpha in p["normalizer_exponents"][r+1:]]
                rows.append((n,z,target))
            b=[Q(0)]*r+[Q(1)]+solve(rows)
            add(canonical(p["delta"],cs,b,p["channel"]),origins+["learned_normalizer"])
    return [out[k] for k in sorted(out)]


def slope(points):
    if len(points)<3:return 0.0
    mx=sum(x for x,y in points)/len(points);my=sum(y for x,y in points)/len(points)
    return sum((x-mx)*(y-my) for x,y in points)/sum((x-mx)**2 for x,y in points)


def infer(p,observed,spec):
    values={int(n):flint.arb(v) for n,v in observed.items()}
    offsets=[{"kind":"rational","value":"0"}]
    if p["exact_center"] is not None:offsets.append(p["exact_center"])
    out=[];nu=Q(p["leading_shift"])
    for A in offsets:
        av=offset_value(A)
        for ell in map(Q,spec["log_powers"]):
            growth=slope([(math.log(n),float(abs(v-av).mid().log())-float(ell)*math.log(float((flint.arb.const_e()+n).log().mid()))) for n,v in values.items() if n>=16 and abs(v-av)>0])
            thetas=set(map(Q,spec["theta_grid"]))|{Q(1,2)-nu,Q(1,2)-nu-Q(1,8)}
            thetas|={max(Q(-6),min(Q(2),Q(math.ceil(32*(growth+m)),32))) for m in (0,1/8,1/4)}
            if p["weak_uniform_bound"]["status"].startswith("proved"):thetas.add(Q(p["weak_uniform_bound"]["theta"]))
            for theta in sorted(thetas):
                top=max((abs(v-av)/real(n)**real(theta)/(flint.arb.const_e()+n).log()**real(ell)).upper() for n,v in values.items())
                C=max(Q(1,1024),Q(int((top*2048).ceil().fmpz()),1024))
                tr=transfer(p,theta,ell,C,A)
                c={"program_id":p["id"],"theta":str(theta),"log_power":str(ell),"constant":str(C),"offset":A,
                    "observed_growth_slope":growth,"transfer":tr,"analytic_status":tr["analytic_status"]}
                if tr["analytic_status"].startswith("RH_sufficient"):
                    sigma=Q(tr["ordinary_zeta_exponent"])+Q(spec["cost_line_margin"])
                    cost=recovery_cost(p,tr,sigma,Q(spec["cost_height"]),Q(spec["recovery_terminal_real_part"]))
                    assert cost is not None
                    c.update({"cost_sigma":str(sigma),"cost_height":spec["cost_height"],"full_recovery_cost":cost,
                        "log_reciprocal_cost":float(flint.arb(cost["log_reciprocal_zeta_bound_ball"]).upper())})
                c["id"]=digest({k:c[k] for k in ("program_id","theta","log_power","constant","offset")});out.append(c)
    return out


def state(v,b):return "pass" if v<=b else ("fail" if v>b else "unresolved")


def comparisons(c,values):
    A=offset_value(c["offset"]);theta,ell,C=map(Q,(c[k] for k in ("theta","log_power","constant")))
    return {n:state(abs(flint.arb(v)-A),real(C)*real(n)**real(theta)*(flint.arb.const_e()+real(n)).log()**real(ell)) for n,v in values.items()}


def choose(cs,ps,spec):
    lookup={p["id"]:p for p in ps};out=[];used=set()
    def key(c):
        rank=0 if c["analytic_status"].startswith("RH_sufficient") else (1 if c["analytic_status"].startswith("signed_prime") else 3)
        return (bool(c["validation_failures"] or c["validation_unresolved"]),rank,Q(c["transfer"]["ordinary_zeta_exponent"]),c.get("log_reciprocal_cost",1e100),Q(c["constant"]),c["id"])
    def add(pool):
        pool=[c for c in pool if c["program_id"] not in used]
        if pool:
            c=min(pool,key=key);out.append(c);used.add(c["program_id"])
    add([c for c in cs if lookup[c["program_id"]]["channel"]=="weighted" and lookup[c["program_id"]]["coefficients"]==["1"] and lookup[c["program_id"]]["normalizers"]==["1"] and Q(c["theta"])==Q(1,2) and Q(c["log_power"])==0])
    for channel in spec["channels"]:add([c for c in cs if lookup[c["program_id"]]["channel"]==channel])
    for delta in spec["deltas"]:
        add([c for c in cs if lookup[c["program_id"]]["delta"]==delta and len(lookup[c["program_id"]]["coefficients"])>1 and c["analytic_status"].startswith("RH_sufficient")])
    add([c for c in cs if Q(c["theta"])<0 and c["analytic_status"].startswith("RH_sufficient")])
    add([c for c in cs if Q(c["theta"])<=Q(1,2) and Q(c["transfer"]["ordinary_zeta_exponent"])>Q(1,2) and Q(lookup[c["program_id"]]["leading_shift"])>0])
    add([c for c in cs if c["analytic_status"].startswith("uniform_claim_ruled_out_by_actual")])
    for delta in spec["density_matched_delayed_controls"]["deltas"]:
        add([c for c in cs if lookup[c["program_id"]]["delta"]==delta and lookup[c["program_id"]]["coefficient_range_certificate"]["status"]=="proved_between_zero_and_one" and c["analytic_status"].startswith("uniform_claim_ruled_out_by_shifted")])
    for c in sorted(cs,key=key):
        if len(out)>=spec["archive_size"]:break
        if c["program_id"] not in used:out.append(c);used.add(c["program_id"])
    return out


def discover(directory):
    spec=read(directory/"protocol.json");verify_code(spec);denied=restrict(directory,spec);flint.ctx.prec=spec["precision"]
    f=logarithmic_coefficients(max(spec["training_points"]));ps=programs(spec,f)
    observed=observe(ps,f,spec["training_points"])
    candidates=[c for p in ps for c in infer(p,observed[p["id"]],spec)]
    write(directory/"discovery_data.json",{"complete_point_values":observed,"coefficient_sha256":digest(list(map(str,f))),"coefficient_cutoff":len(f)-1})
    write(directory/"candidate_batch.json",{"programs":ps,"candidates":candidates,"frozen_before_validation":True,"protocol_sha256":digest(spec),"discovery_sha256":sha(directory/"discovery_data.json")})
    f=logarithmic_coefficients(max(spec["validation_points"]));validation=observe(ps,f,spec["validation_points"])
    for c in candidates:
        states=comparisons(c,validation[c["program_id"]]);c["validation_failures"]=[n for n,v in states.items() if v=="fail"];c["validation_unresolved"]=[n for n,v in states.items() if v=="unresolved"]
    write(directory/"validation_data.json",{"complete_point_values":validation,"candidates":candidates,"coefficient_sha256":digest(list(map(str,f))),"coefficient_cutoff":len(f)-1})
    selected=choose(candidates,ps,spec)
    write(directory/"archive.json",{"archive":selected,"worker_access_denials":denied,"final_data_used":False,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False})
    write(directory/"seal.json",{"protocol_sha256":digest(spec),"selection_closed":True,"final_cases_exist_at_seal":False,"files":{n:sha(directory/n) for n in ("protocol.json","discovery_data.json","candidate_batch.json","validation_data.json","archive.json")}})
    print("Sealed",len(selected),"prime-twist decay bounds from",len(ps),"programs /",len(candidates),"estimates",flush=True)


def fresh_cases(spec,seal):
    seed=int.from_bytes(os.urandom(32),"big");rng=random.Random(seed);rule=spec["final_cases"]
    large=sorted(rng.sample(range(rule["large_range"][0],rule["large_range"][1]+1),rule["large_count"]))
    intermediate=sorted(rng.sample(range(rule["irregular_point_range"][0],rule["irregular_point_range"][1]+1),rule["irregular_point_count"]))
    generic=spec["generic_response_calibration"]
    f=["0","0"]+[str(Q(rng.randint(*generic["numerator_range"]),rng.choice(generic["denominators"]))) for _ in range(2,generic["cutoff"]+1)]
    return {"evaluator_seed":str(seed),"large_windows":large,"intermediate_points":intermediate,"points":sorted(set(rule["boundary"]+intermediate+large+[2*X for X in large])),
        "generic_coefficients":f,"generic_points":generic["points"],"created_after_selection_closed":True,"seal_sha256":digest(seal)}


def harmonic_data(f,points,Cp):
    A=[real(0)];S=[real(0)]
    for n in range(1,len(f)):
        A.append(A[-1]+real(f[n])*real(n).log()/n);S.append(S[-1]+real(f[n])/n)
    rows=[]
    for n in points:
        if n<2:continue
        Qvalue=A[n-1]-real(n).log()
        assert Qvalue>=-1 and Qvalue<=real(Cp)
        mertens=S[n-1]-real(n).log().log()-flint.arb.const_euler()
        assert abs(mertens)<=real(Q(Cp)+1)/real(n).log()
        R=sum((real(f[m])*real(m).log()*real(Q(n%m,m)) for m in range(2,n+1) if f[m]),real(0))
        factorial_value=real(math.factorial(n)).log()
        assert (real(n)*A[n]-R).overlaps(factorial_value)
        rows.append({"x":n,"strict_harmonic_residual_ball":serialize(Qvalue),"centered_harmonic_residual_ball":serialize(Qvalue+flint.arb.const_euler()),
            "signed_reciprocal_prime_error_ball":serialize(mertens),"fractional_part_trace_ball":serialize(R),"factorial_ball":serialize(factorial_value)})
    return {"rows":rows,"harmonic_interval":["-1",str(Cp)],"mertens_logarithmic_constant":str(Q(Cp)+1),
        "signed_harmonic_global_theorem_proved":True,"signed_reciprocal_prime_tail_theorem_proved":True,
        "all_scale_real_fractional_orders_nu_ge_one":True,"ordinary_zeta_exponent_after_recovery":"1","RH_sufficient":False,
        "imported_prime_distribution_estimate":False,"analytic_proof_machine_formalized":False}


def final(directory):
    spec=read(directory/"protocol.json");verify_code(spec);seal=read(directory/"seal.json")
    for n,h in seal["files"].items():assert sha(directory/n)==h
    flint.ctx.prec=spec["precision"];path=directory/"final_cases.json"
    if not path.exists():write(path,fresh_cases(spec,seal))
    cases=read(path);assert cases["seal_sha256"]==digest(seal)
    N=max(cases["points"]);f=logarithmic_coefficients(N);arc=read(directory/"archive.json")
    allps=read(directory/"candidate_batch.json")["programs"];used={c["program_id"] for c in arc["archive"]};ps=[p for p in allps if p["id"] in used]
    actual=observe(ps,f,cases["points"]);outcomes=[]
    for c in arc["archive"]:
        states=comparisons(c,actual[c["program_id"]]);outcomes.append({"candidate_id":c["id"],"point_comparisons":states,"finite_points_passed":all(v=="pass" for v in states.values()),"reselected":False,"uniform_signed_premise_proved":False})
    controls=[];cut=spec["density_matched_delayed_controls"]["actual_prefix_cutoff"]
    for delta in spec["density_matched_delayed_controls"]["deltas"]:
        counts=real(0);values=[real(0)]*(N+1)
        for n in range(1,N+1):
            if n>=2:values[n]=real(n).log().ei()-counts
            weight=real(1) if n<=cut else 1-twist(n,Q(delta))
            counts+=real(f[n])*weight
        a=[real(0)]+[values[n]-values[n-1] for n in range(1,N+1)];count,weighted=square_prefix(a)
        observed={}
        for X in cases["large_windows"]:
            energy=complete_energy([["1","1"]],values,X);D=diagonal([["1","1"]],a,count,weighted,X)
            observed[str(X)]={"A2":serialize(energy),"D":serialize(D),"C_off":serialize(energy-D)}
        states={}
        for c in spec["source_unfiltered_moment_obligations"]:
            rho,gamma,B=map(Q,(c[k] for k in ("rho","gamma","constant")))
            states[c["id"]]={X:state(flint.arb(row["C_off"]),real(rho)*flint.arb(row["D"])+real(B)*real(X)**real(gamma)) for X,row in observed.items()}
        controls.append({"delta":delta,"actual_prefix_cutoff":cut,"complete_moments":observed,"source_bound_comparisons":states,
            "same_actual_prime_power_locations_at_every_index":True,"same_all_scale_density_and_diagonal_bounds":True,
            "unmodified_prime_power_weights":False,"uniform_RH_moment_claim_ruled_out_by_shifted_pole":str(1-Q(delta))})
    native=[];rule=spec["native_shift_log_bridge"]
    shifts=sorted({j*Q(p["delta"]) for p in ps for j in range(len(p["coefficients"])) if Q(p["coefficients"][j])})
    for shift in shifts:
        for h in rule["heights"]:
            s=flint.acb(real(rule["real_part"])+real(shift),real(h))
            partial=sum((real(f[n])*flint.acb(twist(n,shift))*(-flint.acb(real(rule["real_part"]),real(h))*real(n).log()).exp() for n in range(2,N+1) if f[n]),flint.acb(0))
            full=s.zeta().log();tail=real(N)**real(-rule["tail_h"])*real(Q(rule["real_part"])+shift-rule["tail_h"]).zeta().log()
            assert abs(full-partial).upper()<tail.lower()
            native.append({"shift":str(shift),"height":h,"log_zeta_ball":[serialize(full.real),serialize(full.imag)],"partial_ball":[serialize(partial.real),serialize(partial.imag)],"tail_ball":serialize(tail)})
    generic=observe(ps,list(map(Q,cases["generic_coefficients"])),cases["generic_points"])
    write(directory/"final_evaluation.json",{"actual_values":actual,"outcomes":outcomes,"density_matched_delayed_controls":controls,
        "generic_response_values":generic,
        "signed_harmonic_calibration":harmonic_data(f,cases["points"],spec["prime_density_constant"]),"native_shift_log_checks":native,
        "coefficient_cutoff":N,"coefficient_sha256":digest(list(map(str,f))),"seal_sha256":digest(seal),"cases_sha256":digest(cases),
        "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False})
    print("Evaluated prime-twist decay and complete density-matched control windows through",N,flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("mode",choices=("run","discover","final"));parser.add_argument("--run-dir",type=Path,required=True);parser.add_argument("--source-run",type=Path)
    args=parser.parse_args();directory=args.run_dir.resolve()
    if args.mode=="run":
        if directory.exists() or args.source_run is None:raise ValueError("A fresh run and verified prime-discrepancy source required")
        directory.mkdir(parents=True);write(directory/"protocol.json",protocol(args.source_run))
        copies=directory/"frozen_source";copies.mkdir()
        for name in CODE:(copies/name).write_bytes((BASE/name).read_bytes())
        for mode in ("discover","final"):subprocess.run([sys.executable,str(Path(__file__)),mode,"--run-dir",str(directory)],check=True,cwd=BASE)
        subprocess.run([sys.executable,str(BASE/"check_prime_twists.py"),"--run-dir",str(directory)],check=True,cwd=BASE)
        from prime_twist_report import publish
        publish(directory)
    elif args.mode=="discover":discover(directory)
    else:final(directory)

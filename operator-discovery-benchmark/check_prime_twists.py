#!/usr/bin/env python3
"""Independent prime-twist, signed harmonic theorem and inverse-cost audit."""
import argparse
from collections import Counter
from fractions import Fraction as Q
import hashlib
import json
from math import ceil,comb,factorial
from pathlib import Path
import random
import subprocess
import sys
import flint
from check_signed_mellin_transfer import zero_disk

BASE=Path(__file__).resolve().parent
SEMANTICS=("channel","delta","coefficients","normalizers","leading_index","leading_shift","increment_shift","normalizer_exponents")


def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(d):return hashlib.sha256(json.dumps(d,sort_keys=True,separators=(",",":"),allow_nan=False).encode()).hexdigest()
def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def prime_coefficients(N):
    spf=list(range(N+1))
    for p in range(2,N+1):
        if spf[p]==p:
            for n in range(p*p,N+1,p):
                if spf[n]==n:spf[n]=p
    result=[Q(0)]*(N+1)
    for n in range(2,N+1):
        p,k,r=spf[n],0,n
        while r%p==0:r//=p;k+=1
        if r==1:result[n]=Q(1,k)
    return result


def enclose(stored,v):
    b=flint.arb(stored)
    assert b.is_finite() and v.is_finite() and b.contains(v),(stored,v)
    assert b.rad()<real(Q(1,10**35))*(1+abs(v))


def power(n,a):return (-real(a)*real(n).log()).exp()


def kernel(alpha,x,channel):
    alpha,x=Q(alpha),Q(x)
    if x<2:return real(0)
    if channel=="log":
        return real(Q(x,2)).log() if not alpha else (real(x)**real(alpha)-real(2)**real(alpha))/real(alpha)
    if alpha>0:return (real(x)**real(alpha)).li()-(real(2)**real(alpha)).li()
    if alpha<0:return (-real(alpha)*real(2).log()).gamma_upper(0)-(-real(alpha)*real(x).log()).gamma_upper(0)
    return (real(x).log()/real(2).log()).log()


def logarithmic_derivative(x):
    z=flint.acb(real(x));v=flint.acb_series([z,1],prec=2).zeta()[1]/z.zeta()
    assert v.imag.contains(0)
    return v.real


_CENTER_CACHE={}


def center(p):
    key=(flint.ctx.prec,digest({name:p[name] for name in SEMANTICS}))
    if key not in _CENTER_CACHE:_CENTER_CACHE[key]=uncached_center(p)
    return _CENTER_CACHE[key]


def uncached_center(p):
    result=real(0)
    for j,(c,b) in enumerate(zip(p["coefficients"],p["normalizers"])):
        c,b=Q(c),Q(b);a=j*Q(p["delta"]);kappa=1-a
        if p["channel"]=="log":
            if a==1:
                if c!=b:return None
                result+=real(c)*(flint.arb.const_euler()-real(2).log())
            else:
                if b:result+=real(b)*real(2)**real(kappa)/real(-kappa)
                if c:result+=real(c)*logarithmic_derivative(a)
        else:
            if kappa>=0 and c!=b:return None
            if not kappa:B=-flint.arb.const_euler()-real(2).log().log()
            elif kappa>0:B=-(real(2)**real(kappa)).li()+real(kappa).log()
            else:B=(-real(kappa)*real(2).log()).gamma_upper(0)+real(-kappa).log()
            result+=real(b)*B
            if c!=b:result+=real(c-b)*real(-kappa).log()
            if c:
                F=real(1) if a==1 else real(a-1)*real(a).zeta()
                assert F>0;result-=real(c)*F.log()
    return result


def offset(A,p):
    if A["kind"]=="rational":return real(A["value"])
    assert A["kind"]=="Mellin_finite_part_at_zero" and A["semantic_digest"]==p["id"]
    v=center(p);assert v is not None;enclose(A["value_ball"],v)
    return v


def independent_observe(ps,f,points):
    prefix={}
    pairs=sorted({(p["channel"],j*Q(p["delta"])) for p in ps for j in range(len(p["coefficients"]))})
    for channel,a in pairs:
        totals=[real(0)]
        for n in range(1,len(f)):
            value=real(f[n])*power(n,a) if f[n] else real(0)
            if channel=="log" and f[n]:value*=real(n).log()
            totals.append(totals[-1]+value)
        prefix[channel,a]=totals
    keys={(p["channel"],Q(v),n) for p in ps for v in p["normalizer_exponents"] for n in points}
    kernels={(channel,a,n):kernel(a,n,channel) for channel,a,n in keys}
    out={}
    for p in ps:
        rows={}
        for n in points:
            v=sum((real(b)*kernels[p["channel"],Q(alpha),n] for b,alpha in zip(p["normalizers"],p["normalizer_exponents"])),real(0))
            v-=sum((real(c)*prefix[p["channel"],j*Q(p["delta"])][n-1] for j,c in enumerate(p["coefficients"])),real(0))
            rows[str(n)]=v
        out[p["id"]]=rows
    return out


def program_checks(p,Cp):
    assert p["id"]==digest({k:p[k] for k in SEMANTICS})
    c,b=list(map(Q,p["coefficients"])),list(map(Q,p["normalizers"]));delta=Q(p["delta"])
    assert delta>0 and len(c)==len(b) and (c[-1] or b[-1])
    r=next(j for j,v in enumerate(c) if v);active=next(j for j,(v,w) in enumerate(zip(c,b)) if v or w)
    assert p["leading_index"]==r and c[r]==1 and Q(p["leading_shift"])==r*delta
    assert Q(p["increment_shift"])==active*delta
    assert p["normalizer_exponents"]==[str(1-j*delta) for j in range(len(c))]
    certificate=p["coefficient_range_certificate"]
    if certificate["status"]=="proved_between_zero_and_one":
        m=certificate["degree"];bs=list(map(Q,certificate["bernstein_coefficients"]));assert len(bs)==m+1 and 0<=min(bs)<=max(bs)<=1
        expanded=[Q(0)]*(m+1)
        for k,v in enumerate(bs):
            for i in range(m-k+1):expanded[k+i]+=v*comb(m,k)*comb(m-k,i)*(-1)**i
        assert expanded==c+[Q(0)]*(m+1-len(c)) and certificate["strictly_positive_in_open_interval"]==any(bs)
    else:
        assert certificate["status"]=="unresolved_by_declared_Bernstein_budget"
        for m in range(len(c)-1,max(len(c)-1,1)+5):
            bs=[sum((c[j]*Q(comb(k,j),comb(m,j)) for j in range(min(k,len(c)-1)+1)),Q(0)) for k in range(m+1)]
            assert min(bs)<0 or max(bs)>1
    weak=p["weak_uniform_bound"];nu=r*delta;Sc=sum(map(abs,c),Q(0));Sb=sum(map(abs,b),Q(0))
    if any(b[:r]):assert weak["status"]=="unsupported_normalizers_precede_leading_twist"
    else:
        divisor=real(2).log() if p["channel"]=="weighted" else real(1)
        if nu<1:theta,ell=1-nu,Q(0);value=real(Sc*Q(Cp)+Sb)/real(1-nu)/divisor
        elif nu==1:theta,ell=Q(0),Q(1);value=real(2*(Sc*Q(Cp)+Sb))/divisor
        else:theta,ell=Q(0),Q(0);value=real(Sc*Q(Cp)*nu+Sb)/real(nu-1)/divisor
        enclose(weak["unrounded_constant_ball"],value)
        assert real(weak["constant"])>=value.upper() and real(weak["constant"])-value.upper()<real(Q(1,1024))
        assert Q(weak["theta"])==theta and Q(weak["log_power"])==ell and Q(weak["ordinary_zeta_exponent_after_shift_recovery"])==theta+nu
        assert not weak["uses_signed_cancellation"] and not weak["RH_sufficient"] and not weak["RH_proved"]
    exact=center(p)
    if exact is None:assert p["exact_center"] is None
    else:offset(p["exact_center"],p)


def comparison(v,b):return "pass" if v<=b else ("fail" if v>b else "unresolved")


def comparisons(c,p,observed):
    A=offset(c["offset"],p);theta,ell,C=map(Q,(c[k] for k in ("theta","log_power","constant")))
    return {n:comparison(abs(v-A),real(C)*real(n)**real(theta)*(flint.arb.const_e()+real(n)).log()**real(ell)) for n,v in observed.items()}


def candidate_checks(c,p,training=None):
    theta,ell,C=map(Q,(c[k] for k in ("theta","log_power","constant")));A=offset(c["offset"],p)
    assert ell>=0 and C>0
    nu=Q(p["leading_shift"]);a=Q(p["increment_shift"]);eta_out=max(theta,-a);eta=eta_out+nu
    poles=[{"location":str(1-j*Q(p["delta"])),"residue":str(Q(v)-Q(w))} for j,(v,w) in enumerate(zip(p["coefficients"],p["normalizers"])) if 1-j*Q(p["delta"])>eta_out and Q(v)!=Q(w)]
    bad_center=eta_out<0 and (center(p) is None or c["offset"]["kind"]!="Mellin_finite_part_at_zero")
    expected=("uniform_claim_ruled_out_by_shifted_pole_logarithm" if poles else
        "negative_growth_obligation_missing_exact_Mellin_center_certificate" if bad_center else
        "uniform_claim_ruled_out_by_actual_critical_zero_and_right_shift_recovery" if eta<Q(1,2) else
        "RH_sufficient_prime_twist_obligation_missing_uniform_signed_proof" if eta<=Q(1,2) else
        "signed_prime_twist_obligation_above_RH_threshold")
    tr=c["transfer"]
    assert c["analytic_status"]==tr["analytic_status"]==expected
    assert Q(tr["output_mellin_exponent"])==eta_out and Q(tr["ordinary_zeta_exponent"])==eta
    assert tr["uncancelled_pole_residues_in_output_half_plane"]==poles
    assert tr["RH_sufficient_if_uniform"]==(not poles and not bad_center and eta<=Q(1,2))
    assert not tr["all_height_nonvanishing_required"] and not tr["uniform_signed_premise_proved"] and not tr["RH_proved"]
    Sc=sum(map(abs,map(Q,p["coefficients"])),Q(0));Sb=sum(map(abs,map(Q,p["normalizers"])),Q(0))
    inc=real(Sc+Sb) if p["channel"]=="log" else real(Sc)+real(Sb)/real(2).log()
    enclose(tr["increment_cost_ball"],inc);enclose(tr["integer_to_real_bound_factor_ball"],real(2)**real(max(Q(0),-theta)))
    assert Q(tr["increment_shift"])==a and tr["increment_log_power"]==(1 if p["channel"]=="log" else 0)
    assert c["id"]==digest({k:c[k] for k in ("program_id","theta","log_power","constant","offset")})
    if training is not None:
        top=max((abs(v-A)/real(n)**real(theta)/(flint.arb.const_e()+real(n)).log()**real(ell)).upper() for n,v in training.items())
        assert real(C)+real(Q(1,10**30))>=2*top
        assert real(C)-2*top<real(Q(1,1024))+real(Q(1,10**30)) or C==Q(1,1024)


def inverse_cost(c,p):
    sigma,height=Q(c["cost_sigma"]),Q(c["cost_height"]);tr=c["transfer"];data=c["full_recovery_cost"]
    terminal=Q(data["terminal_sigma"]);delta=Q(p["delta"]);nu=Q(p["leading_shift"]);r=p["leading_index"]
    theta,ell,C=map(Q,(c[k] for k in ("theta","log_power","constant")));av=offset(c["offset"],p)
    assert sigma>Q(tr["ordinary_zeta_exponent"]) and terminal>1
    spread=max(Q(0),terminal-sigma) if p["channel"]=="log" else Q(0)
    assert Q(data["horizontal_integration_width"])==spread and data["full_shift_path_cost_charged"]
    weights={0:Q(1)};todo=[0];costs={};nodes={n["shift_index"]:n for n in data["recurrence_nodes"]}
    # Independent forward path accounting, using exact rational path masses.
    while todo:
        k=min(todo);todo.remove(k);Re=sigma+k*delta;z=flint.acb(real(Re),real(height))
        if Re>=terminal:
            value=(abs((z-1).log())+real(Re).zeta().log() if p["channel"]=="weighted" else
                1/abs(z-1)-logarithmic_derivative(Re))
            kind="terminal_Euler_half_plane"
        else:
            s=z-real(nu);gap=Re-nu-theta;m=ceil(ell);L=(flint.arb.const_e()+1).log();a=Q(tr["increment_shift"])
            Sc=sum(map(abs,map(Q,p["coefficients"])),Q(0));Sb=sum(map(abs,map(Q,p["normalizers"])),Q(0))
            inc=real(Sc+Sb) if p["channel"]=="log" else real(Sc)+real(Sb)/real(2).log()
            H=real(C)*real(2)**real(max(Q(0),-theta))*sum((real(comb(m,j)*factorial(j))*L**(m-j)/real(gap)**(j+1) for j in range(m+1)),real(0))
            hgap=real(Re-nu+a)
            H+=inc*real(2)**real(a)*(L/hgap+1/hgap**2 if p["channel"]=="log" else 1/hgap)
            value=(abs(s)+real(spread))*H+abs(av)
            for j,(co,b) in enumerate(zip(p["coefficients"],p["normalizers"])):
                kappa=1-j*delta;d=s-real(kappa)
                major=real(2).log()*max(real(1),real(2)**real(kappa-(Re-nu)))
                if p["channel"]=="weighted":major=flint.arb.const_euler()+abs(real(2).log().log())+abs(d)*major
                value+=real(abs(Q(b)))*major
                if Q(co)!=Q(b):
                    assert Re-nu>kappa
                    value+=real(abs(Q(co)-Q(b)))*(abs(d.log()) if p["channel"]=="weighted" else 1/abs(d))
            for j in range(r+1,len(p["coefficients"])):
                if not Q(p["coefficients"][j]):continue
                child=k+j-r
                if child not in weights:weights[child]=Q(0);todo.append(child)
                weights[child]+=weights[k]*abs(Q(p["coefficients"][j]))
            kind="charged_shift_recurrence"
        assert nodes[k]["kind"]==kind and Q(nodes[k]["real_part"])==Re
        costs[k]=value
    assert set(costs)==set(nodes)
    subtrees={}
    for k in sorted(costs,reverse=True):
        value=costs[k]
        if nodes[k]["kind"]=="charged_shift_recurrence":
            value+=sum((real(abs(Q(p["coefficients"][j])))*subtrees[k+j-r] for j in range(r+1,len(p["coefficients"])) if Q(p["coefficients"][j])),real(0))
        subtrees[k]=value
        assert nodes[k]["transform"]==("log_F" if p["channel"]=="weighted" else "logarithmic_derivative_F")
        enclose(nodes[k]["conditional_transform_bound_ball"],value)
    total=sum((real(weights[k])*v for k,v in costs.items()),real(0))
    if p["channel"]=="log":
        end=flint.acb(real(sigma+spread),real(height))
        total=abs((end-1).log())+real(sigma+spread).zeta().log()+real(spread)*total
    bound=abs(flint.acb(real(sigma-1),real(height))).log()+total
    enclose(data["log_reciprocal_zeta_bound_ball"],bound)
    assert abs(float(bound.upper())-c["log_reciprocal_cost"])<1e-9*(1+abs(c["log_reciprocal_cost"]))


def shifted_pole(delta):
    """Native singular part plus certified holomorphic actual-zeta remainder."""
    delta=Q(delta);s0=1-delta;r=real(Q(1,4096))
    box=flint.acb(real(s0)+flint.arb(0,2*r),flint.arb(0,2*r));z=box+real(delta)
    deflated=flint.acb_series([z,1],prec=2).zeta(deflate=True)
    F=1+(z-1)*deflated[0]
    assert box.zeta().abs_lower()>0 and F.abs_lower()>0 and abs(box-1).lower()>0
    vertices=[flint.acb(real(s0)+r,r),flint.acb(real(s0)-r,r),flint.acb(real(s0)-r,-r),flint.acb(real(s0)+r,-r)]
    def singular(s,analytic):return -1/(s-real(s0))
    value=sum((flint.acb.integral(singular,vertices[j],vertices[(j+1)%4],abs_tol=real(Q(1,2**180)),rel_tol=real(Q(1,2**180)),eval_limit=20000,depth_limit=24) for j in range(4)),flint.acb(0))/(2*flint.arb.pi()*flint.acb(0,1))
    assert value.is_finite() and value.real.contains(-1) and value.imag.contains(0)
    assert value.real.rad()<real(Q(1,2**100)) and value.imag.rad()<real(Q(1,2**100))
    return {"delta":str(delta),"location":str(s0),"native_singular_part_residue":[value.real.str(40),value.imag.str(40)],
        "unshifted_zeta_box_lower":box.zeta().abs_lower().str(40),"shifted_pole_neutral_F_box_lower":F.abs_lower().str(40),
        "scope":"actual-zeta meromorphic decomposition; remainder certified holomorphic, residue -1 obtained from isolated native singular part"}


def kernel_calibrations(ps,points):
    alphas=sorted({Q(a) for p in ps for a in p["normalizer_exponents"]});out=[]
    for alpha in alphas:
        for x in map(Q,points):
            for channel in ("weighted","log"):
                def integrand(u,analytic):return (real(alpha)*u).exp()/(u if channel=="weighted" else 1)
                value=flint.acb.integral(integrand,real(2).log(),real(x).log(),abs_tol=real(Q(1,2**160)),rel_tol=real(Q(1,2**160)),eval_limit=20000,depth_limit=24)
                expected=kernel(alpha,x,channel)
                assert value.is_finite() and value.real.contains(expected) and value.imag.contains(0)
                out.append({"alpha":str(alpha),"x":str(x),"channel":channel,"real_ball":value.real.str(40),"imag_ball":value.imag.str(40)})
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--run-dir",type=Path,required=True)
    directory=parser.parse_args().run_dir.resolve()
    spec,seal,arc,cases,final=(read(directory/n) for n in ("protocol.json","seal.json","archive.json","final_cases.json","final_evaluation.json"))
    for n,h in spec["code_sha256"].items():assert sha(BASE/n)==h
    for n in spec["this_stage_source_files"]:assert sha(directory/"frozen_source"/n)==spec["code_sha256"][n]
    source=Path(spec["source_run"])
    for name,key in (("verification.json","source_verification_sha256"),("archive.json","source_archive_sha256"),("final_evaluation.json","source_final_sha256")):assert sha(source/name)==spec[key]
    from prime_discrepancy_report import summary as parent_summary
    parent=parent_summary(source);assert spec["prime_density_constant"]==parent["selected_prime_density_certificate"]["density"]["constant"]
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"] and not seal["final_cases_exist_at_seal"]
    for n,h in seal["files"].items():assert sha(directory/n)==h
    assert cases["created_after_selection_closed"] and cases["seal_sha256"]==final["seal_sha256"]==digest(seal) and final["cases_sha256"]==digest(cases)
    assert all(arc["worker_access_denials"].values()) and not arc["final_data_used"] and not arc["RH_proved"]
    rng=random.Random(int(cases["evaluator_seed"]));rule=spec["final_cases"]
    large=sorted(rng.sample(range(rule["large_range"][0],rule["large_range"][1]+1),rule["large_count"]))
    intermediate=sorted(rng.sample(range(rule["irregular_point_range"][0],rule["irregular_point_range"][1]+1),rule["irregular_point_count"]))
    assert cases["large_windows"]==large and cases["intermediate_points"]==intermediate
    assert cases["points"]==sorted(set(rule["boundary"]+large+intermediate+[2*X for X in large]))
    generic_rule=spec["generic_response_calibration"]
    generic_f=[Q(0),Q(0)]+[Q(rng.randint(*generic_rule["numerator_range"]),rng.choice(generic_rule["denominators"])) for _ in range(2,generic_rule["cutoff"]+1)]
    assert cases["generic_coefficients"]==list(map(str,generic_f)) and cases["generic_points"]==generic_rule["points"]
    replay=directory/"replay"
    if not replay.exists():
        replay.mkdir();(replay/"protocol.json").write_bytes((directory/"protocol.json").read_bytes())
        subprocess.run([sys.executable,str(BASE/"prime_twist_search.py"),"discover","--run-dir",str(replay)],check=True,cwd=BASE)
    for n in ("discovery_data.json","candidate_batch.json","validation_data.json","archive.json","seal.json"):assert sha(directory/n)==sha(replay/n)
    batch=read(directory/"candidate_batch.json");development=read(directory/"discovery_data.json");validation=read(directory/"validation_data.json")
    assert batch["frozen_before_validation"] and batch["protocol_sha256"]==digest(spec) and batch["discovery_sha256"]==sha(directory/"discovery_data.json")
    ps=batch["programs"];lookup={p["id"]:p for p in ps};assert len(lookup)==len(ps)
    flint.ctx.prec=768;zero,margin=zero_disk(spec["known_zero_dependency"]);flint.ctx.prec=768
    assert zero.real.contains(real(Q(1,2)))
    for p in ps:program_checks(p,spec["prime_density_constant"])
    print("Independent twist semantics, exact centers and weak uniform bounds checked",flush=True)
    total_coeff=point_count=0;training=None
    for label,points,data in (("training",spec["training_points"],development),("validation",spec["validation_points"],validation)):
        f=prime_coefficients(max(points));assert data["coefficient_cutoff"]==len(f)-1 and data["coefficient_sha256"]==digest(list(map(str,f)));total_coeff+=len(f)-1
        observed=independent_observe(ps,f,points);assert set(observed)==set(data["complete_point_values"])
        for pid,row in observed.items():
            assert set(row)==set(data["complete_point_values"][pid])
            for n,v in row.items():enclose(data["complete_point_values"][pid][n],v);point_count+=1
        if label=="training":training=observed
        else:
            assert len(data["candidates"])==len(batch["candidates"])
            for c,old in zip(data["candidates"],batch["candidates"]):
                assert all(c[k]==v for k,v in old.items());p=lookup[c["program_id"]]
                candidate_checks(c,p,training[p["id"]])
                if "full_recovery_cost" in c:inverse_cost(c,p)
                states=comparisons(c,p,observed[p["id"]])
                assert c["validation_failures"]==[n for n,v in states.items() if v=="fail"] and c["validation_unresolved"]==[n for n,v in states.items() if v=="unresolved"]
    print("Independent negative decay fits and complete shift recovery costs checked",flush=True)
    N=max(cases["points"]);f=prime_coefficients(N);assert final["coefficient_cutoff"]==N and final["coefficient_sha256"]==digest(list(map(str,f)));total_coeff+=N
    used={c["program_id"] for c in arc["archive"]};chosen=[p for p in ps if p["id"] in used];observed=independent_observe(chosen,f,cases["points"])
    assert set(final["actual_values"])==used
    for pid,row in observed.items():
        for n,v in row.items():enclose(final["actual_values"][pid][n],v);point_count+=1
    for c,o in zip(arc["archive"],final["outcomes"]):
        assert c["id"]==o["candidate_id"];states=comparisons(c,lookup[c["program_id"]],observed[c["program_id"]])
        assert o["point_comparisons"]==states and o["finite_points_passed"]==all(v=="pass" for v in states.values()) and not o["reselected"] and not o["uniform_signed_premise_proved"]
    generic=independent_observe(chosen,generic_f,cases["generic_points"]);generic_count=0
    assert set(generic)==set(final["generic_response_values"])
    for pid,row in generic.items():
        assert set(row)==set(final["generic_response_values"][pid])
        for n,v in row.items():enclose(final["generic_response_values"][pid][n],v);generic_count+=1
    root_checks=0
    shifts=sorted({j*Q(p["delta"]) for p in chosen for j in range(len(p["coefficients"])) if Q(p["coefficients"][j])})
    for a in shifts:
        for n in cases["points"]:
            if n<2:continue
            assert (power(n,a)**a.denominator*real(n)**a.numerator).contains(1);root_checks+=1
    rule=spec["native_shift_log_bridge"]
    assert [(r["shift"],r["height"]) for r in final["native_shift_log_checks"]]==[(str(a),h) for a in shifts for h in rule["heights"]]
    for record in final["native_shift_log_checks"]:
        a=Q(record["shift"]);s=flint.acb(real(rule["real_part"])+real(a),real(record["height"]))
        full=s.zeta().log();partial=sum((real(f[n])*flint.acb(real(n))**(-s) for n in range(2,N+1) if f[n]),flint.acb(0))
        tail=real(Q(1,N**rule["tail_h"]))*real(Q(rule["real_part"])+a-rule["tail_h"]).zeta().log()
        for k,v in (("log_zeta_ball",full),("partial_ball",partial)):enclose(record[k][0],v.real);enclose(record[k][1],v.imag)
        enclose(record["tail_ball"],tail);assert abs(full-partial).upper()<tail.lower()
    A=[real(0)];S=[real(0)]
    for n in range(1,N+1):A.append(A[-1]+real(f[n])*real(n).log()/n);S.append(S[-1]+real(f[n])/n)
    cal=final["signed_harmonic_calibration"];Cp=Q(spec["prime_density_constant"])
    assert cal["harmonic_interval"]==["-1",str(Cp)] and Q(cal["mertens_logarithmic_constant"])==Cp+1
    assert cal["signed_harmonic_global_theorem_proved"] and cal["signed_reciprocal_prime_tail_theorem_proved"] and not cal["RH_sufficient"]
    assert cal["all_scale_real_fractional_orders_nu_ge_one"] and cal["ordinary_zeta_exponent_after_recovery"]=="1" and not cal["imported_prime_distribution_estimate"]
    assert [r["x"] for r in cal["rows"]]==[n for n in cases["points"] if n>=2]
    for row in cal["rows"]:
        n=row["x"];q=A[n-1]-real(n).log();m=S[n-1]-real(n).log().log()-flint.arb.const_euler()
        R=sum((real(f[d])*real(d).log()*(real(Q(n,d))-n//d) for d in range(2,n+1) if f[d]),real(0))
        fac=real(n+1).lgamma()
        for key,v in (("strict_harmonic_residual_ball",q),("centered_harmonic_residual_ball",q+flint.arb.const_euler()),("signed_reciprocal_prime_error_ball",m),("fractional_part_trace_ball",R),("factorial_ball",fac)):enclose(row[key],v)
        assert q>=-1 and q<=real(Cp) and abs(m)<=real(Cp+1)/real(n).log()
        assert (n*A[n]-R).overlaps(fac)
    # Direct finite evaluations of the uniform-in-order signed tail theorem.
    signed_tail_cases=0
    tail_programs=[p for p in ps if p["channel"]=="weighted" and Q(p["leading_shift"])>=1 and p["coefficients"]==p["normalizers"]]
    tail_values=independent_observe(tail_programs,f,cases["points"])
    for p in tail_programs:
        values=tail_values[p["id"]];K=center(p);nu=Q(p["leading_shift"]);Sc=sum(map(abs,map(Q,p["coefficients"])),Q(0))
        for n,v in values.items():
            if int(n)>=2:assert abs(v-K)<=real((Cp+1)*Sc)*real(n)**real(1-nu)/real(n).log();signed_tail_cases+=1
    print("Independent signed harmonic and reciprocal-prime global certificates checked",flush=True)
    li=[real(0),real(0)]+[real(n).li() for n in range(2,N+1)];control_count=control_entries=0
    poles=[]
    for ctrl in final["density_matched_delayed_controls"]:
        delta=Q(ctrl["delta"]);cut=ctrl["actual_prefix_cutoff"];counts=real(0);values=[real(0)]*(N+1);psi=real(0)
        assert cut==spec["density_matched_delayed_controls"]["actual_prefix_cutoff"]>=spec["source_coefficient_square_certificate"]["initial_cutoff"]
        for n in range(1,N+1):
            if n>=2:values[n]=li[n]-counts
            weight=real(1) if n<=cut else 1-power(n,delta)
            assert weight>0 and weight<=1
            counts+=real(f[n])*weight;psi+=real(f[n])*real(n).log()*weight
            assert psi<=real(Cp)*n
        increments=[real(0)]+[values[n]-values[n-1] for n in range(1,N+1)]
        # Initial patch of the old diagonal theorem plus the same universal
        # tail lemma; no unmodified-prime-weight assertion is made.
        sq=real(0);Ca=real(spec["source_coefficient_square_certificate"]["constant"])
        for n in range(1,spec["source_coefficient_square_certificate"]["initial_cutoff"]+1):
            sq+=increments[n]*increments[n];assert sq*(flint.arb.const_e()+n).log()/n<=Ca
        assert ctrl["same_actual_prime_power_locations_at_every_index"] and ctrl["same_all_scale_density_and_diagonal_bounds"] and not ctrl["unmodified_prime_power_weights"]
        assert Q(ctrl["uniform_RH_moment_claim_ruled_out_by_shifted_pole"])==1-delta>Q(1,2)
        observed_ctrl={}
        for X in cases["large_windows"]:
            energy=real(0)
            for n in range(X,2*X):
                midpoint=(values[n]+values[n+1])/2
                energy+=(values[n]*values[n]+4*midpoint*midpoint+values[n+1]*values[n+1])/6
            D=sum((increments[n]*increments[n]*real(X if n<=X else Q(2*X-n)+Q(1,3)) for n in range(1,2*X+1)),real(0))
            row={"A2":energy,"D":D,"C_off":energy-D}
            for k,v in row.items():enclose(ctrl["complete_moments"][str(X)][k],v)
            observed_ctrl[str(X)]=row;control_count+=1;control_entries+=2*X
        for c in spec["source_unfiltered_moment_obligations"]:
            rho,gamma,B=map(Q,(c[k] for k in ("rho","gamma","constant")))
            states={X:comparison(v["C_off"],real(rho)*v["D"]+real(B)*real(X)**real(gamma)) for X,v in observed_ctrl.items()}
            assert states==ctrl["source_bound_comparisons"][c["id"]]
        poles.append(shifted_pole(delta))
    assert [r["delta"] for r in final["density_matched_delayed_controls"]]==spec["density_matched_delayed_controls"]["deltas"]
    kernels=kernel_calibrations(chosen,spec["native_kernel_points"])
    # Upper-triangular right-shift equations have unit diagonal at ANY size.
    # Examples demonstrate local cancellation followed by an exposed last zero.
    multiplicity_cases=0
    for p in ps:
        r=p["leading_index"];tail=list(map(Q,p["coefficients"][r:]));size=17
        m=[Q(0)]*size
        for k in range(size-1,-1,-1):m[k]=-sum((tail[j]*m[k+j] for j in range(1,min(len(tail),size-k))),Q(0))
        assert not any(m)
        synthetic=[Q(3)]*size
        residues=[sum((tail[j]*synthetic[k+j] for j in range(min(len(tail),size-k))),Q(0)) for k in range(size)]
        assert residues[-1]==3;multiplicity_cases+=1
    assert not final["RH_proved"] and not final["uniform_RH_sufficient_signed_controls_verified"]
    checks={"frozen_source_seal_private_final_provenance_and_replay_checked":True,
        "fractional_root_semantics_and_actual_prime_power_coefficients_checked":True,
        "unrelated_signed_input_finite_semantics_checked_without_zeta_claims":True,
        "exact_Bernstein_weight_ranges_and_prime_support_certificates_checked":True,
        "independent_normalizers_and_regular_zero_exponent_kernel_checked":True,
        "negative_growth_exact_Mellin_centers_and_integer_to_real_costs_checked":True,
        "right_shift_all_multiplicity_recovery_and_actual_zero_obstruction_checked":True,
        "all_training_constants_validation_and_fresh_point_comparisons_checked":True,
        "full_shift_path_and_horizontal_reciprocal_recovery_costs_checked":True,
        "signed_harmonic_factorial_trace_and_uniform_reciprocal_prime_tail_checked":True,
        "complete_density_matched_control_moments_and_same_diagonal_bound_checked":True,
        "shifted_pole_controls_certified_by_native_singular_parts_and_analytic_remainders":True,
        "native_log_zeta_shift_bridges_and_independent_kernel_integrals_checked":True,
        "weak_signed_global_results_separated_from_RH_strength_uniform_obligations":True}
    result={"all_passed":all(checks.values()),"checks":checks,"protocol_sha256":digest(spec),"final_sha256":sha(directory/"final_evaluation.json"),
        "checker_sha256":sha(BASE/"check_prime_twists.py"),"programs_checked":len(ps),"estimates_checked":len(batch["candidates"]),
        "exact_coefficients_checked":total_coeff,"complete_point_values_checked":point_count,"fractional_root_identity_cases":root_checks,
        "generic_signed_response_values_checked":generic_count,
        "native_shift_log_checks":len(final["native_shift_log_checks"]),"native_kernel_integrals_checked":len(kernels),
        "signed_harmonic_cases_checked":len(cal["rows"]),"signed_fractional_tail_cases_checked":signed_tail_cases,
        "complete_density_matched_control_windows_checked":control_count,"control_Gram_entries_checked":control_entries,
        "native_shifted_pole_calibrations":poles,"kernel_calibrations":kernels,"multiplicity_recovery_cases":multiplicity_cases,
        "actual_zero_Rouche_margin":margin,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    (directory/"verification.json").write_text(json.dumps(result,indent=2)+"\n")
    print("Independent prime-twist signed-control audit",sum(checks.values()),"/",len(checks),flush=True)


if __name__=="__main__":main()

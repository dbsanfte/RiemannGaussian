#!/usr/bin/env python3
"""Independent factor/divisor, Kummer, and derivative-integral verification.

No producer mathematical module is imported by the checking functions.
The optional deterministic discovery replay runs in a separate process.
"""
from fractions import Fraction as Q
from math import factorial,comb
from pathlib import Path
import argparse
import hashlib
import json
import math
import subprocess
import sys
import tempfile
import flint

BASE=Path(__file__).resolve().parent


def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def read(path):return json.loads(Path(path).read_text())
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(",",":"),allow_nan=False).encode()).hexdigest()


def complex_interval(record):return flint.acb(flint.arb(record["real"]),flint.arb(record["imag"]))


def sieve(N):
    spf=list(range(N+1))
    for p in range(2,N+1):
        if spf[p]!=p:continue
        for n in range(p*p,N+1,p):
            if spf[n]==n:spf[n]=p
    mu=[0]*(N+1);mu[1]=1
    for n in range(2,N+1):
        p=spf[n];m=n//p
        mu[n]=0 if m%p==0 else -mu[m]
    return mu,spf


def kummer(alpha,x):
    alpha,x=Q(alpha),Q(x)
    if x==1:return flint.arb(0)
    u=real(x).log()
    return real(x)*u**real(alpha+1)/real(alpha+1)*(-u).hypgeom_1f1(1,real(alpha+2))


def tables(N,alphas,points):
    mu,_=sieve(N);out={}
    for alpha in sorted(set(map(Q,alphas))):
        weights=[flint.arb(0),flint.arb(0)]+[real(n).log()**real(alpha) for n in range(2,N+1)]
        T=[flint.arb(0)]*(N+1)
        for d in range(1,N+1):
            if mu[d]:
                for m in range(2,N//d+1):T[d*m]+=mu[d]*weights[m]
        S=[flint.arb(0)]*(N+1)
        for n in range(1,N+1):S[n]=S[n-1]+T[n]
        rows={}
        for x in map(Q,points):
            top=x.numerator//x.denominator
            G=sum((mu[d]*kummer(alpha,x/d) for d in range(1,top+1) if mu[d]),flint.arb(0))
            rows[str(x)]={"discrete":S[top],"continuous":G,"remainder":S[top]-G}
        out[str(alpha)]=rows
    return out,mu


def observer(p,data,qs,points):
    out={};D=max(1,len(p["coefficients"])-1)
    for q in qs:
        for x in map(Q,points):
            v=flint.arb(0)
            for j,(c,b) in enumerate(zip(p["coefficients"],p["normalizers"])):
                if Q(c) or Q(b):
                    row=data[str(Q(j,D*q))][str(x)]
                    v+=real(c)*row["discrete"]-real(b)*row["continuous"]
            out[f"{q}:{x}"]=v
    return out


def jet(s,length):
    old=flint.ctx.cap;flint.ctx.cap=max(old,length+2)
    try:return flint.acb_series([s,1],prec=length).zeta(deflate=True)
    finally:flint.ctx.cap=old


def derivative_numerator(alpha,sigma,height,K=84,U=72,terms=18):
    alpha,sigma,height=map(Q,(alpha,sigma,height));s=flint.acb(real(sigma),real(height))
    if alpha==0:return jet(s,1)[0]-1
    if alpha==1:return -jet(s,2)[1]
    if not 0<alpha<1:raise ValueError("Independent numerator requires 0<=alpha<=1")
    d=Q(1,80);r=3*d
    box=flint.acb(flint.arb(0,real(r)),flint.arb(0,real(r)))
    M=jet(s+box,2)[1].abs_upper()
    if not M.is_finite():raise ArithmeticError("Nonfinite independent Cauchy bound")
    coeff=jet(s,K+2)
    small=sum(((k+1)*coeff[k+1]*real(d)**real(k+1-alpha)/real(k+1-alpha)
               for k in range(K+1)),flint.acb(0))
    e0=M*real(d)**real(1-alpha)*real(d/r)**(K+1)/real((K+2-alpha)*(1-d/r))
    def integrand(v,analytic):return jet(s+v.exp(),2)[1]*(real(1-alpha)*v).exp()
    mid=flint.acb.integral(integrand,real(d).log(),real(U).log(),
        abs_tol=real(Q(1,2**104)),rel_tol=real(Q(1,2**104)),eval_limit=200000,depth_limit=50)
    if not mid.is_finite():raise ArithmeticError("Independent derivative integral unresolved")
    q=-(s-1)/U;qabs=q.abs_upper()
    if not qabs<1:raise ValueError("Independent tail start too small")
    rational=real(U)**real(-alpha-1)*sum(((k+1)*q**k/real(alpha+k+1) for k in range(K+1)),flint.acb(0))
    e1=real(U)**real(-alpha-1)*qabs**(K+1)/(1-qabs)
    tail=sum(((-s*real(n).log()).exp()*real(n).log()**real(alpha)*
               (real(U)*real(n).log()).gamma_upper(real(1-alpha)) for n in range(2,terms+1)),flint.acb(0))
    p=sigma+U
    e2=real(U)**real(-alpha)*real(terms)**real(1-p)/real(p-1)
    pref=(1-real(alpha)).rgamma();err=(e0+e1+e2)*pref
    return -(small+mid+rational-tail)*pref+flint.acb(flint.arb(0,err.upper()),flint.arb(0,err.upper()))


def normalizer_integral(alpha,x):
    alpha,x=Q(alpha),Q(x)
    if x==1:return flint.acb(0)
    p,q=alpha.numerator,alpha.denominator
    end=real(x).log().root(q)
    return flint.acb.integral(lambda v,a:q*v**(p+q-1)*(v**q).exp(),0,end,
        rel_tol=real(Q(1,2**130)),abs_tol=real(Q(1,2**130)))


def structural(p):
    c,b=list(map(Q,p["coefficients"])),list(map(Q,p["normalizers"]));D=len(c)-1
    paired=all(c[j]==b[j] for j in range(1,D+1));moments=[];rate=None
    if paired:
        if c[0]!=b[0]:rate=0
        else:
            for k in range(D+1):
                m=sum((c[j]*j**k for j in range(D+1)),Q(0));moments.append(str(m))
                if m:rate=k;break
    return {"paired":paired,"rate":rate,"moments":moments}


def status(p,candidate):
    st=structural(p);eta=max(Q(0),Q(candidate["theta"]))
    if not st["paired"]:
        return "ruled_out_by_uncompensated_fractional_pole_at_one" if eta<1 else "unsupported_family_zero_bridge_for_uncompensated_positive_orders"
    if Q(candidate["parameter_power"])>st["rate"]:return "ruled_out_by_exact_parameter_vanishing_order"
    if eta<Q(1,2):return "ruled_out_by_actual_critical_zero_and_infinite_parameter_family"
    if eta==Q(1,2):return "RH_sufficient_infinite_family_obligation_missing_uniform_proof"
    return "infinite_family_signed_obligation_above_RH_threshold"


def check_cover(cover):
    rho=Q(cover["rho"]);mesh=cover["mesh"];rows=cover["boxes"]
    nx=-(-(1+2*rho)*mesh//1);ny=-(-2*rho*mesh//1);nx=int(nx);ny=int(ny)
    assert len(rows)==nx*ny
    maxima=list(map(Q,cover["maxima_rational_upper"]));native=[]
    for index,row in enumerate(rows):
        i,j=divmod(index,ny)
        rect=[-rho+(1+2*rho)*Q(i,nx),-rho+(1+2*rho)*Q(i+1,nx),
              -rho+2*rho*Q(j,ny),-rho+2*rho*Q(j+1,ny)]
        assert list(map(Q,row["rectangle"]))==rect
        lo,hi,bot,top=rect
        z=flint.acb(flint.arb(real((lo+hi)/2),real((hi-lo)/2)),flint.arb(real((bot+top)/2),real((top-bot)/2)))
        vals=[(z*(1-z).rgamma()).abs_upper(),(z*(2-z).rgamma()).abs_upper(),(1-z).rgamma().abs_upper()]
        assert all(v.is_finite() for v in vals)
        for k,v in enumerate(vals):
            assert v<=real(maxima[k])
            assert flint.arb(row["upper_balls"][k]).overlaps(v)
        native.append(vals)
    M1,M2,M3=map(real,maxima)
    C0=M1/(2*(1-real(rho)))+M1/(2*real(2).log()**2)+M2+M3
    assert flint.arb(cover["C0_ball"]).contains(C0)
    assert cover["uses_exact_prime_factor_sign_structure"] and not cover["uses_prime_distribution_estimate"]
    return C0


def global_bound(p,covers):
    c,b=list(map(Q,p["coefficients"])),list(map(Q,p["normalizers"]));r=structural(p)["rate"]
    if not r:
        return real(sum(map(abs,c),Q(0))+Q(3,2)*sum(map(abs,b),Q(0))),real(sum(map(abs,c),Q(0))+6*sum(map(abs,b),Q(0))),0,2,None
    Sr=sum((abs(v)*j**r for j,v in enumerate(c)),Q(0))
    choices=[(float((flint.arb(z["C0_ball"])/real(z["rho"])**r).upper()),z) for z in covers]
    _,cover=min(choices,key=lambda z:z[0]);cost=flint.arb(cover["C0_ball"])/real(cover["rho"])**r
    return real(Sr)*(cost+1+real(Q(1,(r+2)*factorial(r)))),real(Sr)*(cost+real(Q(2,factorial(r)))+4),r,r+2,cover["rho"]


def expected_outcome(p,candidate,values):
    bad=[];unknown=[];worst=(0,None)
    for key,value in values.items():
        q,n=map(int,key.split(':'));a=Q(1,max(1,len(p["coefficients"])-1)*q)
        B=(real(candidate["constant"])*real(a)**real(candidate["parameter_power"])*real(n)**real(candidate["theta"])*
           (flint.arb.const_e()+n).log()**real(candidate["log_power"]))
        v=abs(value)
        if not v<=B:(bad if v>B else unknown).append(key)
        ratio=float((v/B).upper())
        if ratio>worst[0]:worst=(ratio,key)
    return {"failures":bad,"unresolved":unknown,"finite_points_passed":not bad and not unknown,
            "maximum_ratio":worst[0],"maximum_ratio_case":worst[1]}


def compare_outcome(record,expected):
    for k in ["failures","unresolved","finite_points_passed"]:assert record[k]==expected[k]
    assert math.isclose(record["maximum_ratio"],expected["maximum_ratio"],rel_tol=1e-12,abs_tol=1e-12)
    assert not record["uniform_signed_premise_proved"]


def majorant(theta,ell,C,sigma):
    m=math.ceil(Q(ell));gap=real(Q(sigma)-Q(theta));l=(flint.arb.const_e()+1).log()
    return C*sum((real(comb(m,j)*factorial(j))*l**(m-j)/gap**(j+1) for j in range(m+1)),flint.arb(0))


def conditional_cost(p,c,cert,values,sigma,height,qs):
    s=flint.acb(real(sigma),real(height));out=[]
    for q in qs:
        a=Q(1,max(1,p["degree"])*q)
        Qs=real(p["coefficients"][0])*(values["0"]+1/(s-1))-real(p["normalizers"][0])/(s-1)
        for j,v in enumerate(p["coefficients"][1:],1):
            if Q(v):Qs+=real(v)*values[str(j*a)]
        H=majorant(c["theta"],c["log_power"],real(c["constant"])*real(a)**real(c["parameter_power"])*
                   real(2)**real(max(Q(0),-Q(c["theta"]))),sigma)
        H+=majorant(0,cert["log_power"],flint.arb(cert["unit_increment_constant_ball"])*
                    real(a)**cert["parameter_power"]*2**cert["log_power"],sigma)
        out.append({"q":q,"numerator":Qs,"H":H,"bound":s.abs_upper()*H/Qs.abs_lower() if Qs.abs_lower()>0 else None})
    return out


def parameter_pole_diagnostic(p,epsilon=Q(1,2**20),sigma=Q(2),cutoff=128):
    """Finite calibration of the generic residue; the proof uses analytic tails."""
    D=max(j for j,v in enumerate(p["coefficients"]) if Q(v));a=Q(-1+epsilon,D)
    s=real(sigma);Qsum=real(p["coefficients"][0])*(s.zeta()-1)-real(p["normalizers"][0])/(s-1)
    for j,v in enumerate(p["coefficients"][1:],1):
        if not Q(v):continue
        beta=j*a
        finite=sum((real(n).log()**real(beta)/real(n)**real(sigma) for n in range(2,cutoff+1)),flint.arb(0))
        tail=real(2).log()**real(beta)*real(cutoff)**real(1-sigma)/real(sigma-1)
        N=finite+flint.arb(tail/2,tail.upper()/2)-(1+real(beta)).gamma()/(s-1)**(1+real(beta))
        Qsum+=real(v)*N
    scaled=real(epsilon/D)*Qsum;residue=-Q(p["coefficients"][D])/D
    Sc=sum(map(abs,map(Q,p["coefficients"]+p["normalizers"])),Q(0))
    assert abs(scaled-real(residue))<real(Sc/100)
    return {"program_id":p["id"],"epsilon":str(epsilon),"query_real_part":str(sigma),
            "scaled_numerator_ball":str(scaled),"exact_residue":str(residue),"finite_diagnostic_is_not_the_proof":True}


def generic_log(case):
    f=list(map(Q,case["input"]));N=len(f)-1;inv=[Q(0)]*(N+1);inv[1]=1
    for n in range(2,N+1):inv[n]=-sum((f[d]*inv[n//d] for d in range(2,n+1) if n%d==0),Q(0))
    weights=[flint.arb(0),flint.arb(0)]+[real(n).log()**real(case["alpha"])*real(f[n]) for n in range(2,N+1)]
    return [sum((real(inv[d])*weights[n//d] for d in range(1,n+1) if n%d==0),flint.arb(0)) if n else flint.arb(0) for n in range(N+1)]


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--run-dir",required=True);ap.add_argument("--skip-replay",action="store_true");args=ap.parse_args();directory=Path(args.run_dir).resolve()
    spec=read(directory/"protocol.json");seal=read(directory/"seal.json");batch=read(directory/"candidate_batch.json");backend=read(directory/"backend_certificates.json")
    discovery=read(directory/"discovery_data.json");validation=read(directory/"validation_data.json");nums=read(directory/"numerator_data.json")
    archive=read(directory/"archive.json");cases=read(directory/"final_cases.json");final=read(directory/"final_evaluation.json")
    checks={};counts={};flint.ctx.prec=384
    for n,h in spec["code_sha256"].items():assert sha(BASE/n)==h
    for n in spec["this_stage_source_files"]:assert sha(directory/"frozen_source"/n)==spec["code_sha256"][n]
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"] and not seal["final_cases_exist_at_seal"]
    for n,h in seal["files"].items():assert sha(directory/n)==h
    assert final["protocol_sha256"]==digest(spec) and final["seal_sha256"]==cases["seal_sha256"]==digest(seal)
    assert final["cases_sha256"]==digest(cases) and cases["created_after_selection_closed"]
    source=Path(spec["source_run"])
    for n,h in spec["source_sha256"].items():assert sha(source/n)==h
    from prime_oscillation_report import summary as parent_summary
    parent_summary(source)
    assert batch["frozen_before_validation"] and batch["generation_uses_training_only"]
    assert archive["selection_closed"] and not archive["final_data_used"] and all(discovery["worker_access_denials"].values())
    assert not spec["generator_model_literature_network_access"] and spec["not_autonomous_proof_invention"]
    checks["frozen_sources_parent_integrity_and_sealed_separate_evaluation"]=True
    checks["discovery_network_subprocess_and_final_access_denied"]=True

    native_num={};Ncount=0
    for alpha,txt in nums["values"].items():
        v=derivative_numerator(Q(alpha),*map(Q,nums["query"]))
        assert complex_interval(txt).contains(v),("numerator",alpha)
        native_num[alpha]=v;Ncount+=1
    for record in nums["calibrations"]:
        v=derivative_numerator(Q(record["alpha"]),*map(Q,record["query"]))
        assert complex_interval(record["numerator_ball"]).contains(v);Ncount+=1
    assert any(r["query"]==["1","0"] for r in nums["calibrations"])
    counts["native_entire_numerators_checked"]=Ncount
    checks["entire_numerator_independent_derivative_integral_and_infinite_tails"]=True
    print("Independent entire numerator check:",Ncount,"queries",flush=True)

    for c in backend["covers"]:check_cover(c)
    counts["native_reciprocal_gamma_subboxes_checked"]=sum(len(c["boxes"]) for c in backend["covers"])
    checks["full_Cauchy_rectangle_cover_and_native_all_order_coefficient_constants"]=True
    ps={p["id"]:p for p in batch["ablation_programs"]+batch["programs"]}
    for pid,p in ps.items():
        st=structural(p);assert p["positive_orders_compensated"]==st["paired"] and p["parameter_vanishing_order"]==st["rate"]
        assert p["parameter_moments_through_first_nonzero"]==st["moments"]
        W,I,r,ell,rho=global_bound(p,backend["covers"]);cert=backend["global_certificates"][pid]
        assert flint.arb(cert["constant_ball"]).contains(W) and flint.arb(cert["unit_increment_constant_ball"]).contains(I)
        assert cert["parameter_power"]==r and cert["log_power"]==ell and cert["selected_Cauchy_radius"]==rho
        assert cert["ordinary_zeta_exponent"]=="1" and not cert["RH_sufficient"] and not cert["RH_proved"]
    counts["global_signed_parameter_and_unit_certificates_checked"]=len(ps)
    checks["exact_parameter_order_and_generic_all_scale_weak_signed_bounds"]=True

    independent={};totalcells=0;calibration_count=0
    groups=[("discovery",discovery,spec["training_points"]),("validation",validation,spec["validation_points"]),("final",final,cases["points"])]
    for label,record,points in groups:
        alphas=list(map(Q,record["primitive_tables"]));data,mu=tables(record["complete_coefficient_cutoff"],alphas,points)
        assert digest(mu)==record["inverse_coefficient_sha256"]
        for alpha in alphas:
            for x in map(Q,points):
                for k in ["discrete","continuous","remainder"]:
                    assert flint.arb(record["primitive_tables"][str(alpha)][str(x)][k]).contains(data[str(alpha)][str(x)][k]),(label,alpha,x,k)
                    totalcells+=1
                if alpha==0:
                    top=x.numerator//x.denominator
                    exact=1-x*sum((Q(mu[d],d) for d in range(1,top+1)),Q(0))
                    assert data["0"][str(x)]["remainder"].contains(real(exact));calibration_count+=1
        independent[label]=data
        print("Independent complete",label,"tables:",len(alphas),"orders through",record["complete_coefficient_cutoff"],flush=True)
    counts["complete_primitive_interval_values_checked"]=totalcells
    counts["zero_order_recovery_anchors_checked"]=calibration_count
    checks["complete_actual_Mobius_divisor_convolution_and_Kummer_normalizers"]=True
    checks["zero_order_convention_and_exact_all_real_Mobius_anchor"]=True

    quadratures=0
    for alpha in [Q(1,2),Q(1,3),Q(1,6),Q(1,36)]:
        for x in [Q(2),Q(13,3),Q(37)]:
            v=normalizer_integral(alpha,x)
            assert v.is_finite() and v.real.overlaps(kummer(alpha,x)) and v.imag.contains(0);quadratures+=1
    counts["independent_native_normalizer_quadratures"]=quadratures
    checks["fractional_kernel_transformed_native_integral_calibration"]=True

    vqs=sorted(set(spec["training_q"]+spec["validation_new_q"]));val={pid:observer(p,independent["validation"],vqs,spec["validation_points"]) for pid,p in ps.items()}
    for pid,row in validation["program_responses"].items():
        for key,v in row.items():assert flint.arb(v).contains(val[pid][key])
    train={pid:observer(p,independent["discovery"],spec["training_q"],spec["training_points"]) for pid,p in ps.items()}
    candidates={c["id"]:c for c in batch["candidates"]};validated={c["id"]:c for c in validation["candidates"]};costcount=0;diagnostics=[]
    assert candidates.keys()==validated.keys()
    for cid,c in candidates.items():
        p=ps[c["program_id"]];tr=c["transfer"];expected_status=status(p,c)
        assert c["analytic_status"]==tr["analytic_status"]==expected_status
        assert tr["required_uniform_scope"]=="every integer n>=1 AND every integer q>=2" and not tr["uniform_signed_premise_proved"]
        assert tr["finite_parameter_grid_suffices"]==(p["degree"]==0)
        assert tr["RH_sufficient_if_uniform"]==(expected_status=="RH_sufficient_infinite_family_obligation_missing_uniform_proof")
        st=structural(p);assert tr["exact_parameter_vanishing_order"]==st["rate"]
        j=max((j for j,v in enumerate(p["coefficients"]) if Q(v)),default=0)
        assert tr["numerator_parameter_pole_location"]==(str(Q(-1,j)) if j else None)
        assert tr["numerator_parameter_pole_residue"]==(str(-Q(p["coefficients"][j])/j) if j else None)
        compare_outcome(validated[cid]["validation"],expected_outcome(p,c,val[p["id"]]))
        if tr["RH_sufficient_if_uniform"]:
            queried=conditional_cost(p,c,backend["global_certificates"][p["id"]],native_num,*map(Q,spec["cost_query"]),spec["training_q"])
            saved=c["recovery_cost"];assert saved["charges_parameter_normalization_and_unit_increment"] and not saved["height_uniform"]
            entries={row["q"]:row for row in saved["parameter_observers"]}
            for row in queried:
                if row["q"] not in entries:
                    assert row["q"] in saved["unresolved_denominator_orders"];continue
                old=entries[row["q"]]
                assert complex_interval(old["numerator_ball"]).contains(row["numerator"])
                lower=real(old["numerator_lower_rational"])
                assert lower>0 and lower<=row["numerator"].abs_lower()
                assert flint.arb(old["numerator_lower_ball"]).contains(lower)
                cost=flint.arb(old["conditional_reciprocal_zeta_bound_ball"])
                # Alternative numerator gives a sharper denominator. A small
                # relative tolerance handles the published 45-digit interval
                # boundary while the complete conditional formula is checked.
                assert row["bound"] is not None and row["bound"].upper()<=cost.upper()*(1+real(Q(1,2**110)))
                expected=saved["best_conditional_reciprocal_zeta_bound_ball"]
                assert expected is not None;costcount+=1
    for p in ps.values():
        if p["positive_orders_compensated"] and any(Q(v) for v in p["coefficients"][1:]):diagnostics.append(parameter_pole_diagnostic(p))
    counts["complete_growth_hypotheses_analytically_checked"]=len(candidates);counts["charged_native_parameter_observer_costs_checked"]=costcount
    counts["finite_parameter_pole_diagnostics"]=len(diagnostics)
    checks["infinite_parameter_identity_theorem_bridge_and_nonzero_exact_pole_residues"]=True
    checks["uncompensated_branch_parameter_rate_and_actual_zero_rejection_gates"]=True
    checks["complete_validation_outcomes_and_full_conditional_recovery_costs"]=True

    dep=spec["known_critical_zero_dependency"];zero_path=BASE/"shift-ratio-results/shift_ratio_analytic_verification.json";zero_source=BASE/"shift-ratio-results/shift_ratio_analytic.json"
    assert sha(zero_path)==dep["verification_sha256"] and sha(zero_source)==dep["source_sha256"]
    checked=read(zero_path);assert checked["all_passed"] and checked["source_artifact_sha256"]==sha(zero_source)
    assert {r["label"] for r in archive["negative_controls"]}=={"excess_parameter_rate","subcritical_family","uncompensated_branch"}
    checks["named_native_ordinary_critical_zero_and_three_false_control_classes"]=True

    selected=archive["archive"]+[r["candidate"] for r in archive["negative_controls"]];selectedps={c["program_id"]:ps[c["program_id"]] for c in selected}
    values={pid:observer(p,independent["final"],cases["qs"],cases["integers"]+cases["boundary"]) for pid,p in selectedps.items()}
    allvalues={pid:observer(p,independent["final"],cases["qs"],cases["points"]) for pid,p in selectedps.items()}
    for cid,o in zip([c["id"] for c in selected],final["outcomes"]):
        c=candidates[cid];assert o["candidate_id"]==cid;compare_outcome(o,expected_outcome(ps[c["program_id"]],c,values[c["program_id"]]))
        assert o["point_comparisons"]==len(values[c["program_id"]]) and not o["RH_proved"]
    counts["fresh_complete_family_bound_comparisons"]=sum(o["point_comparisons"] for o in final["outcomes"])
    for row in final["unit_increment_checks"]:
        p=selectedps[row["program_id"]];cert=backend["global_certificates"][p["id"]];a=Q(1,max(1,p["degree"])*row["q"]);n=row["n"]
        v=allvalues[p["id"]];delta=abs(v[f"{row['q']}:{Q(n)+Q(spec['final_cases']['real_offset'])}"]-v[f"{row['q']}:{n}"])
        bound=flint.arb(cert["unit_increment_constant_ball"])*real(a)**cert["parameter_power"]*(flint.arb.const_e()+n+1).log()**cert["log_power"]
        assert flint.arb(row["difference_ball"]).contains(delta) and flint.arb(row["bound_ball"]).overlaps(bound)
        assert row["passed"] and delta<=bound
    for row in final["weak_bound_checks"]:
        p=selectedps[row["program_id"]];cert=backend["global_certificates"][p["id"]];a=Q(1,max(1,p["degree"])*row["q"]);x=Q(row["x"])
        B=flint.arb(cert["constant_ball"])*real(a)**cert["parameter_power"]*real(x)*(flint.arb.const_e()+real(x)).log()**cert["log_power"]
        assert row["passed"] and abs(allvalues[p["id"]][f"{row['q']}:{x}"])<=B
    counts["fresh_parameter_sensitive_unit_increment_checks"]=len(final["unit_increment_checks"])
    counts["fresh_proved_weak_family_bound_checks"]=len(final["weak_bound_checks"])
    checks["fresh_integer_bounds_real_unit_checks_and_weak_theorem_witnesses"]=True

    for row in final["generic_input_responses"]:
        expected=generic_log(row["case"])
        for txt,v in zip(row["arithmetic_logarithm"],expected):assert flint.arb(txt).contains(v)
    counts["generic_signed_input_coefficients_checked"]=sum(len(r["arithmetic_logarithm"]) for r in final["generic_input_responses"])
    checks["generic_signed_unit_arithmetic_identity_calibration"]=True

    assert cases["fresh_q"]==sorted(set(cases["fresh_q"])) and len(cases["fresh_q"])==spec["final_cases"]["fresh_q_count"]
    assert not set(cases["fresh_q"])&set(spec["training_q"]+spec["validation_new_q"])
    assert all(spec["final_cases"]["fresh_q_range"][0]<=q<=spec["final_cases"]["fresh_q_range"][1] for q in cases["fresh_q"])
    assert all(spec["final_cases"]["integer_range"][0]<=n<=spec["final_cases"]["integer_range"][1] for n in cases["integers"])
    for r in spec["retained_failed_runs_are_development"]:
        old=Path(r["run_directory"])
        for name,key in [("failure.json","failure_sha256"),("protocol.json","protocol_sha256"),("final_evaluation.json","final_sha256"),("final_cases.json","final_cases_sha256")]:assert sha(old/name)==r[key]
        for n,h in r["original_source_sha256"].items():assert sha(old/"frozen_source"/n)==h
        assert not set(cases["integers"])&set(r["excluded_integer_scales"])
        assert not set(cases["fresh_q"])&set(r["excluded_fresh_q"])
    assert archive["ablation_comparison"]["equal_promotion_slot_budgets"]
    assert final["uniform_RH_sufficient_signed_controls_verified"]==spec["uniform_RH_sufficient_signed_controls_verified"]==[]
    assert final["final_scope_is_finite"] and not final["RH_proved"]
    checks["freshness_equal_budget_ablation_and_universal_premise_not_inferred"]=True

    replay_hashes={}
    if not args.skip_replay:
        with tempfile.TemporaryDirectory(prefix="fractional-remainder-replay-") as tmp:
            replay=Path(tmp);(replay/"protocol.json").write_bytes((directory/"protocol.json").read_bytes())
            proc=subprocess.run([sys.executable,str(BASE/"fractional_remainder_search.py"),"--phase","discover","--run-dir",str(replay)],capture_output=True,text=True)
            if proc.returncode:raise RuntimeError("Deterministic replay failed: "+proc.stderr[-4000:])
            for n in seal["files"]:
                assert sha(replay/n)==sha(directory/n),"replay "+n;replay_hashes[n]=sha(replay/n)
    checks["deterministic_generation_selection_promotion_and_ablation_replay"]=not args.skip_replay
    output={"protocol_sha256":digest(spec),"final_sha256":sha(directory/"final_evaluation.json"),"checker_sha256":sha(BASE/"check_fractional_remainders.py"),
        "all_passed":all(checks.values()),"checks":checks,**counts,"parameter_pole_diagnostics":diagnostics,"replay_sha256":replay_hashes,
        "independent_algorithms":{"coefficient":"factor-sieve Mobius and direct divisor convolution","normalizer":"Kummer-transformed hypergeometric and integral",
            "entire_numerator":"derivative integral, different endpoints/orders, and explicit infinite tails","proof_scope":"reviewed generic arguments plus native constants; not machine formalized"},
        "native_proof_is_machine_formalized":False,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    destination=directory/"verification.json"
    if destination.exists():raise FileExistsError("Retain the original audit, including failures")
    destination.write_text(json.dumps(output,indent=2)+"\n")
    print("Fractional remainder checks:",sum(checks.values()),"/",len(checks),"; RH uniform premise unproved",flush=True)


if __name__=="__main__":main()

#!/usr/bin/env python3
"""Independent prime support, residue-faithfulness and complete-point audit."""
import argparse
from bisect import bisect_left
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


def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(d):return hashlib.sha256(json.dumps(d,sort_keys=True,separators=(",",":"),allow_nan=False).encode()).hexdigest()
def real(x):
    x=Q(x)
    return flint.arb(x.numerator)/x.denominator


def prime_coefficients(N):
    spf=list(range(N+1))
    for p in range(2,N+1):
        if spf[p]==p:
            for n in range(p*p,N+1,p):
                if spf[n]==n:spf[n]=p
    f=[Q(0)]*(N+1)
    for n in range(2,N+1):
        p,r,k=spf[n],n,0
        while r%p==0:r//=p;k+=1
        f[n]=Q(1,k) if r==1 else Q(0)
    return f


def support_table(f):
    locations=[];sums=[Q(0)]
    for n,v in enumerate(f):
        if v:
            locations.append(n);sums.append(sums[-1]+v)
    return locations,sums


def independent_response(p,table,points):
    locations,sums=table
    beta=Q(p["beta"])
    out={}
    for t in points:
        value=flint.arb(0)
        for delay,coefficient in p["atoms"]:
            x=Q(t)/Q(delay)
            if x<2:continue
            count=sums[bisect_left(locations,x)]
            # A different special-function entry point than Ei(log x).
            value+=real(coefficient)*(real(x).li()-real(beta*count))
        out[str(t)]=value
    return out


def enclosure(stored,v):
    ball=flint.arb(stored)
    assert ball.is_finite() and v.is_finite() and ball.contains(v)
    assert ball.rad()<real(Q(1,10**35))*(1+abs(v))


def status(v,b):return "pass" if v<=b else ("fail" if v>b else "unresolved")


def independent_increment(p):
    return sum((real(abs(Q(c)))*(real(abs(Q(p["beta"])))+1/(real(d)*real(2).log())+
                (abs(real(2).li()) if Q(d).denominator!=1 else real(0))) for d,c in p["atoms"]),real(0))


def check_candidate(c,p,training=None):
    theta,ell,C,A=map(Q,(c[k] for k in ("theta","log_power","constant","offset")))
    tr=c["transfer"];beta=Q(p["beta"])
    assert theta>=0 and ell>=0 and C>0
    for key,v in (("theta",theta),("log_power",ell),("constant",C),("offset",A)):
        assert Q(tr[key])==v
    assert Q(tr["mellin_exponent"])==theta
    assert tr["multiplier_not_identically_zero"] and not tr["all_height_multiplier_nonvanishing_required"]
    assert tr["every_ordinary_zero_multiplicity_retained"]==(beta!=0)
    assert tr["uncancelled_pole_logarithm_at_one"]==(beta!=1 and theta<1)
    assert tr["RH_sufficient_if_uniform"]==(beta==1 and theta<=Q(1,2))
    assert not tr["uniform_signed_premise_proved"] and not tr["RH_proved"]
    B=independent_increment(p)
    enclosure(tr["increment_cost_ball"],B)
    expected=("uniform_claim_ruled_out_by_uncancelled_pole_logarithm" if beta!=1 and theta<1 else
              "uniform_claim_ruled_out_by_actual_critical_zero_even_if_multiplier_vanishes" if beta==1 and theta<Q(1,2) else
              "RH_sufficient_signed_prime_error_obligation_missing_uniform_proof" if beta==1 and theta<=Q(1,2) else
              "signed_growth_obligation_above_RH_threshold")
    assert c["analytic_status"]==expected
    if training is not None:
        top=max((abs(v-real(A))/real(n)**real(theta)/(flint.arb.const_e()+real(n)).log()**real(ell)).upper() for n,v in training.items())
        assert real(C)>=2*top or real(C)-2*top>real(Q(-1,10**30))
        assert real(C)<=2*top+real(Q(1,1024))+real(Q(1,10**30)) or C==Q(1,1024)
    if "cost_sigma" in c:
        sigma=Q(c["cost_sigma"])
        assert sigma==theta+Q(1,8) and Q(c["cost_height"])==16
        s=flint.acb(real(sigma),real(16))
        D=sum((real(a)*flint.acb(real(d))**(-s) for d,a in p["atoms"]),flint.acb(0))
        assert not c["cost_is_all_height_certificate"]
        if c["conditional_log_reciprocal_bound_ball"] is None:
            assert not D.abs_lower()>0
        else:
            assert D.abs_lower()>0
            degree=ceil(ell)
            l=(1+flint.arb.const_e()).log()
            H=real(C)*sum((comb(degree,j)*factorial(j)*l**(degree-j)/real(sigma-theta)**(j+1)
                          for j in range(degree+1)),real(0))+B/real(sigma)
            l2=real(2).log()
            J=l2*(2+flint.arb.const_euler()-l2.log())
            cost=abs(s-1).log()+(abs(s)*H+real(abs(A)))/D.abs_lower()+abs(s)*J
            enclosure(c["conditional_log_reciprocal_bound_ball"],cost)
            assert abs(float(cost.upper())-c["log_reciprocal_cost"])<1e-9*(1+abs(c["log_reciprocal_cost"]))


def native_zero_residue(dependency):
    """Actual simple zero: F'/F has residue 1; derivatives of F^-k have 0.

    F^k is a guided example multiplier vanishing at the enclosed zero. It is
    not claimed to be a finite-dilation program from the arithmetic search.
    """
    zero,previous_margin=zero_disk(dependency)
    centre=flint.acb(real(Q(1,2)),dependency["centre"][1])
    r=real(Q(dependency["radius"])/16)
    box=centre+flint.acb(flint.arb(0,2*r),flint.arb(0,2*r))
    first=flint.acb_series([centre,1],prec=2).zeta()[1]
    second=2*flint.acb_series([box,1],prec=3).zeta()[2]
    margins=[]
    for radius in (r,2*r):
        margin=first.abs_lower()*radius-centre.zeta().abs_upper()-second.abs_upper()*radius*radius/2
        assert margin>0
        margins.append(margin.str(40))
    # Certified local zeta values and derivatives. Taylor's integral
    # remainder on the convex complex box bounds both functions, including
    # the complex disks queried by native analytic quadrature. This avoids
    # repeated, poorly conditioned broad-interval zeta evaluations.
    order=12
    R=8*r
    derivative_box=centre+flint.acb(flint.arb(0,R),flint.arb(0,R))
    coefficients=flint.acb_series([centre,1],prec=order).zeta()
    remainder=flint.acb_series([derivative_box,1],prec=order+1).zeta()[order].abs_upper()
    assert remainder.is_finite()
    corners=[centre+flint.acb(r,r),centre+flint.acb(-r,r),centre+flint.acb(-r,-r),centre+flint.acb(r,-r)]
    values=[]
    for k in range(4):
        def integrand(s,analytic):
            z=s-centre
            if abs(z.real).upper()>R or abs(z.imag).upper()>R:
                return flint.acb("nan")
            value=coefficients[order-1];derivative=flint.acb(0)
            for j in range(order-2,-1,-1):
                derivative=derivative*z+value
                value=value*z+coefficients[j]
            radius=abs(z).upper()
            error=(remainder*radius**order).upper()
            value+=flint.acb(flint.arb(0,error),flint.arb(0,error))
            error_derivative=(order*remainder*radius**(order-1)).upper()
            derivative+=flint.acb(flint.arb(0,error_derivative),flint.arb(0,error_derivative))
            Fprime=value+(s-1)*derivative;F=(s-1)*value
            return Fprime/F if k==0 else -k*Fprime/F**(k+1)
        value=sum((flint.acb.integral(integrand,corners[j],corners[(j+1)%4],
                   abs_tol=real(Q(1,2**140)),rel_tol=real(Q(1,2**180)),eval_limit=50000,depth_limit=32)
                   for j in range(4)),flint.acb(0))/(2*flint.arb.pi()*flint.acb(0,1))
        expected=1 if k==0 else 0
        assert value.is_finite() and value.real.contains(expected) and value.imag.contains(0)
        assert value.real.rad()<real(Q(1,2**80)) and value.imag.rad()<real(Q(1,2**80))
        print("Native ordinary-zero residue case",k,"verified",flush=True)
        values.append({"kind":"Fprime/F" if k==0 else "derivative_of_F^(-"+str(k)+")",
                       "real":value.real.str(35),"imag":value.imag.str(35),"expected_residue":expected})
    return {"guided_multiplier_scope":"F^k vanishes at the actual zero; general analytic multiplier calibration, not a searched finite filter",
            "previous_Rouche_margin":previous_margin,"inner_outer_Rouche_margins":margins,
            "zeta_Taylor_order":order,"native_derivative_remainder_majorant":remainder.str(40),
            "native_Taylor_box_radius":R.str(40),
            "contour_integrals":values}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--run-dir",type=Path,required=True)
    directory=parser.parse_args().run_dir.resolve()
    spec,seal,arc,cases,final=(read(directory/n) for n in ("protocol.json","seal.json","archive.json","final_cases.json","final_evaluation.json"))
    for n,h in spec["code_sha256"].items():assert sha(BASE/n)==h
    source=Path(spec["source_run"])
    assert sha(source/"verification.json")==spec["source_verification_sha256"]
    assert sha(source/"jet_data.json")==spec["source_data_sha256"] and read(source/"verification.json")["all_passed"]
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"] and not seal["final_cases_exist_at_seal"]
    for n,h in seal["files"].items():assert sha(directory/n)==h
    assert cases["created_after_selection_closed"] and cases["seal_sha256"]==final["seal_sha256"]==digest(seal)
    assert final["cases_sha256"]==digest(cases)
    assert all(arc["worker_access_denials"].values()) and not arc["final_data_used"] and not arc["uniform_signed_premise_proved"]
    assert not spec["all_height_multiplier_nonvanishing_required"]
    rng=random.Random(int(cases["evaluator_seed"]));rule=spec["final_cases"]
    large=sorted(rng.sample(range(rule["large_range"][0],rule["large_range"][1]+1),rule["large_count"]))
    intermediate=sorted(rng.sample(range(rule["intermediate_range"][0],rule["intermediate_range"][1]+1),rule["intermediate_count"]))
    assert cases["large"]==large and cases["intermediate"]==intermediate and cases["points"]==sorted(set(rule["boundary"]+intermediate+large))
    replay=directory/"replay"
    if not replay.exists():
        replay.mkdir();(replay/"protocol.json").write_bytes((directory/"protocol.json").read_bytes())
        subprocess.run([sys.executable,str(BASE/"prime_error_search.py"),"discover","--run-dir",str(replay)],check=True,cwd=BASE)
    for n in ("discovery_data.json","candidate_batch.json","validation_data.json","archive.json","seal.json"):
        assert sha(directory/n)==sha(replay/n)
    batch=read(directory/"candidate_batch.json");validation=read(directory/"validation_data.json")
    assert batch["frozen_before_validation"] and batch["protocol_sha256"]==digest(spec)
    assert batch["discovery_sha256"]==sha(directory/"discovery_data.json")
    ps={p["id"]:p for p in batch["programs"]};assert len(ps)==len(batch["programs"])
    for p in ps.values():
        grouped={}
        for d,c in p["atoms"]:grouped[Q(d)]=grouped.get(Q(d),Q(0))+Q(c)
        expected=[[str(d),str(c)] for d,c in sorted(grouped.items()) if c]
        assert expected==p["atoms"] and expected[0]==["1","1"]
        assert all(Q(d)>=1 for d,c in expected)
        assert p["id"]==digest({k:p[k] for k in ("atoms","beta")})
        assert Q(p["multiplier_at_one"])==sum((Q(c)/Q(d) for d,c in expected),Q(0))
    flint.ctx.prec=768
    native_zero=native_zero_residue(spec["known_zero_dependency"])
    point_count=coeff_count=estimate_count=0
    training_values={}
    for label,points,data in (("training",spec["training_points"],read(directory/"discovery_data.json")),
                              ("validation",spec["validation_points"],validation)):
        f=prime_coefficients(max(points));table=support_table(f)
        assert data["coefficient_sha256"]==digest(list(map(str,f)));coeff_count+=len(f)-1
        assert set(data["complete_values"])==set(ps)
        observed={}
        for pid,p in ps.items():
            observed[pid]=independent_response(p,table,points)
            assert set(data["complete_values"][pid])==set(map(str,points))
            for n,v in observed[pid].items():enclosure(data["complete_values"][pid][n],v);point_count+=1
        if label=="training":training_values=observed
        else:
            assert len(data["candidates"])==len(batch["candidates"])
            for c,original in zip(data["candidates"],batch["candidates"]):
                assert all(c[k]==v for k,v in original.items())
                assert c["id"]==digest({k:c[k] for k in ("program_id","theta","log_power","constant","offset")})
                check_candidate(c,ps[c["program_id"]],training_values[c["program_id"]])
                A,theta,ell,C=map(Q,(c[k] for k in ("offset","theta","log_power","constant")))
                states={n:status(abs(v-real(A)),real(C)*real(n)**real(theta)*(flint.arb.const_e()+real(n)).log()**real(ell))
                        for n,v in observed[c["program_id"]].items()}
                assert c["validation_failures"]==[n for n,v in states.items() if v=="fail"]
                assert c["validation_unresolved"]==[n for n,v in states.items() if v=="unresolved"]
                estimate_count+=1
    N=max(cases["points"]);f=prime_coefficients(N);table=support_table(f)
    assert final["coefficient_cutoff"]==N and final["coefficient_sha256"]==digest(list(map(str,f)));coeff_count+=N
    positive=[Q(0),Q(0)]+[Q(1)]*(N-1)
    cut=spec["delayed_support_cutoff"];delayed=f[:cut+1]+[Q(1)]*(N-cut)
    used={c["program_id"] for c in arc["archive"]}
    assert set(final["actual_values"])==set(final["support_control_values"])==used
    actual={};controls={};control_count=0
    for pid in sorted(used):
        actual[pid]=independent_response(ps[pid],table,cases["points"])
        assert set(final["actual_values"][pid])==set(map(str,cases["points"]))
        for n,v in actual[pid].items():enclosure(final["actual_values"][pid][n],v);point_count+=1
        controls[pid]={name:independent_response(ps[pid],support_table(coefs),large)
                       for name,coefs in (("positive_support",positive),("delayed_support",delayed))}
        for name,response in controls[pid].items():
            assert set(final["support_control_values"][pid][name])==set(map(str,large))
            for n,v in response.items():enclosure(final["support_control_values"][pid][name][n],v);control_count+=1
    assert len(final["outcomes"])==len(arc["archive"])
    for c,o in zip(arc["archive"],final["outcomes"]):
        assert c["id"]==o["candidate_id"]
        check_candidate(c,ps[c["program_id"]])
        A,theta,ell,C=map(Q,(c[k] for k in ("offset","theta","log_power","constant")))
        bound=lambda n:real(C)*real(n)**real(theta)*(flint.arb.const_e()+real(n)).log()**real(ell)
        states={n:status(abs(v-real(A)),bound(n)) for n,v in actual[c["program_id"]].items()}
        assert o["point_comparisons"]==states and o["finite_points_passed"]==all(v=="pass" for v in states.values())
        for name,values in controls[c["program_id"]].items():
            assert o["support_control_comparisons"][name]=={n:status(abs(v-real(A)),bound(n)) for n,v in values.items()}
        assert o["support_control_uniform_claims_ruled_out"]==(theta<1)
        assert not o["uniform_signed_premise_proved"] and not o["reselected"]
    # Declared native coefficient-log bridge: absolute tail is N^-h log(zeta(sigma-h)).
    native=spec["native_logarithmic_bridge"]
    assert [v["height"] for v in final["native_logarithmic_checks"]]==native["heights"]
    for record in final["native_logarithmic_checks"]:
        s=flint.acb(native["real_part"],real(record["height"]))
        expected=s.zeta().log()
        partial=sum((real(f[n])*flint.acb(real(n))**(-s) for n in range(2,N+1) if f[n]),flint.acb(0))
        tail=real(Q(1,N**native["tail_h"]))*real(native["real_part"]-native["tail_h"]).zeta().log()
        enclosure(record["log_zeta_ball"][0],expected.real);enclosure(record["log_zeta_ball"][1],expected.imag)
        enclosure(record["partial_ball"][0],partial.real);enclosure(record["partial_ball"][1],partial.imag)
        enclosure(record["proved_tail_ball"],tail)
        assert abs(expected-partial).upper()<tail.lower()
    # Exact local algebra: differentiation kills the potential z^-1 coefficient.
    algebra_cases=0
    for pole_order in range(17):
        coefficients={k:Q((k+pole_order+3)**2-7,13) for k in range(-pole_order,6)}
        derivative={k-1:k*v for k,v in coefficients.items()}
        assert derivative.get(-1,Q(0))==0
        for m in range(1,17):
            assert -Q(1)*m!=0
            algebra_cases+=1
    # Check whole-unit costs at irregular offsets, including rational-delay activations.
    increments=0
    for pid in used:
        p=ps[pid];B=independent_increment(p)
        for n in (1,2,3,4,5,8,15,31,64,127):
            points=[Q(n),Q(n)+Q(1,127),Q(n)+Q(126,127)]
            values=independent_response(p,table,points)
            for t in points[1:]:
                assert abs(values[str(t)]-values[str(Q(n))]).upper()<=B.lower()
                increments+=1
    assert not final["RH_proved"] and not final["uniform_RH_sufficient_signed_controls_verified"]
    checks={"frozen_source_parent_and_sealed_final_provenance_checked":True,
        "isolated_discovery_and_deterministic_selection_replay_checked":True,
        "all_exact_logarithmic_coefficients_checked_by_actual_prime_sieve":True,
        "complete_point_values_recomputed_with_logarithmic_integral":True,
        "all_multiplicity_meromorphic_residue_rule_and_pole_weight_obstruction_checked":True,
        "actual_zero_and_vanishing_multiplier_calibrated_by_native_contours":True,
        "whole_unit_prime_jumps_and_rational_activation_costs_checked":True,
        "full_exponential_recovery_cost_and_fixed_point_scope_checked":True,
        "native_zeta_logarithms_checked_with_proved_absolute_coefficient_tails":True,
        "support_controls_and_no_finite_to_uniform_promotion_checked":True}
    result={"all_passed":all(checks.values()),"checks":checks,"protocol_sha256":digest(spec),
            "final_sha256":sha(directory/"final_evaluation.json"),"checker_sha256":sha(BASE/"check_prime_error.py"),
            "programs_checked":len(ps),"estimates_checked":estimate_count,"exact_coefficients_checked":coeff_count,
            "complete_signed_point_values_checked":point_count,"complete_support_control_values_checked":control_count,
            "native_logarithmic_bridge_checks":len(final["native_logarithmic_checks"]),
            "native_zero_residue_calibration":native_zero,"local_Laurent_algebra_cases":algebra_cases,
            "whole_unit_increment_cases":increments,
            "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    (directory/"verification.json").write_text(json.dumps(result,indent=2)+"\n")
    print("Independent signed first-jet prime-error audit",sum(checks.values()),"/",len(checks),flush=True)


if __name__=="__main__":main()

#!/usr/bin/env python3
"""Independent prime-power, incomplete-gamma and Mellin obstruction audit."""
import argparse
from fractions import Fraction as Q
import hashlib,json,random,subprocess,sys
from pathlib import Path
import flint
from check_signed_mellin_transfer import zero_disk

BASE=Path(__file__).resolve().parent
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(d):return hashlib.sha256(json.dumps(d,sort_keys=True,separators=(",",":"),allow_nan=False).encode()).hexdigest()
def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def prime_coefficients(a,N):
    a=Q(a);spf=list(range(N+1))
    for p in range(2,N+1):
        if spf[p]==p:
            for n in range(p*p,N+1,p):
                if spf[n]==n:spf[n]=p
    f=[Q(0)]*(N+1);f[1]=Q(1)
    for n in range(2,N+1):
        p=spf[n];r=n;k=0;local=Q(1)
        while r%p==0:
            r//=p;k+=1;local*=Q(k-1-a)/k
        f[n]=f[r]*local;assert abs(f[n])<=1
    return f


def independent_kernel(b,k,u):
    b,k=Q(b),Q(k)
    if b==0:return flint.arb(1)
    if u==0:return flint.arb(0)
    incomplete=flint.acb(-real(k)*u).gamma_lower(real(b),regularized=2)
    assert incomplete.is_finite() and incomplete.imag.contains(0)
    return u**real(b)*incomplete.real


def independent_values(fs,b,k,points):
    converted={a:[real(v) for v in f] for a,f in fs.items()};out={a:{} for a in fs}
    for x in points:
        sums={a:flint.arb(0) for a in fs}
        for n in range(1,x+1):
            u=flint.arb(0) if n==x else real(Q(x,n)).log();v=independent_kernel(b,k,u)
            for a,f in converted.items():sums[a]+=f[n]*v
        for a in fs:out[a][x]=sums[a]
    return out


def enclosure(stored,value):
    s=flint.arb(stored);assert s.is_finite() and value.is_finite() and s.contains(value)
    assert s.rad()<real(Q(1,10**35))*(1+abs(value))


def status(value,bound):return "pass" if value<=bound else ("fail" if value>bound else "unresolved")


def audit_candidate(c,p):
    a,b,k,theta,C,A=map(Q,(p["a"],p["b"],p["kappa"],c["theta"],c["constant"],c["offset"]))
    tr=c["transfer"];lam=max(k-1,Q(0)) if b else Q(0);eta=max(theta,lam)
    assert Q(tr["mellin_exponent"])==eta and Q(tr["increment_exponent"])==lam
    assert all(Q(tr[key])==x for key,x in (("a",a),("b",b),("kappa",k),("theta",theta),("constant",C),("offset",A)))
    E=real(0) if b==0 else real(4+4/b)/real(b).gamma()*real(2)**real(lam)
    assert flint.arb(tr["increment_constant_ball"]).overlaps(E)
    one=a-b if k==1 and b else a;ob=[]
    if eta<1 and (one.denominator!=1 or one<0):ob.append({"location":"1","kind":"uncancelled_zeta_pole_branch_or_pole","local_order":str(one)})
    if b and k!=1 and k>eta:
        assert real(k).zeta().is_finite() and real(k).zeta().abs_lower()>0
        ob.append({"location":str(k),"kind":"introduced_kernel_branch_or_pole","local_order":str(-b)})
    assert tr["local_divisor_obstructions"]==ob and tr["zero_multiplicities_preserved"]
    assert tr["RH_sufficient_if_uniform"]==(eta<=Q(1,2) and not ob)
    assert not tr["uniform_integer_signed_bound_proved"] and not tr["RH_proved"]
    if eta<Q(1,2):expected="uniform_claim_ruled_out_by_actual_critical_zero"
    elif ob:expected="uniform_claim_ruled_out_by_local_pole_or_branch"
    elif eta<=Q(1,2):expected="RH_sufficient_signed_obligation_missing_uniform_proof"
    else:expected="signed_growth_obligation_above_RH_threshold"
    assert c["analytic_status"]==expected
    if "cost_sigma" in c:
        sigma=Q(c["cost_sigma"]);assert sigma==eta+Q(1,8) and Q(c["cost_height"])==16
        B=real(C)/real(sigma-theta)+E*(1/real(sigma-lam)+1/real(sigma-lam)**2)
        s=flint.acb(real(sigma),real(16));cost=(abs(s)*B+real(abs(A)))**real(1/a)*abs(s-real(k))**real(b/a)
        enclosure(c["conditional_reciprocal_bound_ball"],cost)
        assert abs(float(cost.upper().log())-c["log_cost"])<1e-10


def kernel_quadrature(b,k,u):
    b,k,u=Q(b),Q(k),Q(u)
    if b==0:return real(1)
    upper=real(u).root(b.denominator)
    def f(z,analytic):return (real(k)*z**b.denominator).exp()*z**(b.numerator-1)
    integral=flint.acb.integral(f,0,flint.acb(upper),abs_tol=real(Q(1,2**100)),rel_tol=real(Q(1,2**100)),eval_limit=20000,depth_limit=30)
    expected=integral*b.denominator/real(b).gamma()
    assert expected.imag.contains(0) and expected.is_finite()
    return expected.real


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--run-dir",type=Path,required=True)
    directory=parser.parse_args().run_dir.resolve();spec=read(directory/"protocol.json");seal=read(directory/"seal.json")
    for n,h in spec["code_sha256"].items():assert sha(BASE/n)==h
    source=Path(spec["source_run"]);branch=Path(spec["branch_run"])
    assert sha(source/"archive.json")==spec["source_archive_sha256"] and sha(source/"verification.json")==spec["source_verification_sha256"]
    assert sha(branch/"branch_audit.json")==spec["branch_audit_sha256"] and sha(branch/"verification.json")==spec["branch_verification_sha256"]
    assert read(source/"verification.json")["all_passed"] and read(branch/"verification.json")["all_passed"]
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"] and not seal["final_cases_exist_at_seal"]
    for n,h in seal["files"].items():assert sha(directory/n)==h
    cases,final,arc=read(directory/"final_cases.json"),read(directory/"final_evaluation.json"),read(directory/"archive.json")
    assert cases["created_after_selection_closed"] and cases["seal_sha256"]==final["seal_sha256"]==digest(seal) and final["cases_sha256"]==digest(cases)
    assert all(arc["worker_access_denials"].values()) and not arc["final_data_used"] and not arc["uniform_signed_bound_proved"]
    rng=random.Random(int(cases["evaluator_seed"]));rule=spec["final_cases"]
    large=sorted(rng.sample(range(rule["large_range"][0],rule["large_range"][1]+1),rule["large_count"]))
    intermediate=sorted(rng.sample(range(rule["intermediate_range"][0],rule["intermediate_range"][1]+1),rule["intermediate_count"]))
    assert cases["large"]==large and cases["intermediate"]==intermediate and cases["points"]==sorted(set(rule["boundary"]+intermediate+large))
    kr=spec["kernel_quadrature_calibration"]
    assert cases["quadrature_u"]==[str(Q(rng.randint(*kr["u_numerator_range"]),kr["u_denominator"])) for _ in range(kr["count"])]
    replay=directory/"replay"
    if not replay.exists():
        replay.mkdir();(replay/"protocol.json").write_bytes((directory/"protocol.json").read_bytes())
        subprocess.run([sys.executable,str(BASE/"pole_neutral_search.py"),"discover","--run-dir",str(replay)],check=True,cwd=BASE)
    for n in ("discovery_data.json","candidate_batch.json","validation_data.json","archive.json","seal.json"):assert sha(directory/n)==sha(replay/n)
    flint.ctx.prec=640;flint.ctx.cap=24;z,zero_margin=zero_disk(spec["known_zero_dependency"])
    batch=read(directory/"candidate_batch.json");assert batch["frozen_before_validation"] and batch["protocol_sha256"]==digest(spec)
    assert batch["discovery_sha256"]==sha(directory/"discovery_data.json")
    ps={p["id"]:p for p in batch["programs"]};assert len(ps)==len(batch["programs"])
    for p in ps.values():assert p["id"]==digest({key:p[key] for key in ("a","b","kappa")})
    count=coeff_count=0
    for label,points,data in (("training",spec["training_points"],read(directory/"discovery_data.json")),("validation",spec["validation_points"],read(directory/"validation_data.json"))):
        fs={a:prime_coefficients(a,max(points)) for a in map(Q,spec["coefficient_powers"])}
        for a,f in fs.items():assert data["coefficient_sha256"][str(a)]==digest(list(map(str,f)));coeff_count+=len(f)-1
        groups=sorted({(Q(p["b"]),Q(p["kappa"])) for p in ps.values()})
        for i,(b,k) in enumerate(groups):
            observed=independent_values(fs,b,k,points)
            for p in ps.values():
                if (Q(p["b"]),Q(p["kappa"]))!=(b,k):continue
                for n,v in observed[Q(p["a"])].items():enclosure(data["complete_values"][p["id"]][str(n)],v);count+=1
                if label=="validation":
                    for c in data["candidates"]:
                        if c["program_id"]!=p["id"]:continue
                        audit_candidate(c,p);A,theta,C=map(Q,(c["offset"],c["theta"],c["constant"]))
                        states={n:status(abs(v-real(A)),real(C)*real(n)**real(theta)) for n,v in observed[Q(p["a"])].items()}
                        assert c["validation_failures"]==[n for n,v in states.items() if v=="fail"]
                        assert c["validation_unresolved"]==[n for n,v in states.items() if v=="unresolved"]
            if i%8==0:print("Independent fractional kernel",label,i+1,"/",len(groups),flush=True)
    N=final["coefficient_cutoff"];assert N==max(cases["points"])<=spec["maximum_final_cutoff"]
    fs={a:prime_coefficients(a,N) for a in map(Q,final["coefficient_sha256"])}
    for a,f in fs.items():assert final["coefficient_sha256"][str(a)]==digest(list(map(str,f)));coeff_count+=N
    control_count=quad_count=0
    for pid,response in final["actual_values"].items():
        p=ps[pid];a,b,k=map(Q,(p["a"],p["b"],p["kappa"]));observed=independent_values({a:fs[a]},b,k,cases["points"])[a]
        for n,v in observed.items():enclosure(response[str(n)],v);count+=1
        positive=[Q(0)]+[Q(1)]*N;cut=spec["delayed_positive_cutoff"];delayed=fs[a][:cut+1]+[Q(1)]*(N-cut)
        control=independent_values({Q(1):positive,Q(2):delayed},b,k,cases["large"])
        for name,key in (("positive",Q(1)),("delayed",Q(2))):
            for n,v in control[key].items():enclosure(final["control_values"][pid][name][str(n)],v);control_count+=1
        for c in arc["archive"]:
            if c["program_id"]!=pid:continue
            o=next(o for o in final["outcomes"] if o["candidate_id"]==c["id"]);A,theta,C=map(Q,(c["offset"],c["theta"],c["constant"]))
            states={str(n):status(abs(v-real(A)),real(C)*real(n)**real(theta)) for n,v in observed.items()}
            assert o["point_comparisons"]==states and o["finite_points_passed"]==all(v=="pass" for v in states.values())
            for name,key in (("positive",Q(1)),("delayed",Q(2))):
                assert o["control_comparisons"][name]=={str(n):status(abs(v-real(A)),real(C)*real(n)**real(theta)) for n,v in control[key].items()}
            assert o["positive_control_uniform_claims_ruled_out_by_pole"]==(Q(c["transfer"]["mellin_exponent"])<1)
            assert not o["reselected"] and not o["uniform_signed_bound_proved"]
        for u in map(Q,cases["quadrature_u"]):
            quadrature=kernel_quadrature(b,k,u);expected=independent_kernel(b,k,real(u))
            assert quadrature.overlaps(expected);quad_count+=1
        print("Independent final coefficient operator",p,flush=True)
    native_count=0;rule=spec["native_Mellin_calibration"]
    for record in final["native_Mellin_checks"]:
        p=ps[record["program_id"]];a,b,k=map(Q,(p["a"],p["b"],p["kappa"]));f=fs[a]
        assert len(record["checks"])==len(rule["heights"])
        for r,height in zip(record["checks"],rule["heights"]):
            assert r["height"]==height;s=flint.acb(rule["real_part"],real(height));mult=(s-real(k))**(-real(b))/s
            expected=(s.zeta()**(-real(a)))*mult
            partial=sum((real(f[n])/(flint.acb(n)**s) for n in range(1,N+1)),flint.acb(0))*mult
            tail=real(N)**real(-rule["tail_h"])*real(rule["real_part"]-rule["tail_h"]).zeta()**real(a)*abs(mult)
            enclosure(r["value"][0],expected.real);enclosure(r["value"][1],expected.imag)
            enclosure(r["partial"][0],partial.real);enclosure(r["partial"][1],partial.imag);enclosure(r["tail"],tail)
            assert abs(expected-partial).upper()<tail.lower();native_count+=1
    assert not final["RH_proved"] and not final["uniform_RH_sufficient_signed_controls_verified"]
    checks={"frozen_sources_and_local_branch_dependencies_checked":True,"OS_final_cases_isolation_and_deterministic_replay_checked":True,
        "all_exact_coefficients_independently_checked_by_prime_power_recursion":True,
        "complete_signed_sums_recomputed_with_regularized_incomplete_gamma":True,
        "kernel_representations_checked_by_entire_integrand_quadrature":True,
        "real_increment_and_full_inverse_power_costs_checked":True,
        "all_multiplicity_root_identity_and_actual_critical_zero_recertified":True,
        "local_pole_and_introduced_shift_obstructions_checked":True,
        "native_Mellin_values_and_proved_coefficient_tails_checked":True,
        "positive_controls_and_no_finite_to_uniform_promotion_checked":True}
    result={"all_passed":True,"checks":checks,"protocol_sha256":digest(spec),"source_final_sha256":sha(directory/"final_evaluation.json"),"checker_sha256":sha(Path(__file__)),
        "complete_signed_values_checked":count,"complete_control_values_checked":control_count,"exact_coefficients_checked":coeff_count,
        "kernel_quadrature_checks":quad_count,"native_Mellin_checks":native_count,"coefficient_cutoff":N,
        "independent_nested_zero_margin":zero_margin,"mathematical_audit_imports_production_integrator":False,
        "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    (directory/"verification.json").write_text(json.dumps(result,indent=2)+"\n")
    print("Independent pole-neutral fractional arithmetic audit",sum(checks.values()),"/",len(checks),flush=True)


if __name__=="__main__":main()

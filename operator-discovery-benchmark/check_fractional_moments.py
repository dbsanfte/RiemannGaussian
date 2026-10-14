#!/usr/bin/env python3
"""Independent rational-power, complete-moment, recovery and provenance audit."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from math import lcm
from pathlib import Path
import random
import subprocess
import sys
import flint

from check_signed_control import independent_inverse
from check_stable_scale import audit_operator
from check_signed_mellin_transfer import zero_disk

BASE=Path(__file__).resolve().parent
def read(path): return json.loads(Path(path).read_text())
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def digest(data): return hashlib.sha256(json.dumps(data,sort_keys=True,separators=(",",":"),allow_nan=False).encode()).hexdigest()
def real(x):
    x=Q(x); return flint.arb(x.numerator)/x.denominator


def independent_moments(mu,M,rows,scales,orders):
    """Split sign crossings explicitly; use log/exp, not the root producer."""
    rows=[(d,Q(a)) for d,a in rows]; D=lcm(1,*[(a/d).denominator for d,a in rows])
    coefficients=[(d,int(D*a/d)) for d,a in rows]
    def endpoint(n):
        answer=D*M[n]
        for d,a in coefficients:
            quotient,remainder=divmod(n,d)
            answer-=a*(d*M[quotient]+remainder*mu[quotient+1])
        return answer
    qs=list(map(Q,orders)); caches={q:{} for q in qs}; constant_caches={q:{} for q in qs}
    def absolute_power(n,a,cache):
        if n not in cache:
            if n==0: cache[n]=flint.arb(0)
            elif a.denominator==1: cache[n]=flint.arb(n)**a.numerator
            else: cache[n]=(flint.arb(n).log()*real(a)).exp()
        return cache[n]
    normalization={q:(real(D)**q.numerator if q.denominator==1 else (real(D).log()*real(q)).exp()) for q in qs}
    endpoints={v for X in scales for v in (X,2*X)}; totals={q:flint.arb(0) for q in qs}; snapshots={}
    u=endpoint(0)
    for n in range(max(endpoints)+1):
        if n:
            v=endpoint(n)
            for q in qs:
                if u==v:
                    piece=absolute_power(abs(u),q,constant_caches[q])
                elif u*v<=0:
                    piece=(absolute_power(abs(u),q+1,caches[q])+absolute_power(abs(v),q+1,caches[q]))/real((abs(u)+abs(v))*(q+1))
                else:
                    a,b=sorted((abs(u),abs(v)))
                    piece=(absolute_power(b,q+1,caches[q])-absolute_power(a,q+1,caches[q]))/real((b-a)*(q+1))
                totals[q]+=piece
            u=v
        if n in endpoints: snapshots[n]=totals.copy()
    return {X:{str(q):(snapshots[2*X][q]-snapshots[X][q])/normalization[q] for q in qs} for X in scales}


def audit_moments(record,expected):
    for X,row in expected.items():
        for q,value in row.items():
            source=flint.arb(record[str(X)][q])
            assert source.is_finite() and value.is_finite()
            assert source.contains(value),(X,q,"fractional moment enclosure did not contain the independent value")
            assert source.rad()<real(Q(1,10**35))*(1+abs(value))
    assert set(record)=={str(X) for X in expected}
    return sum(len(r) for r in expected.values())


def convolution(f,g):
    N=len(f)-1; out=[Q(0)]*(N+1)
    # Divisor rows differ from the producer's product scatter.
    for n in range(1,N+1):
        out[n]=sum((f[d]*g[n//d] for d in range(1,n+1) if n%d==0),Q(0))
    return out


def independent_dirichlet_power(values,a):
    """Formal log/exp, not the producer's generalized binomial expansion."""
    f=[Q(0)]+list(map(Q,values)); N=len(values); assert f[1]==1
    delta=[Q(0)]*(N+1); delta[1]=Q(1); h=list(f); h[1]-=1
    logarithm=[Q(0)]*(N+1); term=list(delta)
    for k in range(1,N.bit_length()):
        term=convolution(term,h)
        for n in range(1,N+1): logarithm[n]+=Q((-1)**(k+1),k)*term[n]*a
    out=list(delta); term=list(delta); factorial=1
    for k in range(1,N.bit_length()):
        term=convolution(term,logarithm); factorial*=k
        for n in range(1,N+1): out[n]+=term[n]/factorial
    return out


def state(value,bound):
    return "pass" if value<=bound else ("fail" if value>bound else "unresolved")


def audit_transfer(c,program,zero):
    q,beta,C=map(Q,(c["effective_order"],c["beta"],c["constant"])); L=Q(program["operator_certificate"]["lipschitz_constant"])
    root=Q(c["root_exponent"]); outer=c["outer_moment_order"]
    assert root>0 and outer>0 and root*outer==q and Q(c["inverse_exponent"])*root==1
    assert root==Q(1,q.denominator) and outer==q.numerator
    cert=c["root_certificate"]; assert cert["mode"]=="signed" and Q(cert["exponent"])==root
    assert cert["signed_information_preserved_invertibly"] and Q(cert["signed_inverse_exponent"])==1/root
    assert not cert["ordinary_zero_exclusion_proved"] and not cert["uniform_signed_arithmetic_control_proved"]
    transfer=c["transfer"]
    eta=(beta-1)/q if q>=1 else 2*beta/(q+1)-1
    assert Q(transfer["mellin_exponent"])==eta
    assert Q(transfer["order"])==q and Q(transfer["beta"])==beta and Q(transfer["constant"])==C and Q(transfer["lipschitz"])==L
    assert transfer["RH_sufficient_if_uniform_and_all_height_multiplier_nonzero"]==(eta<=Q(1,2))
    assert transfer["contradicted_if_critical_zero_multiplier_nonzero"]==(eta<Q(1,2))
    assert not transfer["uniform_signed_moment_premise_proved"] and not transfer["RH_proved"]
    if q>=1: coeff=real(C)**real(1/q)
    else:
        K=(real(2)**real(q+2)*real(L*C))**real(1/(q+1)); coeff=real(C)*K**real(1-q)
        assert "Lipschitz" in transfer["method"]
    assert flint.arb(transfer["mellin_bound_coefficient_ball"]).overlaps(coeff)
    polynomial=program["polynomial"]; w=(-zero*real(program["base"]).log()).exp(); F=flint.acb(0)
    for a in reversed(polynomial): F=F*w+real(a)
    nonzero=bool(F.abs_lower()>0); all_height=program["operator_certificate"]["all_height_critical_multiplier_certified"]
    assert c["actual_zero_multiplier_nonzero"]==nonzero and c["all_height_multiplier_nonzero"]==all_height
    if nonzero and eta<Q(1,2): expected="uniform_estimate_ruled_out_by_actual_zeta_zero"
    elif not all_height: expected="numerical_lead_missing_all_height_multiplier"
    elif eta<=Q(1,2): expected="RH_sufficient_obligation_missing_uniform_signed_proof"
    else: expected="numerical_signed_obligation_above_RH_threshold"
    assert c["analytic_status"]==expected
    if "cost_line" in c:
        sigma=Q(c["cost_line"]); assert sigma==eta+Q(1,8)
        delta=Q(c["global_multiplier_lower_bound"]); assert delta==Q(program["operator_certificate"]["selected_schur_certificate"]["uniform_multiplier_lower_bound"])
        compact=flint.arb(0)
        for d,a in program["operator_certificate"]["atoms"]:
            integral=real(d).log() if sigma==1 else (real(d)**real(1-sigma)-1)/real(1-sigma)
            compact+=real(abs(Q(a))/d)*integral
        bound=(coeff/(1-real(2)**real(eta-sigma))+compact)/real(delta)+1/real(sigma)
        assert flint.arb(c["conditional_reciprocal_bound_ball"]).contains(bound)
        assert abs(float(bound.upper().log())-c["log_cost"])<1e-10


def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--run-dir",type=Path,required=True)
    directory=parser.parse_args().run_dir.resolve(); spec=read(directory/"protocol.json"); seal=read(directory/"seal.json")
    for name,expected in spec["code_sha256"].items(): assert sha(BASE/name)==expected
    source=Path(spec["source_run"])
    assert sha(source/"archive.json")==spec["source_archive_sha256"] and sha(source/"verification.json")==spec["source_verification_sha256"]
    assert read(source/"protocol.json")==spec["source_protocol"]
    assert spec["input_operators"]==[r["program"] for r in read(source/"archive.json")["archive"]]
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"] and not seal["final_cases_exist_at_seal"]
    for name,expected in seal["files"].items(): assert sha(directory/name)==expected
    cases,final,archive=read(directory/"final_cases.json"),read(directory/"final_evaluation.json"),read(directory/"archive.json")
    assert final["seal_sha256"]==cases["seal_sha256"]==digest(seal) and final["cases_sha256"]==digest(cases)
    assert cases["created_after_selection_closed"] and not archive["final_data_used"]
    assert all(archive["worker_access_denials"].values()) and not archive["uniform_signed_arithmetic_proof"]
    rng=random.Random(int(cases["evaluator_seed"])); rule=spec["final_cases"]
    large=sorted(rng.sample(range(rule["large_range"][0],rule["large_range"][1]+1),rule["large_count"]))
    middle=sorted(rng.sample(range(rule["intermediate_range"][0],rule["intermediate_range"][1]+1),rule["intermediate_count"]))
    assert cases["large"]==large and cases["intermediate"]==middle and cases["scales"]==sorted(set(rule["boundary"]+middle+large))
    gr=spec["generic_final_sequences"]
    generic=[["1"]+[str(Q(rng.randint(*gr["integer_range"]),gr["denominator"])) for _ in range(N-1)] for N in gr["cutoffs"]]
    assert generic==cases["generic_normalized_sequences"]
    zr=spec["zeta_root_calibration"]
    assert cases["zeta_heights"]==[str(Q(rng.randint(*zr["height_integer_range"]),zr["height_denominator"])) for _ in range(zr["cases"])]
    replay=directory/"replay"
    if not replay.exists():
        replay.mkdir(); (replay/"protocol.json").write_bytes((directory/"protocol.json").read_bytes())
        subprocess.run([sys.executable,str(BASE/"fractional_moment_search.py"),"discover","--run-dir",str(replay)],check=True,cwd=BASE)
    for name in ("discovery_data.json","candidate_batch.json","validation_data.json","archive.json","seal.json"):
        assert sha(directory/name)==sha(replay/name),(name,"replay mismatch")
    flint.ctx.prec=768; flint.ctx.cap=24
    programs={p["id"]:p for p in spec["input_operators"]}
    for p in programs.values(): audit_operator(p,spec["source_protocol"])
    zero,margin=zero_disk(spec["known_zero_dependency"])
    training,validation=read(directory/"discovery_data.json"),read(directory/"validation_data.json")
    batch=read(directory/"candidate_batch.json")
    assert batch["frozen_before_validation"] and batch["protocol_sha256"]==digest(spec)
    assert batch["discovery_sha256"]==sha(directory/"discovery_data.json") and archive["batch_sha256"]==sha(directory/"candidate_batch.json")
    count=0
    for label,scales,data in (("training",spec["training_scales"],training),("validation",spec["validation_scales"],validation)):
        mu,M=independent_inverse(2*max(scales))
        if label=="training": assert training["inverse_coefficient_sha256"]==digest(mu)
        for i,p in enumerate(programs.values()):
            values=independent_moments(mu,M,p["operator_certificate"]["atoms"],scales,spec["orders"])
            count+=audit_moments(data["moments"][p["id"]],values)
            if label=="validation":
                for c in validation["candidates"]:
                    if c["program_id"]!=p["id"]: continue
                    audit_transfer(c,p,zero)
                    q,beta,C=map(Q,(c["effective_order"],c["beta"],c["constant"]))
                    states={X:state(row[str(q)],real(C)*real(X)**real(beta)) for X,row in values.items()}
                    assert c["validation_failures"]==[X for X,s in states.items() if s=="fail"]
                    assert c["validation_unresolved"]==[X for X,s in states.items() if s=="unresolved"]
            print("Independent fractional",label,i+1,flush=True)
    mu,M=independent_inverse(final["coefficient_cutoff"])
    assert final["inverse_coefficient_sha256"]==digest(mu) and final["coefficient_cutoff"]==2*max(cases["scales"])<=spec["maximum_final_cutoff"]
    cutoff=spec["delayed_positive_cutoff"]; delayed=mu[:cutoff+1]+[1]*(len(mu)-cutoff-1)
    delayed_M=[0]*len(mu)
    for n in range(1,len(mu)): delayed_M[n]=delayed_M[n-1]+delayed[n]
    controls=0
    for pid,record in final["actual_moments"].items():
        p=programs[pid]; qs=sorted({Q(c["effective_order"]) for c in archive["archive"] if c["program_id"]==pid})
        values=independent_moments(mu,M,p["operator_certificate"]["atoms"],cases["scales"],qs)
        delay=independent_moments(delayed,delayed_M,p["operator_certificate"]["atoms"],cases["large"],qs)
        count+=audit_moments(record,values); controls+=audit_moments(final["delayed_positive_moments"][pid],delay)
        slope=sum((Q(a)/p["base"]**k for k,a in enumerate(p["polynomial"])),Q(0))
        for c in archive["archive"]:
            if c["program_id"]!=pid: continue
            out=next(o for o in final["outcomes"] if o["candidate_id"]==c["id"])
            q,beta,C=map(Q,(c["effective_order"],c["beta"],c["constant"]))
            states={str(X):state(row[str(q)],real(C)*real(X)**real(beta)) for X,row in values.items()}
            assert out["window_comparisons"]==states and out["finite_windows_passed"]==all(s=="pass" for s in states.values())
            positive={X:(real(abs(slope))**real(q))*real(X)**real(q+1)*(real(2)**real(q+1)-1)/real(q+1) for X in cases["large"]}
            for X,v in positive.items(): assert flint.arb(out["positive_control_moment_balls"][str(X)]).overlaps(v)
            for name,raw in (("positive",positive),("delayed",{X:r[str(q)] for X,r in delay.items()})):
                assert out["control_comparisons"][name]=={str(X):state(v,real(C)*real(X)**real(beta)) for X,v in raw.items()}
            assert out["both_positive_control_uniform_claims_false"]==bool(slope and beta<q+1)
            assert not out["uniform_signed_moment_premise_proved"] and not out["reselected"]
        print("Independent fractional final",p["family"],flush=True)
    exact_coefficients=native_count=0
    expected_exponents={Q(sign,d) for d in range(2,spec["max_denominator"]+1) for sign in (-1,1)}
    assert {Q(r["exponent"]) for r in final["Dirichlet_root_calibrations"]}==expected_exponents
    assert len(final["Dirichlet_root_calibrations"])==len(expected_exponents)
    for record in final["Dirichlet_root_calibrations"]:
        a=Q(record["exponent"])
        for f,raw in zip(generic,record["generic_exact_coefficients"]):
            independent=independent_dirichlet_power(f,a)
            assert list(map(Q,raw))==independent[1:]; exact_coefficients+=len(raw)
            restored=independent_dirichlet_power(raw,1/a)
            assert restored[1:]==list(map(Q,f))
        N=zr["cutoff"]; coeff=independent_dirichlet_power([Q(1)]*N,a)
        assert list(map(Q,record["zeta_exact_coefficients"]))==coeff[1:]; exact_coefficients+=N
        # The entire Re(s)>=4 image lies in |zeta-1|<zeta(4)-1<1,
        # so the principal Log matches the Euler-product branch here.
        assert real(4).zeta()-1<1
        assert len(record["native_zeta_checks"])==zr["cases"]
        for outcome,height in zip(record["native_zeta_checks"],cases["zeta_heights"]):
            assert outcome["height"]==height
            s=flint.acb(zr["real_part"],real(height)); expected=(s.zeta().log()*real(a)).exp()
            partial=sum((real(coeff[n])/(flint.acb(n)**s) for n in range(1,N+1)),flint.acb(0))
            tail=real(N)**real(-zr["tail_u"])*real(zr["real_part"]-zr["tail_u"]).zeta()**real(abs(a))
            assert flint.arb(outcome["value"][0]).contains(expected.real) and flint.arb(outcome["value"][1]).contains(expected.imag)
            assert flint.arb(outcome["partial"][0]).contains(partial.real) and flint.arb(outcome["partial"][1]).contains(partial.imag)
            assert flint.arb(outcome["tail_bound_ball"]).contains(tail) and abs(expected-partial).upper()<tail.lower()
            native_count+=1
    assert final["selection_closed_before_final_data"] and not final["RH_proved"] and not final["uniform_sublinear_signed_controls_verified"]
    checks={"frozen_sources_and_source_operator_dependencies_checked":True,"fresh_cases_and_worker_isolation_checked":True,
        "discovery_and_selection_deterministically_replayed":True,"independent_prime_inverse_and_all_height_multiplier_audits":True,
        "complete_fractional_moments_recomputed_by_sign_splitting_and_log_exp":True,
        "root_inverse_and_effective_order_recovery_audited":True,"fractional_Holder_and_subunit_Lipschitz_transfers_audited":True,
        "actual_ordinary_zero_obstructions_and_reciprocal_costs_checked":True,"complete_positive_controls_and_no_uniform_promotion_checked":True,
        "independent_exact_Dirichlet_log_exp_roots_and_inverse_laws_checked":True,"native_zeta_root_values_with_proved_all_index_tails_checked":True}
    result={"all_passed":True,"checks":checks,"protocol_sha256":digest(spec),"source_final_sha256":sha(directory/"final_evaluation.json"),
        "checker_sha256":sha(Path(__file__)),"certified_actual_moment_values_checked":count,"certified_delayed_positive_values_checked":controls,
        "exact_Dirichlet_coefficients_checked":exact_coefficients,"native_zeta_root_checks":native_count,
        "complete_coefficient_cutoff":len(mu)-1,"independent_nested_zero_margin":margin,
        "mathematical_audit_imports_production_integrator":False,"replay_invokes_production_generator":True,
        "uniform_sublinear_signed_controls_verified":[],"RH_proved":False}
    (directory/"verification.json").write_text(json.dumps(result,indent=2)+"\n")
    print("Independent fractional-power audit",sum(checks.values()),"/",len(checks),flush=True)


if __name__=="__main__": main()

#!/usr/bin/env python3
"""Independent integer, moment, zero-bridge and provenance verification."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import flint

BASE = Path(__file__).resolve().parent


def read(path): return json.loads(Path(path).read_text())
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def digest(value): return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(",", ":"),allow_nan=False).encode()).hexdigest()
def real(value): value=Q(value); return flint.arb(value.numerator)/value.denominator


def independent_inverse(N):
    mu=[1]*(N+1); mu[0]=0; composite=bytearray(N+1)
    for p in range(2,N+1):
        if composite[p]: continue
        for n in range(p,N+1,p):
            mu[n]=-mu[n]
            if n>p: composite[n]=1
        square=p*p
        if square<=N:
            for n in range(square,N+1,square): mu[n]=0
    M=[0]*(N+1)
    for n in range(1,N+1): M[n]=M[n-1]+mu[n]
    return mu,M


def independent_rows(encoded): return [(int(d),Q(a)) for d,a in encoded]


def value(mu,M,rows,t):
    def interp(t):
        n=t.numerator//t.denominator
        return Q(M[n]) if t.denominator==1 else Q(M[n])+(t-n)*mu[n+1]
    return interp(Q(t))-sum((a*interp(Q(t)/d) for d,a in rows),Q(0))


def unit_integral(x,y,q):
    total=x+y; product=x*y; h0,h1=Q(1),total
    for j in range(2,q+1): h0,h1=h1,total*h1-product*h0
    return h1/(q+1)


def complete(mu,M,rows,scales,orders):
    from math import lcm
    D=lcm(*(a.denominator*d for d,a in rows)) if rows else 1
    prepared=[(d,int(D*a)) for d,a in rows]
    def integer(n):
        result=D*M[n]
        for d,a in prepared:
            k,r=divmod(n,d)
            result-=a*M[k]+(a//d)*mu[k+1]*r
        return result
    # D*a is divisible by d by construction. This uses a different cleared
    # denominator and endpoint recurrence from the production divided difference.
    assert all(a%d==0 for d,a in prepared)
    endpoints={n for X in scales for n in (X,2*X)}
    sums={q:0 for q in orders}; snapshots={}; left=integer(0)
    for n in range(1,max(endpoints)+1):
        right=integer(n); s,p=left+right,left*right; h0,h1=1,s
        for j in range(2,max(orders)+1):
            h0,h1=h1,s*h1-p*h0
            if j in sums: sums[j]+=h1
        left=right
        if n in endpoints: snapshots[n]=sums.copy()
    return {X:{q:Q(snapshots[2*X][q]-snapshots[X][q],(q+1)*D**q) for q in orders} for X in scales}


def check_zero(dependency,archive):
    path=BASE/"shift-ratio-results/shift_ratio_analytic_verification.json"
    assert sha(path)==dependency["verification_sha256"]
    old=read(path); assert old["all_passed"]
    assert sha(BASE/"shift-ratio-results/shift_ratio_analytic.json")==dependency["source_sha256"]==old["source_artifact_sha256"]
    flint.ctx.cap=24
    c=flint.acb(real(Q(dependency["centre"][0])),dependency["centre"][1]); r=real(Q(dependency["radius"])/2)
    rectangle=c+flint.acb(flint.arb(0,r),flint.arb(0,r))
    derivative=flint.acb_series([c,1],prec=2).zeta()[1]
    second=2*flint.acb_series([rectangle,1],prec=3).zeta()[2]
    margin=derivative.abs_lower()*r-c.zeta().abs_upper()-second.abs_upper()*r*r/2
    assert margin>0
    lower=[]
    for row in archive:
        F=1-sum((real(Q(a))*(-rectangle*flint.arb(d).log()).exp() for d,a in row["program"]["atoms"]),flint.acb(0))
        assert F.abs_lower()>0
        lower.append(F.abs_lower().str(35))
    return {"fresh_nested_Rouche_margin":margin.str(35),"multiplier_lower_bounds_on_zero_disk":lower,
            "ordinary_zero_obstruction_retained":True,"global_RH_estimate_proved":False}


def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--run-dir",type=Path,required=True)
    args=parser.parse_args(); directory=args.run_dir.resolve(); flint.ctx.prec=384
    spec,seal=read(directory/"protocol.json"),read(directory/"seal.json")
    for name,expected in spec["code_sha256"].items(): assert sha(BASE/name)==expected
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"] and not seal["final_cases_exist_at_seal"]
    for name,expected in seal["files"].items(): assert sha(directory/name)==expected
    archive=read(directory/"archive.json"); final=read(directory/"final_evaluation.json"); cases=read(directory/"final_cases.json")
    assert final["seal_sha256"]==cases["seal_sha256"]==digest(seal)
    assert final["final_cases_sha256"]==digest(cases) and cases["created_after_selection_closed"]
    assert not archive["final_data_used"] and not archive["historical_priority_used"]
    assert all(archive["worker_access_denials"].values())
    mu,M=independent_inverse(final["coefficient_cutoff"])
    assert digest(mu)==final["inverse_coefficient_sha256"]
    batch=read(directory/"candidate_batch.json"); discovery=read(directory/"discovery_data.json")
    assert digest(mu[:discovery["coefficient_cutoff"]+1])==discovery["inverse_coefficient_sha256"]
    assert batch["frozen_before_validation"] and archive["batch_sha256"]==digest(batch)
    for program in batch["programs"]:
        rows=independent_rows(program["atoms"])
        cost=sum((real(abs(a))/real(d).sqrt() for d,a in rows),flint.arb(0))
        assert cost<real(Q(spec["critical_inverse_cost_cap"]))
        cert=program["operator_certificate"]
        assert Q(cert["lipschitz_constant"])==1+sum((abs(a)/d for d,a in rows),Q(0))
        assert cert["nonvanishing_multiplier_Re_s_ge_half_certified"] and not cert["global_signed_cancellation_estimate_proved"]
    validation=read(directory/"validation_data.json"); exact_count=0; sampled_count=0
    assert len(final["records"])==len(archive["archive"])
    for index,(row,result) in enumerate(zip(archive["archive"],final["records"])):
        program=row["program"]; rows=independent_rows(program["atoms"])
        assert result["program_id"]==program["id"]==digest(program["atoms"])
        for label,data,recordkey in (("training",discovery,"sampled_training_moments"),("validation",validation,"sampled_validation_moments")):
            for X,observed in row[recordkey].items():
                X=int(X); cells=data["cells"][str(X)]
                for q,number in observed.items():
                    q=int(q); own=Q(X,len(cells))*sum((unit_integral(value(mu,M,rows,n),value(mu,M,rows,n+1),q) for n in cells),Q(0))
                    assert own==Q(number); sampled_count+=1
        exact=complete(mu,M,rows,cases["scales"],spec["orders"])
        for X,observed in result["exact_window_moments"].items():
            for q,number in observed.items(): assert exact[int(X)][int(q)]==Q(number); exact_count+=1
        assert result["every_unit_interval_included"]
        for estimate,outcome in zip(row["estimates"],result["estimate_outcomes"]):
            q,beta,C=estimate["order"],Q(estimate["beta"]),Q(estimate["constant"])
            theta=beta/(q+1); transfer=estimate["moment_to_signed_pointwise_transfer"]
            assert Q(transfer["pointwise_exponent"])==theta
            assert estimate["known_zero_rules_out_uniform_claim"]==(theta<Q(1,2))
            assert not transfer["uniform_moment_premise_proved"] and not outcome["uniform_moment_bound_proved"]
            failures=[X for X in cases["scales"] if not real(exact[X][q])<=real(C)*real(X)**real(beta)]
            assert failures==outcome["complete_final_failure_windows"] and outcome["finite_validation_passed"]==(not failures)
            for control in outcome["controls"]:
                offset=0 if control["name"]=="all_positive" else M[4096]-4096
                slope=1-sum((a/d for d,a in rows),Q(0)); intercept=offset*(1-sum((a for d,a in rows),Q(0)))
                assert slope>0
                for X,number in control["moments"].items():
                    X=int(X); assert X>4096*max((d for d,a in rows),default=1)
                    own=X*unit_integral(slope*X+intercept,slope*2*X+intercept,q)
                    assert own==Q(number)
                failures=[int(X) for X,number in control["moments"].items() if not real(Q(number))<=real(C)*real(int(X))**real(beta)]
                assert failures==control["finite_failure_windows"] and control["uniform_sublinear_claim_false"]==(beta<q+1)
        print("Independent signed operator moments",index,program["family"],flush=True)
    zero=check_zero(archive["known_zero_dependency"],archive["archive"])
    # A genuinely bounded signed control with a root-erasing Mellin multiplier
    # is retained as a negative RH calibration, not promoted as an RH solution.
    bounded_controls=[]
    for X in (1,2,3,31,4096,65536,final["coefficient_cutoff"]):
        total=sum(mu[n]*(X//n) for n in range(1,X+1)); assert total==1
        bounded_controls.append([X,total])
    replay=directory/"replay"
    if not replay.exists():
        replay.mkdir(); shutil.copy2(directory/"protocol.json",replay/"protocol.json")
        subprocess.run([sys.executable,str(BASE/"signed_control_search.py"),"discover","--run-dir",str(replay)],check=True,cwd=BASE)
    for name in seal["files"]: assert sha(replay/name)==sha(directory/name)
    checks={"frozen_code_batches_seal_and_fresh_final_cases":True,
            "independent_full_mobius_prefix_and_sampled_signed_responses":True,
            "independent_complete_final_moment_integrals_and_negative_controls":True,
            "universal_lipschitz_cost_and_critical_inverse_multiplier_certificates":True,
            "moment_pointwise_and_RH_family_obligations_kept_conditional":True,
            "ordinary_zeta_zero_bridge_and_root_erasing_bounded_control":True,
            "deterministic_adaptation_selection_replay_and_worker_denials":True,
            "historical_priority_removed_from_acceptance_and_no_finite_to_global_promotion":True}
    out={"all_passed":True,"checks":checks,"independent_complete_inverse_coefficients":len(mu)-1,
         "independent_complete_moment_values":exact_count,"independent_sampled_moment_values":sampled_count,
         "ordinary_zero_audit":zero,"bounded_but_root_erasing_control":{"observations":bounded_controls,
          "all_scale_identity":"sum mu(n)*floor(X/n)=1, by divisor inversion", "mellin_multiplier":"zeta(s)",
          "RH_relevance_rejected":True},"source_final_sha256":sha(directory/"final_evaluation.json"),
         "protocol_sha256":digest(spec),"checker_code_sha256":sha(Path(__file__)),
         "proof_sha256":sha(BASE/"signed_control_proof.txt"),"mathematical_audit_imports_production_code":False,
         "replay_invokes_production_generator":True,"uniform_sublinear_signed_controls_verified":[],"RH_proved":False}
    (directory/"verification.json").write_text(json.dumps(out,indent=2)+"\n")
    print("Independent signed-control audit",len(checks),"/",len(checks),flush=True)


if __name__=="__main__": main()

#!/usr/bin/env python3
"""Independent complete-moment, recurrence, root and frozen-run audit."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import random
import subprocess
import sys
import flint
from check_stable_scale import read,sha,digest,BASE,audit_operator
from check_signed_control import independent_inverse,complete
from check_signed_mellin_transfer import zero_disk,real


def reciprocal_cost(c,program):
    q,B,A1=c["order"],Q(c["B"]),Q(c["transfer"]["A_1"])
    critical=2**(q//2+1); sigma=Q(3,4)
    weight=real(2)**real(Q(1,2)-sigma)
    norm=real(A1+B/critical)**real(Q(1,q)); geometric=norm/(1-weight)**2
    compact=sum((real(abs(Q(a)))*(real(d)**real(-sigma)-real(Q(1,d)))/real(1-sigma)
                 for d,a in program["operator_certificate"]["atoms"]),flint.arb(0))
    delta=Q(program["operator_certificate"]["selected_schur_certificate"]["uniform_multiplier_lower_bound"])
    return (geometric+compact)/real(delta)+1/real(sigma)


def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--run-dir",type=Path,required=True)
    args=parser.parse_args(); directory=args.run_dir.resolve(); flint.ctx.prec=640
    spec,seal=read(directory/"protocol.json"),read(directory/"seal.json")
    for name,expected in spec["code_sha256"].items(): assert sha(BASE/name)==expected
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"] and not seal["final_cases_exist_at_seal"]
    for name,expected in seal["files"].items(): assert sha(directory/name)==expected
    source=Path(spec["source_run"]); source_spec=read(source/"protocol.json"); previous=read(source/"verification.json")
    assert previous["all_passed"] and all(previous["checks"].values())
    assert sha(source/"archive.json")==spec["source_archive_sha256"] and sha(source/"verification.json")==spec["source_verification_sha256"]
    assert spec["input_operators"]==[r["program"] for r in read(source/"archive.json")["archive"]]
    for p in spec["input_operators"]: audit_operator(p,source_spec)
    cases,final,archive=read(directory/"final_cases.json"),read(directory/"final_evaluation.json"),read(directory/"archive.json")
    assert cases["seal_sha256"]==final["seal_sha256"]==digest(seal) and final["cases_sha256"]==digest(cases)
    assert cases["created_after_selection_closed"] and final["selection_closed_before_final_data"]
    rule=spec["final_cases"]; rng=random.Random(int(cases["evaluator_seed"]))
    large=sorted(rng.sample(range(rule["large_range"][0],rule["large_range"][1]+1),rule["large_count"]))
    intermediate=sorted(rng.sample(range(rule["intermediate_range"][0],rule["intermediate_range"][1]+1),rule["intermediate_count"]))
    assert cases["large"]==large and cases["intermediate"]==intermediate and cases["scales"]==sorted(rule["boundary"]+intermediate+large)
    assert all(archive["worker_access_denials"].values()) and not archive["final_data_used"] and not archive["historical_priority_used"]
    batch,train,val=read(directory/"candidate_batch.json"),read(directory/"discovery_data.json"),read(directory/"validation_data.json")
    assert batch["frozen_before_validation"] and batch["validation_coefficients_not_computed_before_batch_freeze"]
    assert batch["training_sha256"]==sha(directory/"discovery_data.json") and batch["protocol_sha256"]==digest(spec)
    assert len(batch["candidates"])==len(val["candidates"])
    mu,M=independent_inverse(final["coefficient_cutoff"])
    assert digest(mu)==final["inverse_coefficient_sha256"]
    assert final["coefficient_cutoff"]==4*max(cases["scales"])<=spec["maximum_final_cutoff"]
    assert train["coefficient_cutoff"]==4*max(spec["training_scales"])
    assert val["coefficient_cutoff"]==4*max(spec["validation_scales"])
    for data in (train,val): assert digest(mu[:data["coefficient_cutoff"]+1])==data["inverse_coefficient_sha256"]
    delayed=mu[:4097]+[1]*(len(mu)-4097); delayed_M=[0]*len(mu)
    for n in range(1,len(mu)): delayed_M[n]=delayed_M[n-1]+delayed[n]
    used={c["program_id"] for c in archive["archive"]}; actual_values={}; delayed_values={}
    actual_count=delay_count=0
    for i,p in enumerate(spec["input_operators"]):
        scales=set(spec["training_scales"]+spec["validation_scales"])
        if p["id"] in used: scales|=set(cases["scales"])
        windows=sorted({x for X in scales for x in (X,2*X)}); rows=[(d,Q(a)) for d,a in p["operator_certificate"]["atoms"]]
        values=complete(mu,M,rows,windows,spec["orders"]); actual_values[p["id"]]=values
        actual_count+=len(values)*len(spec["orders"])
        for phase,expected in ((train,train["moments"][p["id"]]),(val,val["moments"][p["id"]])):
            for X,observed in expected.items(): assert values[int(X)]=={int(q):Q(v) for q,v in observed.items()}
        if p["id"] in used:
            observed=final["actual_moments"][p["id"]]
            for X,out in observed.items(): assert values[int(X)]=={int(q):Q(v) for q,v in out.items()}
            delayed_windows=sorted({x for X in large for x in (X,2*X)})
            delay=complete(delayed,delayed_M,rows,delayed_windows,spec["orders"]); delayed_values[p["id"]]=delay
            delay_count+=len(delay)*len(spec["orders"])
            assert {str(X):{str(q):str(v) for q,v in r.items()} for X,r in delay.items()}==final["delayed_positive_moments"][p["id"]]
        print("Independent exact signed-defect moments",i+1,"/",len(spec["input_operators"]),flush=True)
    zero,margin=zero_disk(spec["known_zero_dependency"]); programs={p["id"]:p for p in spec["input_operators"]}
    for before,c in zip(batch["candidates"],val["candidates"]):
        assert before=={k:v for k,v in c.items() if k!="exact_validation_failure_windows"}
        assert c["id"]==digest({k:c[k] for k in ("program_id","order","rho","gamma","B")})
        p=programs[c["program_id"]]; q,rho,gamma,B=c["order"],Q(c["rho"]),Q(c["gamma"]),Q(c["B"])
        values=actual_values[p["id"]]
        assert q in spec["orders"] and abs(rho)<=128 and 0<=gamma<=q+1 and B>=0
        positive={X:max(values[2*X][q]-rho*values[X][q],Q(0)) for X in spec["training_scales"]}
        assert {str(X):str(v) for X,v in positive.items()}==c["positive_training_defects"]
        assert all(real(v)<=real(B)*real(X)**real(gamma) for X,v in positive.items())
        failures=[X for X in spec["validation_scales"] if not real(values[2*X][q]-rho*values[X][q])<=real(B)*real(X)**real(gamma)]
        assert failures==c["exact_validation_failure_windows"]
        template=c["transfer"]; assert template["q"]==q and Q(template["rho"])==rho and Q(template["gamma"])==gamma and Q(template["B"])==B
        assert Q(template["A_1"])==values[1][q]
        critical=2**(q//2+1); sufficient=rho<=critical and gamma<=Q(q,2)+1
        impossible=max(rho,Q(0))<critical and gamma<Q(q,2)+1
        assert template["RH_sufficient_with_global_zero_bridge"]==sufficient
        assert template["strictly_subcritical_recurrence_ruled_out_if_critical_zero_multiplier_nonzero"]==impossible
        L=Q(p["operator_certificate"]["lipschitz_constant"])
        elementary=L**q*Q(4**(q+1)-2**(q+1)+max(-rho,Q(0))*(2**(q+1)-1),q+1)
        generic=gamma>=q+1 and B>=elementary
        assert Q(c["generic_universal_defect_upper_coefficient"])==elementary
        assert c["generic_magnitude_premise_proved"]==template["uniform_signed_recurrence_premise_proved"]==generic
        w=(-zero*real(p["base"]).log()).exp(); F=flint.acb(0)
        for coefficient in reversed(p["polynomial"]): F=F*w+real(Q(coefficient))
        nonzero=bool(F.abs_lower()>0); all_height=p["operator_certificate"]["all_height_critical_multiplier_certified"]
        assert c["actual_zero_multiplier_nonzero"]==nonzero and c["all_height_multiplier_nonzero"]==all_height
        status=("uniform_recurrence_ruled_out_by_actual_zeta_zero" if nonzero and impossible else
                "numerical_lead_missing_all_height_bridge" if not all_height else
                "RH_sufficient_recurrence_missing_uniform_arithmetic_proof" if sufficient else
                "generic_magnitude_bound_proved_below_RH_strength" if generic else
                "numerical_recurrence_not_at_RH_strength")
        assert c["analytic_status"]==status and not template["RH_proved"]
        if status=="RH_sufficient_recurrence_missing_uniform_arithmetic_proof":
            bound=reciprocal_cost(c,p)
            assert flint.arb(c["conditional_reciprocal_bound_ball"]).contains(bound)
            assert abs(c["conditional_log_cost"]-float(bound.upper().log()))<1e-10
            assert not generic
    assert len(archive["archive"])==spec["archive_size"]==len(final["outcomes"])
    for c,out in zip(archive["archive"],final["outcomes"]):
        assert c in val["candidates"] and out["candidate_id"]==c["id"]
        values=actual_values[c["program_id"]]; p=programs[c["program_id"]]
        q,rho,gamma,B=c["order"],Q(c["rho"]),Q(c["gamma"]),Q(c["B"])
        defects={X:values[2*X][q]-rho*values[X][q] for X in cases["scales"]}
        assert {str(X):str(v) for X,v in defects.items()}==out["exact_signed_defects"]
        failures=[X for X,v in defects.items() if not real(v)<=real(B)*real(X)**real(gamma)]
        assert failures==out["complete_final_failure_windows"] and out["finite_windows_passed"]==(not failures)
        slope=sum((Q(a)/p["base"]**k for k,a in enumerate(p["polynomial"])),Q(0))
        coefficient=slope**q*Q(2**(q+1)-1,q+1)
        positive={X:coefficient*(2**(q+1)-rho)*X**(q+1) for X in large}
        delay=delayed_values[c["program_id"]]; delayed_defects={X:delay[2*X][q]-rho*delay[X][q] for X in large}
        for name,observed in (("all_positive",positive),("delayed_positive",delayed_defects)):
            assert {str(X):str(v) for X,v in observed.items()}==out["control_exact_defects"][name]
            failures=[X for X,v in observed.items() if not real(v)<=real(B)*real(X)**real(gamma)]
            assert failures==out["control_failure_windows"][name]
        assert out["both_positive_control_uniform_claims_false"]==bool(slope and rho<2**(q+1) and gamma<q+1)
        assert out["uniform_signed_recurrence_proved"]==c["generic_magnitude_premise_proved"] and not out["reselected"]
    replay=directory/"replay"
    if not replay.exists():
        replay.mkdir(); (replay/"protocol.json").write_bytes((directory/"protocol.json").read_bytes())
        subprocess.run([sys.executable,str(BASE/"signed_defect_search.py"),"discover","--run-dir",str(replay)],check=True,cwd=BASE)
    for name in seal["files"]: assert sha(directory/name)==sha(replay/name),"deterministic recurrence replay changed: "+name
    assert final["uniform_sublinear_signed_controls_verified"]==[] and not final["RH_proved"]
    checks={"frozen_sources_input_operator_provenance_batches_seal_and_fresh_cases":True,
            "independent_complete_arithmetic_prefix_and_training_validation_final_moments":True,
            "independent_signed_defects_parameter_domains_and_training_upper_bounds":True,
            "conditional_logarithmic_recurrence_transfer_and_reciprocal_cost_checked":True,
            "actual_ordinary_zero_obstruction_recomputed":True,
            "generic_all_scale_magnitude_certificates_kept_below_RH_strength":True,
            "exact_positive_and_complete_delayed_positive_controls":True,
            "deterministic_learning_selection_replay_and_worker_denials":True,
            "no_finite_to_uniform_promotion_and_historical_priority_not_a_gate":True}
    audit={"all_passed":True,"checks":checks,"exact_actual_moment_values_checked":actual_count,
           "exact_delayed_positive_moment_values_checked":delay_count,"complete_coefficient_cutoff":len(mu)-1,
           "source_final_sha256":sha(directory/"final_evaluation.json"),"protocol_sha256":digest(spec),
           "checker_sha256":sha(Path(__file__)),"independent_nested_Rouche_margin":margin,
           "mathematical_audit_imports_production_code":False,"replay_invokes_production_generator":True,
           "uniform_sublinear_signed_controls_verified":[],"RH_proved":False}
    (directory/"verification.json").write_text(json.dumps(audit,indent=2)+"\n")
    print("Independent signed-defect audit",sum(checks.values()),"/",len(checks),flush=True)


if __name__=="__main__": main()

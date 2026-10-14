#!/usr/bin/env python3
"""Independent rational disk, inverse, arithmetic moment and provenance audit."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path
import random
import subprocess
import sys
import flint

# These are existing independent checker primitives. No production grammar,
# moment integrator, Schur recursion or coefficient generator is imported.
from check_signed_control import independent_inverse, complete, value, unit_integral, check_zero

BASE=Path(__file__).resolve().parent


def read(path): return json.loads(Path(path).read_text())
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def digest(data): return hashlib.sha256(json.dumps(data,sort_keys=True,separators=(",", ":"),allow_nan=False).encode()).hexdigest()
def real(x): x=Q(x); return flint.arb(x.numerator)/x.denominator


def independent_disk(p,radius):
    # Homogeneous, unnormalised recursion. Production normalises to constant
    # one after each step. The quotient checks connect the two representations.
    current=[Q(c)*radius**k for k,c in enumerate(p)]; steps=[]; delta=Q(1)
    while len(current)>1:
        constant,leading=current[0],current[-1]
        reflection=leading/constant
        if abs(leading)>=abs(constant):
            return False,steps,None,reflection
        reduced=[constant*current[k]-leading*current[-1-k] for k in range(len(current)-1)]
        steps.append({"polynomial":[str(c/constant) for c in current],
                      "reflection_coefficient":str(reflection),
                      "reduced":[str(c/reduced[0]) for c in reduced]})
        delta*=1-abs(reflection); current=reduced
    return True,steps,delta,None


def newton_inverse(p,count):
    exact=flint.fmpq_poly([flint.fmpq(c.numerator,c.denominator) for c in p])
    reciprocal=flint.fmpq_poly([1]); length=1
    while length<count:
        length=min(count,2*length)
        reciprocal=(reciprocal*(2-exact*reciprocal)).truncate(length)
    assert (exact*reciprocal).truncate(count)==flint.fmpq_poly([1])
    return [Q(str(reciprocal[k])) for k in range(count)]


def inverse_bound(base,p,chosen,theta,count):
    if len(p)==1: return real(1)
    coefficients=newton_inverse(p,count)
    radius,delta=Q(chosen["radius"]),Q(chosen["uniform_multiplier_lower_bound"])
    weight=real(base)**real(-theta); ratio=weight/real(radius)
    assert ratio<1
    exact=sum((real(abs(c))*weight**k for k,c in enumerate(coefficients)),flint.arb(0))
    return exact+ratio**count/(real(delta)*(1-ratio))


def audit_operator(program,spec):
    b=program["base"]; p=[Q(c) for c in program["polynomial"]]
    assert type(b) is int and b in spec["bases"] and p[0]==1
    assert len(p)-1<=spec["maximum_degree"] and (len(p)==1 or p[-1])
    assert all(abs(c)<=spec["coefficient_resource_cap"] for c in p)
    assert program["id"]==digest({"base":b,"polynomial":[str(c) for c in p]})
    cert=program["operator_certificate"]
    assert cert["base"]==b and cert["polynomial"]==program["polynomial"]
    rows=[[b**k,str(-c)] for k,c in enumerate(p) if k and c]
    assert cert["atoms"]==rows
    L=sum((abs(c)/b**k for k,c in enumerate(p)),Q(0))
    assert Q(cert["lipschitz_constant"])==L
    triangle=sum((real(abs(c))/real(b**k).sqrt() for k,c in enumerate(p) if k),flint.arb(0))
    assert flint.arb(cert["triangle_critical_cost_ball"]).contains(triangle)
    assert cert["triangle_certificate_available"]==bool(triangle<1)
    successes=[]
    assert len(cert["schur_attempts"])==4
    for attempt in cert["schur_attempts"]:
        radius=Q(attempt["radius"])
        assert radius>0 and b*radius*radius>1
        ok,steps,delta,failed=independent_disk(p,radius)
        assert attempt["certified"]==ok and attempt["steps"]==steps
        if ok:
            assert Q(attempt["uniform_multiplier_lower_bound"])==delta>0
            successes.append(attempt)
            inverse=newton_inverse(p,spec["inverse_prefix_length"])
            assert all(abs(c)*radius**k<=1/delta for k,c in enumerate(inverse))
        else:
            assert Q(attempt["failed_leading_coefficient"])==failed
    assert cert["all_height_critical_multiplier_certified"]==bool(successes)
    assert not cert["uniform_signed_arithmetic_estimate_proved"]
    if successes:
        chosen=cert["selected_schur_certificate"]; assert chosen in successes
        bound=inverse_bound(b,p,chosen,Q(1,2),spec["inverse_prefix_length"])
        assert flint.arb(cert["critical_weight_inverse_norm_upper_ball"]).contains(bound)
        assert cert["outside_triangle_domain_certified"]==(not cert["triangle_certificate_available"])
        # The inverse certificate also precludes erasing a positive linear input.
        assert sum((c/b**k for k,c in enumerate(p)),Q(0))!=0
    return p,L


def sampled(mu,M,rows,X,cells,q):
    return Q(X,len(cells))*sum((unit_integral(value(mu,M,rows,n),value(mu,M,rows,n+1),q) for n in cells),Q(0))


def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--run-dir",type=Path,required=True)
    args=parser.parse_args(); directory=args.run_dir.resolve(); flint.ctx.prec=512
    spec,seal=read(directory/"protocol.json"),read(directory/"seal.json")
    for name,expected in spec["code_sha256"].items(): assert sha(BASE/name)==expected
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"] and not seal["final_cases_exist_at_seal"]
    for name,expected in seal["files"].items(): assert sha(directory/name)==expected
    cases,final,archive=read(directory/"final_cases.json"),read(directory/"final_evaluation.json"),read(directory/"archive.json")
    assert final["seal_sha256"]==cases["seal_sha256"]==digest(seal)
    assert final["cases_sha256"]==digest(cases) and cases["created_after_selection_closed"]
    rule=spec["final_cases"]; rng=random.Random(int(cases["evaluator_seed"]))
    large=sorted(rng.sample(range(rule["large_range"][0],rule["large_range"][1]+1),rule["large_count"]))
    intermediate=sorted(rng.sample(range(rule["intermediate_range"][0],rule["intermediate_range"][1]+1),rule["intermediate_count"]))
    assert cases["large"]==large and cases["intermediate"]==intermediate
    assert cases["scales"]==sorted(rule["boundary"]+intermediate+large)
    rng=random.Random(int(cases["evaluator_seed"])+1)
    cells={str(X):sorted(rng.sample(range(X,2*X),min(X,spec["negative_control_cells_per_window"]))) for X in large}
    assert cells==cases["control_cells"]
    assert not archive["final_data_used"] and not archive["historical_priority_used"]
    assert all(archive["worker_access_denials"].values()) and not archive["uniform_signed_estimate_proved"]
    batch=read(directory/"candidate_batch.json"); discovery=read(directory/"discovery_data.json")
    validation=read(directory/"validation_data.json")
    assert batch["frozen_before_validation"] and archive["batch_sha256"]==digest(batch)
    assert batch["protocol_sha256"]==digest(spec) and batch["discovery_sha256"]==sha(directory/"discovery_data.json")
    for p in batch["programs"]: audit_operator(p,spec)
    for promotion in batch["promotions"]:
        left=flint.fmpq_poly([flint.fmpq(c) for c in promotion["left"]])
        right=flint.fmpq_poly([flint.fmpq(c) for c in promotion["right"]])
        expected=flint.fmpq_poly([flint.fmpq(c) for c in promotion["result"]])
        assert left*right==expected
    mu,M=independent_inverse(final["coefficient_cutoff"])
    assert final["coefficient_cutoff"]==2*max(cases["scales"])<=spec["maximum_final_cutoff"]
    assert digest(mu)==final["inverse_coefficient_sha256"]
    assert digest(mu[:discovery["coefficient_cutoff"]+1])==discovery["inverse_coefficient_sha256"]
    delayed=mu[:4097]+[1]*(len(mu)-4097); delayed_M=[0]*len(mu)
    for n in range(1,len(mu)): delayed_M[n]=delayed_M[n-1]+delayed[n]
    exact_count=sampled_count=0; supported_for_zero=[]
    assert len(final["records"])==len(archive["archive"])==spec["archive_size"]
    for i,(row,result) in enumerate(zip(archive["archive"],final["records"])):
        program=row["program"]; p,L=audit_operator(program,spec); b=program["base"]
        rows=[(int(d),Q(a)) for d,a in program["operator_certificate"]["atoms"]]
        assert result["program_id"]==program["id"] and result["every_unit_interval_included"]
        for source,key in ((discovery,"sampled_training_moments"),(validation,"sampled_validation_moments")):
            for X,observed in row[key].items():
                X=int(X)
                for q,value_encoded in observed.items():
                    q=int(q); actual=sampled(mu,M,rows,X,source["cells"][str(X)],q)
                    assert actual==Q(value_encoded); sampled_count+=1
        exact=complete(mu,M,rows,cases["scales"],spec["orders"])
        assert {str(X):{str(q):str(v) for q,v in values.items()} for X,values in exact.items()}==result["exact_complete_window_moments"]
        exact_count+=len(exact)*len(spec["orders"])
        for e,out in zip(row["estimates"],result["outcomes"]):
            q,beta,C=e["order"],Q(e["beta"]),Q(e["constant"]); theta=beta/(q+1)
            assert out["order"]==q
            failures=[X for X,values in exact.items() if not real(values[q])<=real(C)*real(X)**real(beta)]
            assert failures==out["complete_final_failure_windows"] and out["finite_windows_passed"]==(not failures)
            transfer=e["transfer"]; cert=program["operator_certificate"]
            assert Q(transfer["pointwise_exponent"])==theta
            eligible=cert["all_height_critical_multiplier_certified"] and Q(1,2)<=theta<=1
            assert transfer["inverse_transfer_certified"]==eligible
            if eligible:
                inverse=inverse_bound(b,p,cert["selected_schur_certificate"],theta,spec["inverse_prefix_length"])
                residual_constant=(2**(q+2)*real(L)*real(C))**real(Q(1,q+1))
                full=inverse*(residual_constant+real(L)+abs(residual_constant-real(L)))/2
                assert flint.arb(transfer["inverse_norm_upper_ball"]).contains(inverse)
                assert flint.arb(transfer["original_M_pointwise_constant_upper_ball"]).contains(full)
                if "full_cost_log_score" in e:
                    score=full*real(spec["score_anchor"])**real(theta-Q(1,2))
                    assert abs(e["full_cost_log_score"]-float(score.upper().log()))<1e-10
            if cert["all_height_critical_multiplier_certified"] and theta<Q(1,2):
                assert e["status"]=="ruled_out_by_ordinary_zero"
            assert not transfer["uniform_premise_proved"] and not transfer["RH_proved"]
            assert not out["uniform_moment_premise_proved"] and not out["reselected"]
            slope=sum((c/b**k for k,c in enumerate(p)),Q(0))
            positive={X:slope**q*Q((2*X)**(q+1)-X**(q+1),q+1) for X in large}
            assert {str(X):str(v) for X,v in positive.items()}==out["positive_control_exact_moments"]
            positive_failures=[X for X,v in positive.items() if not real(v)<=real(C)*real(X)**real(beta)]
            assert positive_failures==out["positive_control_failure_windows"]
            delay={X:sampled(delayed,delayed_M,rows,X,cells[str(X)],q) for X in large}
            assert {str(X):str(v) for X,v in delay.items()}==out["delayed_positive_sampled_moments"]
            delay_failures=[X for X,v in delay.items() if not real(v)<=real(C)*real(X)**real(beta)]
            assert delay_failures==out["delayed_positive_sample_failure_windows"]
            assert out["both_positive_controls_uniform_sublinear_claim_false"]==bool(slope and beta<q+1)
        # This finite native check is allowed for unsupported leads as well;
        # it does not certify all-height nonvanishing for such a lead.
        supported_for_zero.append({"program":{"atoms":program["operator_certificate"]["atoms"]}})
        print("Independent stable moments",i+1,"/",len(archive["archive"]),flush=True)
    zero=check_zero(archive["known_zero_dependency"],supported_for_zero)
    ok,steps,delta,failed=independent_disk([Q(1),Q(-2)],Q(3,4))
    assert not ok and failed==Q(-3,2)
    replay=directory/"replay"
    if not replay.exists():
        replay.mkdir(); (replay/"protocol.json").write_bytes((directory/"protocol.json").read_bytes())
        subprocess.run([sys.executable,str(BASE/"stable_scale_search.py"),"discover","--run-dir",str(replay)],check=True,cwd=BASE)
    for name in seal["files"]: assert sha(directory/name)==sha(replay/name),"deterministic replay changed: "+name
    assert final["selection_closed_before_final_data"] and not final["RH_proved"]
    assert final["uniform_sublinear_signed_controls_verified"]==[]
    checks={"frozen_sources_batches_seal_and_recreated_fresh_final_cases":True,
            "independent_unnormalised_Schur_recursion_and_all_height_margins":True,
            "independent_Newton_reciprocal_and_Cauchy_inverse_costs":True,
            "complete_actual_arithmetic_prefix_and_final_window_moments":True,
            "full_cost_transfer_kept_conditional_and_unsupported_leads_retained":True,
            "exact_positive_and_sampled_delayed_positive_controls":True,
            "ordinary_zero_recomputed_and_root_erasing_polynomial_rejected":True,
            "deterministic_generation_promotion_selection_replay_and_worker_denials":True}
    write={"all_passed":True,"checks":checks,"exact_complete_moment_values":exact_count,
           "independent_sampled_moment_values":sampled_count,"independent_full_inverse_coefficients":len(mu)-1,
           "native_zero_audit":zero,"mathematical_audit_imports_production_code":False,
           "replay_invokes_production_generator":True,"final_sha256":sha(directory/"final_evaluation.json"),
           "protocol_sha256":digest(spec),"checker_sha256":sha(Path(__file__)),
           "uniform_sublinear_signed_controls_verified":[],"RH_proved":False}
    (directory/"verification.json").write_text(json.dumps(write,indent=2)+"\n")
    print("Independent stable-scale audit",sum(checks.values()),"/",len(checks),flush=True)


if __name__=="__main__": main()

#!/usr/bin/env python3
"""Independent Stieltjes-inverse certificates and fresh log-loss repair audit."""
import argparse
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import random
import subprocess
import sys
import flint
from check_prime_twists import (read,sha,digest,real,prime_coefficients,independent_observe,enclose,comparisons)

BASE=Path(__file__).resolve().parent


def class_matches(p,c):
    r=p["leading_index"];delta=Q(p["delta"])
    return (p["channel"]=="log" and Q(c["log_power"])==0 and Q(c["theta"])+r*delta==Q(1,2)
        and all((j-r)*delta>=Q(1,2) for j,(a,b) in enumerate(zip(p["coefficients"],p["normalizers"])) if Q(a)!=Q(b)))


def check_certificate(p,cert):
    r=p["leading_index"];d=Q(p["delta"]);nu=r*d;tail=list(map(Q,p["coefficients"][r+1:]));S=sum(map(abs,tail),Q(0))
    z0=Q(cert["rational_root_cutoff"]);T=cert["eventual_integer_threshold"]
    assert p["coefficients"][r]=="1" and not any(map(Q,p["coefficients"][:r]))
    assert 0<z0<=1 and S*z0<=Q(1,2)
    assert T>=2 and T&(T-1)==0 and Q(T)**d.numerator*z0**d.denominator>=1
    assert z0==(min(Q(1),Q(1)/(2*S)) if S else Q(1))
    if T>2:assert Q(T//2)**d.numerator*z0**d.denominator<1
    L=sum((j*abs(c) for j,c in enumerate(tail,1)),Q(0));M=2*nu+4*d*L
    assert cert["leading_shift"]==str(nu) and cert["tail_absolute_sum"]==str(S)
    assert cert["eventual_normalized_weight_interval"]==["1/2","3/2"] and cert["inverse_weight_constant"]=="2"
    assert Q(cert["inverse_weight_derivative_constant"])==M
    assert cert["normalizer_mismatch_shifts"]==[str((j-r)*d) for j,(a,b) in enumerate(zip(p["coefficients"],p["normalizers"])) if Q(a)!=Q(b)]
    assert all(Q(a)>=Q(1,2) for a in cert["normalizer_mismatch_shifts"])
    assert cert["status"]=="uniform_claim_ruled_out_by_imported_prime_error_oscillation" and not cert["RH_proved"]
    # An independent series derivative checks the inversion backend numerically;
    # its universal certificate is the exact polynomial/triangle inequalities.
    for t in (2*T,3*T):
        var=flint.arb_series([real(t),1],prec=2)
        P=sum((real(c)*(var.log()*real(-j*d)).exp() for j,c in enumerate(p["coefficients"]) if Q(c)),flint.arb_series([0],prec=2))
        inverse=1/P
        assert inverse[0]>0 and inverse[0]<=2*real(t)**real(nu)
        assert abs(inverse[1])<=real(M)*real(t)**real(nu-1)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--run-dir",type=Path,required=True);directory=parser.parse_args().run_dir.resolve()
    spec,seal,gate,repairs,cases,final=(read(directory/n) for n in ("protocol.json","seal.json","compatibility.json","repairs.json","final_cases.json","final_evaluation.json"))
    for name,h in spec["code_sha256"].items():assert sha(BASE/name)==h
    for name in spec["this_stage_source_files"]:assert sha(directory/"frozen_source"/name)==spec["code_sha256"][name]
    dependency=spec["oscillation_dependency"];assert sha(dependency["path"])==dependency["sha256"] and dependency["proof_imported_not_independently_reproved"] and not dependency["machine_formalized"]
    source=Path(spec["source_run"])
    for name,h in spec["source_sha256"].items():assert sha(source/name)==h
    from prime_twist_report import summary as source_summary
    parent=source_summary(source);prior_cut=parent["complete_coefficient_cutoff"]
    if spec["source_coverage"]:
        from prime_twist_coverage_report import summary as coverage_summary
        cv=coverage_summary(spec["source_coverage"]["run_directory"]);assert Path(cv["source_run"])==source
        assert cv["verification_sha256"]==spec["source_coverage"]["verification_sha256"];prior_cut=max(prior_cut,cv["cutoff"])
    assert spec["fresh_final_interval"]["start"]==prior_cut+1
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"] and not seal["final_cases_exist_at_seal"]
    for name,h in seal["files"].items():assert sha(directory/name)==h
    assert repairs["selection_closed"] and not repairs["final_data_used"]
    replay=directory/"replay"
    if not replay.exists():
        replay.mkdir();(replay/"protocol.json").write_bytes((directory/"protocol.json").read_bytes())
        subprocess.run([sys.executable,str(BASE/"prime_oscillation_audit.py"),"discover","--run-dir",str(replay)],check=True,cwd=BASE)
    for name in ("compatibility.json","repairs.json","seal.json"):assert sha(directory/name)==sha(replay/name)
    batch=read(source/"candidate_batch.json");ps={p["id"]:p for p in batch["programs"]};cs={c["id"]:c for c in batch["candidates"]}
    expected={cid for cid,c in cs.items() if class_matches(ps[c["program_id"]],c)}
    assert expected==set(gate["candidate_certificates"]) and gate["complete_candidates_considered"]==len(cs)
    flint.ctx.prec=768;seen={}
    for cid,cert in gate["candidate_certificates"].items():
        p=ps[cs[cid]["program_id"]]
        if p["id"] not in seen:check_certificate(p,cert);seen[p["id"]]=cert
        else:assert cert==seen[p["id"]]
    assert gate["class_status_counts"]==dict(Counter(c["analytic_status"] for cid,c in cs.items() if cid in expected))
    archive=read(source/"archive.json")["archive"];rejected=[c["id"] for c in archive if c["id"] in expected]
    assert rejected==gate["archived_candidates_ruled_out"]
    validation=read(source/"validation_data.json")["candidates"];selected=[]
    for c in archive:
        if c["id"] not in expected:continue
        pool=[v for v in validation if v["program_id"]==c["program_id"] and v["analytic_status"].startswith("RH_sufficient") and Q(v["log_power"])>0 and v["transfer"]["ordinary_zeta_exponent"]==c["transfer"]["ordinary_zeta_exponent"]]
        if pool:
            v=sorted(pool,key=lambda v:(bool(v["validation_failures"] or v["validation_unresolved"]),v["log_reciprocal_cost"],Q(v["log_power"]),Q(v["constant"]),v["id"]))[0]
            selected.append({"rejected_source_candidate_id":c["id"],"candidate":v,"program":ps[v["program_id"]]})
    assert selected==repairs["repairs"]
    N=random.Random(int(cases["evaluator_seed"])).randint(*spec["fresh_final_interval"]["endpoint_range"])
    assert cases["endpoint"]==N==final["coefficient_cutoff"] and cases["start"]==prior_cut+1 and cases["created_after_selection_closed"]
    assert cases["seal_sha256"]==final["seal_sha256"]==digest(seal) and final["cases_sha256"]==digest(cases)
    f=prime_coefficients(N);assert final["coefficient_sha256"]==digest(list(map(str,f)))
    programs=[r["program"] for r in selected];points=list(range(cases["start"],N+1))
    observed=independent_observe(programs,f,points);point_count=0
    assert set(observed)==set(final["values"]) and len(final["outcomes"])==len(selected)
    for pid,row in observed.items():
        assert set(row)==set(final["values"][pid])
        for n,v in row.items():enclose(final["values"][pid][n],v);point_count+=1
    for row,o in zip(selected,final["outcomes"]):
        c,p=row["candidate"],row["program"];states=comparisons(c,p,observed[p["id"]])
        assert c["id"]==o["candidate_id"] and o["comparisons"]==len(points)
        assert o["failures"]==[int(n) for n,v in states.items() if v=="fail"] and o["unresolved"]==[int(n) for n,v in states.items() if v=="unresolved"]
        assert o["finite_interval_passed"]==all(v=="pass" for v in states.values()) and not o["uniform_signed_premise_proved"]
    assert not final["RH_proved"] and not final["uniform_RH_sufficient_signed_controls_verified"]
    checks={"frozen_source_paper_seal_and_deterministic_replay_checked":True,
        "generic_class_test_applied_to_complete_candidate_batch":True,
        "exact_eventual_polynomial_inverse_and_derivative_certificates_checked":True,
        "weighted_channels_and_positive_log_losses_retained":True,
        "imported_oscillation_scope_distinguished_from_reproved_inversion":True,
        "original_finite_outcomes_preserved_and_later_rejections_recorded":True,
        "positive_log_repairs_selected_only_from_source_validation":True,
        "every_fresh_integer_repair_point_independently_checked":True,
        "actual_prime_power_coefficients_and_exact_centers_checked":True,
        "no_RH_strength_uniform_premise_promoted_from_finite_success":True}
    result={"all_passed":all(checks.values()),"checks":checks,"protocol_sha256":digest(spec),"final_sha256":sha(directory/"final_evaluation.json"),
        "checker_sha256":sha(BASE/"check_prime_oscillation.py"),"complete_candidates_checked":len(cs),"oscillation_certificates_checked":len(expected),
        "distinct_eventual_inverse_programs_checked":len(seen),"archived_candidates_ruled_out":len(rejected),"repairs_checked":len(selected),
        "fresh_point_values_checked":point_count,"exact_coefficients_checked":N,"source_paper_sha256":dependency["sha256"],
        "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    (directory/"verification.json").write_text(__import__("json").dumps(result,indent=2)+"\n")
    print("Independent prime-oscillation audit",sum(checks.values()),"/",len(checks),flush=True)


if __name__=="__main__":main()

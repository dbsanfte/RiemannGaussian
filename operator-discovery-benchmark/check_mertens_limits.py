#!/usr/bin/env python3
"""Independent exact limit/inverse algebra and complete fresh repair audit."""
from fractions import Fraction as Q
from pathlib import Path
import argparse,json,hashlib,subprocess,sys,tempfile,math
import flint
from check_fractional_remainders import real,sieve,tables,observer,expected_outcome,compare_outcome

BASE=Path(__file__).resolve().parent
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(v):return hashlib.sha256(json.dumps(v,sort_keys=True,separators=(",",":"),allow_nan=False).encode()).hexdigest()


def gate(p,c):
    cc,bb=list(map(Q,p["coefficients"])),list(map(Q,p["normalizers"]))
    if any(cc[j]!=bb[j] for j in range(1,len(cc))) or Q(c["theta"])!=Q(1,2) or Q(c["log_power"]) or Q(c["parameter_power"]):return None
    S=sum(cc,Q(0));B=sum(bb,Q(0))
    if not S:return None
    lam=1-B/S
    if lam==Q(1,2):return None
    K=(1+abs(B/S)/abs(lam-Q(1,2)))/abs(S) if B else 1/abs(S)
    maximum=Q(c["constant"])*K
    if maximum>Q(7,4):return None
    return S,B,lam,K,maximum


def integral_power(a,b,exponent):
    exponent=Q(exponent)
    return (real(b)/real(a)).log() if not exponent else (real(b)**real(exponent)-real(a)**real(exponent))/real(exponent)


def finite_inverse_calibration():
    mu,_=sieve(32);M=[0]*33;m=[Q(0)]*33
    for n in range(1,33):M[n]=M[n-1]+mu[n];m[n]=m[n-1]+Q(mu[n],n)
    rows=[]
    for S,B in [(Q(1),Q(1)),(Q(1),Q(1,4)),(Q(-2),Q(1)),(Q(3),Q(0))]:
        r=B/S;lam=1-r;delta=B-S
        for x in [Q(2),Q(3),Q(13,3),Q(37,2),Q(32)]:
            n=x.numerator//x.denominator;F=B*x*m[n]-delta*M[n];integral=flint.arb(0)
            for k in range(1,n+1):
                end=min(x,Q(k+1))
                if end>k:integral+=real(B*m[k])*integral_power(k,end,1-lam)-real(delta*M[k])*integral_power(k,end,-lam)
            recovered=real(F/S)-real(r/S)*real(x)**real(lam)*integral
            assert recovered.contains(M[n])
            rows.append({"coefficient_sum":str(S),"normalizer_sum":str(B),"x":str(x),"recovered_Mertens_ball":str(recovered),"exact_Mertens_value":M[n]})
    return rows


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--run-dir",required=True);a=ap.parse_args();directory=Path(a.run_dir).resolve();flint.ctx.prec=384
    spec=read(directory/"protocol.json");source=Path(spec["source_run"]);seal=read(directory/"seal.json");audit=read(directory/"compatibility.json");repairs=read(directory/"repairs.json")["repairs"]
    final=read(directory/"final_evaluation.json");cases=read(directory/"final_cases.json");checks={}
    for n,h in spec["code_sha256"].items():assert sha(BASE/n)==h
    for n in spec["this_stage_source_files"]:assert sha(directory/"frozen_source"/n)==spec["code_sha256"][n]
    for n,h in spec["source_sha256"].items():assert sha(source/n)==h
    from fractional_remainder_report import summary as source_summary
    parent=source_summary(source)
    for n,h in seal["files"].items():assert sha(directory/n)==h
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"] and not seal["final_cases_exist_at_seal"]
    assert final["protocol_sha256"]==digest(spec) and final["seal_sha256"]==cases["seal_sha256"]==digest(seal) and final["cases_sha256"]==digest(cases)
    assert cases["created_after_selection_closed"]
    checks["frozen_source_parent_and_sealed_fresh_case_integrity"]=True
    dep=spec["named_external_dependency"];assert sha(dep["path"])==dep["sha256"] and dep["imported_not_independently_reproduced"] and not dep["machine_formalized"]
    assert Q("1.837625")>Q(7,4) and dep["theorem"]=="6.1"
    checks["named_external_Hurst_theorem_and_strict_rational_weakening"]=True
    batch=read(source/"candidate_batch.json");ps={p["id"]:p for p in batch["ablation_programs"]+batch["programs"]};expected={}
    for c in batch["candidates"]:
        e=gate(ps[c["program_id"]],c)
        if e is None:continue
        expected[c["id"]]=e;cert=audit["certificates"][c["id"]];S,B,lam,K,maximum=e
        assert list(map(Q,[cert["coefficient_sum"],cert["normalizer_sum"],cert["inverse_real_pole"],cert["inverse_asymptotic_norm_constant"],cert["implied_Mertens_lim_abs_upper"]]))==[S,B,lam,K,maximum]
        assert not cert["imported_numerical_theorem_independently_reproduced"] and not cert["RH_proved"]
    assert expected.keys()==audit["certificates"].keys() and audit["complete_candidates_considered"]==len(batch["candidates"])
    archived=read(source/"archive.json")["archive"];rejected=[c["id"] for c in archived if c["id"] in expected];assert rejected==audit["archived_candidates_ruled_out"]
    checks["complete_batch_parameter_limit_and_rational_inverse_rejection_certificates"]=True
    witnesses=finite_inverse_calibration();checks["exact_Volterra_inverse_with_independent_piecewise_native_integrals"]=True
    # For the backward inverse, verify the real zeta denominator where the
    # rational cancellation is used. The all-real nonzero fact is in the proof.
    for lam in [Q(3,4),Q(3,2)]:assert real(lam).zeta().is_finite() and not real(lam).zeta().contains(0)
    checks["conditional_Mellin_cancellation_for_backward_real_inverse"]=True
    validated=read(source/"validation_data.json")["candidates"]
    for row in repairs:
        original=next(c for c in archived if c["id"]==row["rejected_candidate_id"]);c=row["candidate"]
        eligible=[v for v in validated if v["program_id"]==original["program_id"] and v["theta"]==original["theta"] and v["parameter_power"]==original["parameter_power"] and Q(v["log_power"])>0 and v["transfer"]["RH_sufficient_if_uniform"]]
        best=min(eligible,key=lambda v:(bool(v["validation"]["failures"] or v["validation"]["unresolved"]),v["log_reciprocal_cost"] if v.get("log_reciprocal_cost") is not None else 1e100,Q(v["log_power"]),v["id"]))
        assert best==c and row["program"]==ps[c["program_id"]] and gate(row["program"],c) is None
    assert len(repairs)==len(rejected)==len(final["outcomes"])
    checks["same_source_program_positive_log_repair_without_refitting"]=True
    N=cases["endpoint"];mu,_=sieve(N);M=[0]*(N+1);m=[Q(0)]*(N+1)
    for n in range(1,N+1):M[n]=M[n-1]+mu[n];m[n]=m[n-1]+Q(mu[n],n)
    assert digest(mu)==final["inverse_coefficient_sha256"] and digest(M)==final["Mertens_prefix_sha256"]
    point_count=0
    for row,outcome in zip(repairs,final["outcomes"]):
        p,c=row["program"],row["candidate"]
        if not p["degree"]:
            cc,bb=map(Q,(p["coefficients"][0],p["normalizers"][0]));values={f"2:{n}":real(cc-bb*n*m[n]+(bb-cc)*M[n]) for n in range(cases["start"],N+1)}
            assert outcome["every_integer_checked"]
        else:
            saved=final["higher_degree_tables"][p["id"]];data,_=tables(N,list(map(Q,saved)),cases["higher_degree_points"])
            for alpha,rr in saved.items():
                for x,rrr in rr.items():
                    for k,v in rrr.items():assert flint.arb(v).contains(data[alpha][x][k])
            values=observer(p,data,cases["fresh_q"],cases["higher_degree_points"])
        saved=final["program_responses"][p["id"]];assert saved.keys()==values.keys()
        for k,v in values.items():assert flint.arb(saved[k]).contains(v)
        compare_outcome(outcome,expected_outcome(p,c,values));assert not outcome["RH_proved"]
        assert outcome["complete_point_comparisons"]==len(values) and outcome["candidate_id"]==c["id"]
        point_count+=len(values)
    cut=parent["complete_coefficient_cutoff"]
    for row in spec["retained_failed_runs_are_development"]:
        old=Path(row["run_directory"])
        for name,key in [("failure.json","failure_sha256"),("protocol.json","protocol_sha256"),("final_evaluation.json","final_sha256"),("final_cases.json","cases_sha256")]:assert sha(old/name)==row[key]
        for n,h in row["frozen_source_sha256"].items():assert sha(old/"frozen_source"/n)==h
        assert not set(cases["fresh_q"])&set(row["excluded_q"]);cut=max(cut,row["cutoff"])
    assert cases["start"]==cut+1 and spec["fresh_final"]["endpoint_range"][0]<=N<=spec["fresh_final"]["endpoint_range"][1]
    assert spec["uniform_RH_sufficient_signed_controls_verified"]==final["uniform_RH_sufficient_signed_controls_verified"]==[] and not final["RH_proved"]
    checks["complete_fresh_actual_Mobius_repair_values_and_uniform_proof_separation"]=True
    with tempfile.TemporaryDirectory(prefix="mertens-limit-replay-") as tmp:
        d=Path(tmp);(d/"protocol.json").write_bytes((directory/"protocol.json").read_bytes())
        result=subprocess.run([sys.executable,str(BASE/"mertens_limit_audit.py"),"--phase","discover","--run-dir",str(d)],capture_output=True,text=True)
        assert result.returncode==0,result.stderr
        for n in seal["files"]:assert sha(d/n)==sha(directory/n)
    checks["deterministic_complete_gate_and_source_repair_replay"]=True
    result={"protocol_sha256":digest(spec),"final_sha256":sha(directory/"final_evaluation.json"),"checker_sha256":sha(BASE/"check_mertens_limits.py"),
        "all_passed":all(checks.values()),"checks":checks,"complete_candidates_checked":len(batch["candidates"]),"exact_limit_rejection_certificates":len(expected),
        "archived_candidates_ruled_out":len(rejected),"fresh_complete_point_values_checked":point_count,"native_inverse_calibration_cases":len(witnesses),"native_inverse_witnesses":witnesses,
        "published_numerical_Mertens_extremum_theorem_is_named_import":True,"imported_computation_independently_reproduced":False,
        "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    target=directory/"verification.json"
    if target.exists():raise FileExistsError("Retain original audit")
    target.write_text(json.dumps(result,indent=2)+"\n");print("Mertens limit checks:",sum(checks.values()),"/",len(checks),flush=True)


if __name__=="__main__":main()

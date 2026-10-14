#!/usr/bin/env python3
"""Direct signed-moment transfer and post-seal analytic obstruction audit."""
import argparse
from collections import Counter
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import flint

BASE=Path(__file__).resolve().parent
CODE=["signed_mellin_transfer.py","check_signed_mellin_transfer.py","signed_mellin_proof.txt"]


def read(path): return json.loads(Path(path).read_text())
def write(path,data): Path(path).write_text(json.dumps(data,indent=2)+"\n")
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def digest(data): return hashlib.sha256(json.dumps(data,sort_keys=True,separators=(",", ":"),allow_nan=False).encode()).hexdigest()
def real(x): x=Q(x); return flint.arb(x.numerator)/x.denominator


def certificate(order,beta,constant):
    if type(order) is not int or order<2 or order%2:
        raise ValueError("An even integer moment order >=2 is required")
    beta,C=Q(beta),Q(constant)
    if beta<0 or C<=0: raise ValueError("The exponent must be nonnegative and the constant positive")
    eta=(beta-1)/order
    return {"order":order,"beta":str(beta),"constant":str(C),"mellin_exponent":str(eta),
            "uniform_premise":"For every dyadic X>=1, integral_X^(2X)|R(t)|^q dt <= C X^beta",
            "holomorphic_half_plane":"Re(s)>max((beta-1)/q,0)",
            "RH_sufficient_if_uniform_and_all_height_multiplier_nonzero":bool(eta<=Q(1,2)),
            "contradicted_if_critical_zero_multiplier_nonzero":bool(eta<Q(1,2)),
            "uniform_signed_moment_premise_proved":False,"RH_proved":False}


def mellin_bound(order,beta,constant,sigma):
    cert=certificate(order,beta,constant); eta=Q(cert["mellin_exponent"]); sigma=Q(sigma)
    if sigma<=max(eta,Q(0)): raise ValueError("The test line must be inside the holomorphic half-plane")
    return real(Q(constant))**real(Q(1,order))/(1-real(2)**real(eta-sigma))


def compact_correction_bound(rows,sigma):
    sigma=Q(sigma)
    if sigma<=0: raise ValueError("A positive real part is required")
    total=flint.arb(0)
    for d,a in rows:
        if type(d) is not int or d<2: raise ValueError("An integer divisor >=2 is required")
        a=Q(a)
        integral=real(d).log() if sigma==1 else (real(d)**real(1-sigma)-1)/real(1-sigma)
        total+=real(abs(a)/d)*integral
    return total


def reciprocal_bound(rows,delta,order,beta,constant,sigma):
    delta,sigma=Q(delta),Q(sigma)
    if delta<=0 or sigma<Q(1,2): raise ValueError("A positive critical-strip multiplier lower bound is required")
    return (mellin_bound(order,beta,constant,sigma)+compact_correction_bound(rows,sigma))/real(delta)+1/real(sigma)


def source_manifest(directory):
    directory=Path(directory).resolve()
    files=("protocol.json","candidate_batch.json","validation_data.json","archive.json",
           "seal.json","final_cases.json","final_evaluation.json","verification.json")
    spec=read(directory/"protocol.json"); audit=read(directory/"verification.json"); seal=read(directory/"seal.json")
    assert audit["all_passed"] and all(audit["checks"].values())
    for name,expected in spec["code_sha256"].items(): assert sha(BASE/name)==expected
    for name,expected in seal["files"].items(): assert sha(directory/name)==expected
    return {"run_directory":str(directory),"files":{name:sha(directory/name) for name in files}}


def known_zero_rectangle(dependency):
    assert Q(dependency["centre"][0])==Q(1,2)
    assert sha(BASE/"shift-ratio-results/shift_ratio_analytic_verification.json")==dependency["verification_sha256"]
    assert sha(BASE/"shift-ratio-results/shift_ratio_analytic.json")==dependency["source_sha256"]
    centre=flint.acb(real(Q(dependency["centre"][0])),dependency["centre"][1]); radius=real(Q(dependency["radius"])/4)
    rectangle=centre+flint.acb(flint.arb(0,radius),flint.arb(0,radius))
    flint.ctx.cap=24
    first=flint.acb_series([centre,1],prec=2).zeta()[1]
    second=2*flint.acb_series([rectangle,1],prec=3).zeta()[2]
    margin=first.abs_lower()*radius-centre.zeta().abs_upper()-second.abs_upper()*radius*radius/2
    assert margin>0
    return rectangle,{"radius":str(Q(dependency["radius"])/4),"Rouche_margin":margin.str(40)}


def produce(directory,sources):
    directory=Path(directory).resolve()
    if directory.exists(): raise ValueError("A new analytic audit requires a fresh destination")
    directory.mkdir(parents=True)
    manifest={"purpose":"universal transfer and additional analytic audit; no reselection or fresh numerical validation claim",
              "code_sha256":{name:sha(BASE/name) for name in CODE},
              "sources":[source_manifest(s) for s in sources],"precision":640,
              "finite_moment_data_previously_inspected":True,"historical_priority_is_acceptance_gate":False}
    write(directory/"protocol.json",manifest); flint.ctx.prec=manifest["precision"]
    records=[]; zero_audits=[]; archived_records=[]; all_final_false=all_final_true=0
    for source in manifest["sources"]:
        path=Path(source["run_directory"]); archive=read(path/"archive.json")
        validation=read(path/"validation_data.json")["records"]
        zero,zero_audit=known_zero_rectangle(archive["known_zero_dependency"]); zero_audits.append(zero_audit)
        final=read(path/"final_evaluation.json"); final_by_id={r["program_id"]:r for r in final["records"]}
        native_cache={}
        for row in validation:
            program=row["program"]; poly="operator_certificate" in program and "polynomial" in program
            operator=program["operator_certificate"]; atoms=operator["atoms"]
            def native(d):
                if d not in native_cache: native_cache[d]=(-zero*real(d).log()).exp()
                return native_cache[d]
            F=1-sum((real(Q(a))*native(d) for d,a in atoms),flint.acb(0))
            known_nonzero=bool(F.abs_lower()>0)
            all_height=(operator["all_height_critical_multiplier_certified"] if poly else
                        operator["nonvanishing_multiplier_Re_s_ge_half_certified"])
            delta=None
            if all_height:
                if poly:
                    delta=Q(operator["selected_schur_certificate"]["uniform_multiplier_lower_bound"])
                else:
                    cost=sum((real(abs(Q(a)))/real(d).sqrt() for d,a in atoms),flint.arb(0))
                    delta=Q(str((1-cost).lower().fmpq()))
                assert delta>0
            estimates=[]
            for old in row["estimates"]:
                q,beta,C=old["order"],Q(old["beta"]),Q(old["constant"])
                cert=certificate(q,beta,C); eta=Q(cert["mellin_exponent"])
                impossible=known_nonzero and eta<Q(1,2)
                if impossible: status="uniform_estimate_ruled_out_by_actual_zeta_zero"
                elif not all_height: status="numerical_lead_missing_global_multiplier_and_uniform_moment_proof"
                else: status="numerical_lead_missing_uniform_signed_moment_proof"
                result={"certificate":cert,"status":status,"global_multiplier_lower_bound":str(delta) if delta is not None else None}
                if all_height and not impossible:
                    sigma=max(Q(3,4),eta+Q(1,16))
                    bound=reciprocal_bound(atoms,delta,q,beta,C,sigma)
                    result.update({"reciprocal_test_line":str(sigma),"conditional_reciprocal_bound_ball":bound.str(40)})
                if program["id"] in final_by_id:
                    observed=final_by_id[program["id"]]
                    outcomes=observed["outcomes"] if poly else observed["estimate_outcomes"]
                    old_out=next(o for o in outcomes if o["order"]==q)
                    passed=old_out["finite_windows_passed"] if poly else old_out["finite_validation_passed"]
                    result["original_final_windows_passed"]=passed
                    if impossible: all_final_false+=int(passed)
                    elif passed: all_final_true+=1
                estimates.append(result)
            result={"source_run":str(path),"program_id":program["id"],"program":program,
                    "critical_zero_multiplier_nonzero":known_nonzero,"multiplier_lower_ball_on_zero_disk":F.abs_lower().str(40),
                    "all_height_multiplier_nonzero":all_height,"estimates":estimates}
            records.append(result)
            if program["id"] in final_by_id: archived_records.append(result)
    archive_order=[(s["run_directory"],r["program"]["id"]) for s in manifest["sources"]
                   for r in read(Path(s["run_directory"])/"archive.json")["archive"]]
    archived_records.sort(key=lambda r:archive_order.index((r["source_run"],r["program_id"])))
    statuses=Counter(e["status"] for r in records for e in r["estimates"])
    output={"protocol_sha256":digest(manifest),"records":records,"archived_records":archived_records,
            "zero_audits":zero_audits,"statuses":dict(statuses),
            "archived_estimates_passing_finite_windows_but_globally_ruled_out":all_final_false,
            "archived_estimates_passing_finite_windows_without_this_obstruction":all_final_true,
            "no_candidate_reselection":True,"no_fresh_finite_validation_claim":True,
            "uniform_sublinear_signed_controls_verified":[],"RH_proved":False}
    write(directory/"transfer_audit.json",output)
    subprocess.run([sys.executable,str(BASE/"check_signed_mellin_transfer.py"),"--run-dir",str(directory)],check=True,cwd=BASE)
    publish(directory)


def summary(directory):
    directory=Path(directory).resolve(); spec=read(directory/"protocol.json"); audit=read(directory/"verification.json")
    data=read(directory/"transfer_audit.json")
    for name,expected in spec["code_sha256"].items(): assert sha(BASE/name)==expected
    for source in spec["sources"]:
        for name,expected in source["files"].items(): assert sha(Path(source["run_directory"])/name)==expected
    assert audit["all_passed"] and all(audit["checks"].values())
    assert audit["source_sha256"]==sha(directory/"transfer_audit.json") and data["protocol_sha256"]==digest(spec)
    survivors=[{"source_run":r["source_run"],"program_id":r["program_id"],"program":r["program"],"estimate":e}
               for r in data["archived_records"] for e in r["estimates"]
               if e["status"]=="numerical_lead_missing_uniform_signed_moment_proof"]
    return {"status":"independently_verified_direct_signed_moment_transfer_audit","run_directory":str(directory),
            "programs_audited":len(data["records"]),"estimates_audited":sum(len(r["estimates"]) for r in data["records"]),
            "statuses":data["statuses"],"checks":audit["checks"],
            "finite_passes_globally_ruled_out":data["archived_estimates_passing_finite_windows_but_globally_ruled_out"],
            "finite_passes_without_this_obstruction":data["archived_estimates_passing_finite_windows_without_this_obstruction"],
            "surviving_archived_uniform_proof_obligations":survivors,
            "RH_sufficient_single_moment_premise":"For some fixed q>=2, certify A_q(X)<=C X^(q/2+1) at every dyadic scale, preserving every ordinary-zero pole",
            "historical_priority_is_acceptance_gate":False,"no_reselection_or_new_held_out_claim":True,
            "uniform_sublinear_signed_controls_verified":[],"RH_proved":False,
            "verification_sha256":sha(directory/"verification.json")}


def publish(directory):
    directory=Path(directory).resolve(); result=summary(directory); write(directory/"summary.json",result)
    lines=["DIRECT SIGNED MOMENTS TO RH: STRONGER UNIVERSAL AUDIT","",
           "The direct Mellin exponent is eta=(beta-1)/q, avoiding pointwise-conversion loss.",
           "A single fixed-order all-scale bound beta=q/2+1 would suffice for RH if the multiplier is nonzero throughout Re(s)>=1/2.",
           "A critical-line zero rules out beta<q/2+1 whenever its multiplier is nonzero.","",
           f"Programs audited: {result['programs_audited']}; moment estimates audited: {result['estimates_audited']}.",
           f"Independent checks: {sum(result['checks'].values())}/{len(result['checks'])}.",
           f"Finite-window passes nevertheless globally ruled out: {result['finite_passes_globally_ruled_out']}.",
           f"Finite-window passes without this obstruction: {result['finite_passes_without_this_obstruction']}.",
           json.dumps(result["statuses"],indent=2),"",
           "The archived obligations surviving this pole obstruction:"]
    for row in result["surviving_archived_uniform_proof_obligations"]:
        p=row["program"]; e=row["estimate"]; cert=e["certificate"]
        lines.append(f"{p['family']} {p.get('polynomial',p.get('atoms'))}: q={cert['order']}, beta={cert['beta']}, eta={cert['mellin_exponent']}, C={cert['constant']}, finite-pass={e.get('original_final_windows_passed')}")
    lines.extend(["","The data and final evaluations were already inspected. This is a universal analytic audit, with no reselection and no new held-out claim.",
                  "Uniform signed arithmetic moment premises remain unproved. RH remains unproved.",
                  "Proof: signed_mellin_proof.txt. Full provenance: protocol.json and verification.json."])
    (directory/"report.txt").write_text("\n".join(lines)+"\n")
    path=BASE/"signed-mellin-results/latest.json"; path.parent.mkdir(exist_ok=True)
    write(path,{"run_directory":str(directory),"summary_sha256":digest(result)})


def load_latest():
    path=BASE/"signed-mellin-results/latest.json"
    if not path.exists(): return {"status":"not_run","uniform_sublinear_signed_controls_verified":[],"RH_proved":False}
    pointer=read(path); result=summary(pointer["run_directory"]); assert digest(result)==pointer["summary_sha256"]
    return result


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--run-dir",type=Path,required=True)
    parser.add_argument("--source-run",type=Path,action="append",required=True); args=parser.parse_args()
    produce(args.run_dir,args.source_run)

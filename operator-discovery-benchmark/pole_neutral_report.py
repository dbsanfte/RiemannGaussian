"""Strict report of coefficient-root arithmetic and its uniform proof gaps."""
from collections import Counter
import json
from pathlib import Path
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    directory=Path(directory).resolve();spec=read(directory/"protocol.json");seal=read(directory/"seal.json");audit=read(directory/"verification.json")
    arc=read(directory/"archive.json");final=read(directory/"final_evaluation.json");validation=read(directory/"validation_data.json")
    assert audit["all_passed"] and all(audit["checks"].values()) and audit["protocol_sha256"]==digest(spec)
    assert audit["source_final_sha256"]==sha(directory/"final_evaluation.json") and audit["checker_sha256"]==sha(BASE/"check_pole_neutral.py")
    for n,h in spec["code_sha256"].items():assert sha(BASE/n)==h
    for n,h in seal["files"].items():assert sha(directory/n)==h
    assert final["seal_sha256"]==digest(seal) and final["cases_sha256"]==digest(read(directory/"final_cases.json"))
    source=Path(spec["source_run"]);branch=Path(spec["branch_run"])
    assert sha(source/"archive.json")==spec["source_archive_sha256"] and sha(source/"verification.json")==spec["source_verification_sha256"]
    assert sha(branch/"branch_audit.json")==spec["branch_audit_sha256"] and sha(branch/"verification.json")==spec["branch_verification_sha256"]
    survivors=[];finite_but_false=0
    ps={p["id"]:p for p in read(directory/"candidate_batch.json")["programs"]}
    for c,o in zip(arc["archive"],final["outcomes"]):
        assert c["id"]==o["candidate_id"]
        if c["analytic_status"]=="RH_sufficient_signed_obligation_missing_uniform_proof" and o["finite_points_passed"]:survivors.append({"program":ps[c["program_id"]],"candidate":c})
        if c["analytic_status"].startswith("uniform_claim_ruled_out") and o["finite_points_passed"]:finite_but_false+=1
    return {"status":"independently_verified_pole_neutral_fractional_coefficient_search","run_directory":str(directory),"checks":audit["checks"],
        "programs":len(ps),"estimates":len(validation["candidates"]),"archived":len(arc["archive"]),
        "statuses":dict(Counter(c["analytic_status"] for c in validation["candidates"])),
        "complete_signed_values_checked":audit["complete_signed_values_checked"],"complete_control_values_checked":audit["complete_control_values_checked"],
        "exact_coefficients_checked":audit["exact_coefficients_checked"],"native_Mellin_checks":audit["native_Mellin_checks"],"kernel_quadrature_checks":audit["kernel_quadrature_checks"],
        "complete_coefficient_cutoff":audit["coefficient_cutoff"],"finite_archived_passes":sum(o["finite_points_passed"] for o in final["outcomes"]),
        "finite_passes_nevertheless_globally_contradicted":finite_but_false,
        "RH_sufficient_obligations_passing_fresh_points":len(survivors),"surviving_uniform_proof_obligations":survivors,
        "operators_are_pointwise_roots_of_M":False,"global_signed_pointwise_premises_proved":[],
        "uniform_RH_sufficient_signed_controls_verified":[],"historical_priority_is_acceptance_gate":False,"RH_proved":False,
        "verification_sha256":sha(directory/"verification.json")}


def publish(directory):
    directory=Path(directory);r=summary(directory);(directory/"summary.json").write_text(json.dumps(r,indent=2)+"\n")
    lines=["ACTUAL FRACTIONAL COEFFICIENT SUMS WITH POLE-AWARE LOGARITHMIC KERNELS","",
        "Coefficient powers, kernel powers and shifts are generated independently. Actual nu_a coefficients retain arithmetic signs.",
        "The Mellin transform is zeta(s)^(-a)*(s-kappa)^(-b)/s. Matching a=b,kappa=1 repairs the pole locally.",
        "Every ordinary zero multiplicity survives the negative coefficient power. The inverse exponent 1/a and height cost are charged.",
        "The integer-to-real bound and global zero implication are universal conditional arguments; their signed integer premise is unproved.","",
        f"Programs: {r['programs']}; learned estimates: {r['estimates']}; archived: {r['archived']}.",
        f"Independent checks: {sum(r['checks'].values())}/{len(r['checks'])}.",
        f"Complete signed values checked: {r['complete_signed_values_checked']}; exact coefficients checked: {r['exact_coefficients_checked']}.",
        f"Native Mellin checks with proved tails: {r['native_Mellin_checks']}; auxiliary kernel quadratures: {r['kernel_quadrature_checks']}.",
        f"Fresh finite archive passes: {r['finite_archived_passes']}/{r['archived']}.",
        f"RH-sufficient obligations passing fresh points: {r['RH_sufficient_obligations_passing_fresh_points']}.",
        f"Finite passes nevertheless globally contradicted: {r['finite_passes_nevertheless_globally_contradicted']}.",json.dumps(r["statuses"],indent=2),"",
        "Surviving uniform RH proof obligations:"]
    for row in r["surviving_uniform_proof_obligations"]:
        p,c=row["program"],row["candidate"];lines.append(f"a={p['a']}, b={p['b']}, kappa={p['kappa']}; |G(n)-{c['offset']}|<={c['constant']}*n^{c['theta']} for EVERY integer n>=1")
    lines.extend(["","Complete point sums are not complete window moments; no such claim is made.",
        "No global signed arithmetic premise has been proved in this stage. RH remains unproved.",
        "Proof: pole_neutral_proof.txt. Frozen source protocol and independent audit are retained in this directory."])
    (directory/"report.txt").write_text("\n".join(lines)+"\n")
    pointer=BASE/"pole-neutral-results/latest.json";pointer.parent.mkdir(exist_ok=True)
    pointer.write_text(json.dumps({"run_directory":str(directory.resolve()),"summary_sha256":digest(r)},indent=2)+"\n")
    print("Published fractional coefficient search; uniform signed premises remain open",flush=True)


def load_latest():
    p=BASE/"pole-neutral-results/latest.json"
    if not p.exists():return {"status":"not_run","uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    pointer=read(p);r=summary(pointer["run_directory"]);assert digest(r)==pointer["summary_sha256"];return r

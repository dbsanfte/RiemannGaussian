"""Later small-order obstructions supersede original finite plausibility."""
from pathlib import Path
import json
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    directory=Path(directory).resolve();spec,seal,gate,repairs,final,checked,cases=(read(directory/n) for n in
        ["protocol.json","seal.json","compatibility.json","repairs.json","final_evaluation.json","verification.json","final_cases.json"])
    for n,h in spec["code_sha256"].items():assert sha(BASE/n)==h
    for n in spec["this_stage_source_files"]:assert sha(directory/"frozen_source"/n)==spec["code_sha256"][n]
    assert checked["all_passed"] and all(checked["checks"].values()) and checked["protocol_sha256"]==digest(spec)
    assert checked["checker_sha256"]==sha(BASE/"check_mertens_limits.py") and checked["final_sha256"]==sha(directory/"final_evaluation.json")
    for n,h in seal["files"].items():assert sha(directory/n)==h
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"] and not seal["final_cases_exist_at_seal"]
    assert cases["created_after_selection_closed"] and cases["seal_sha256"]==final["seal_sha256"]==digest(seal) and final["cases_sha256"]==digest(cases)
    source=Path(spec["source_run"])
    for n,h in spec["source_sha256"].items():assert sha(source/n)==h
    from fractional_remainder_report import summary as source_summary
    parent=source_summary(source);rejected=set(gate["archived_candidates_ruled_out"])
    retained=[r for r in parent["surviving_uniform_proof_obligations"] if r["candidate"]["id"] not in rejected]
    false=[r for r in parent["archive_results"] if r["candidate"]["id"] in rejected and r["final_outcome"]["finite_points_passed"]]
    dep=spec["named_external_dependency"];assert sha(dep["path"])==dep["sha256"] and dep["imported_not_independently_reproduced"]
    repaired=[]
    for row,outcome in zip(repairs["repairs"],final["outcomes"]):
        assert row["candidate"]["id"]==outcome["candidate_id"]
        if outcome["finite_points_passed"]:repaired.append(dict(row,final_outcome=outcome))
    assert checked["uniform_RH_sufficient_signed_controls_verified"]==final["uniform_RH_sufficient_signed_controls_verified"]==[] and not final["RH_proved"]
    return {"status":"independently_checked_small_order_inverse_with_named_Mertens_extremum_import","run_directory":str(directory),"source_run":str(source),"checks":checked["checks"],
        "complete_candidates_checked":checked["complete_candidates_checked"],"exact_limit_rejection_certificates":checked["exact_limit_rejection_certificates"],
        "archived_candidates_ruled_out":len(rejected),"globally_false_original_finite_survivors":len(false),"known_false_original_finite_survivors":false,
        "original_RH_compatible_survivors_after_new_gate":len(retained),"retained_original_proof_obligations":retained,
        "repairs_selected":len(repairs["repairs"]),"positive_log_repairs_passing_fresh_points":len(repaired),"repaired_uniform_proof_obligations":repaired,
        "fresh_integer_interval":[cases["start"],cases["endpoint"]],"fresh_complete_point_values_checked":checked["fresh_complete_point_values_checked"],
        "complete_coefficient_cutoff":final["complete_coefficient_cutoff"],"named_external_dependency":dep,"published_numerical_extremum_theorem_is_named_import":True,
        "imported_computation_independently_reproduced":False,"derived_limit_and_Volterra_inverse_independently_checked":True,
        "source_outcomes_modified":False,"source_final_is_development":True,"historical_priority_is_acceptance_gate":False,
        "analytic_proof_is_machine_formalized":False,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False,"verification_sha256":sha(directory/"verification.json")}


def publish(directory):
    directory=Path(directory).resolve();r=summary(directory);(directory/"summary.json").write_text(json.dumps(r,indent=2)+"\n")
    lines=["SMALL-ORDER INVERSE COMPATIBILITY AND SOURCE-BATCH LOG REPAIRS","",
        "A common pure square-root fractional-family bound implies a bound on its exact small-order limit.",
        "A generic Volterra/Mellin inverse charges the cost of recovering M(x).",
        "If the resulting normalized constant is <=7/4, Hurst's named published Mertens extremum theorem rules it out.",
        "The published 14,400-zero numerical computation has not been independently reproduced here.",
        "The rational limit and inverse consequences are derived and checked independently.","",
        f"Source candidates considered: {r['complete_candidates_checked']}; exact limit certificates: {r['exact_limit_rejection_certificates']}.",
        f"Originally successful archived bounds rejected: {r['globally_false_original_finite_survivors']}.",
        f"Original conditional RH-family survivors remaining: {r['original_RH_compatible_survivors_after_new_gate']}.",
        "The original sixteen-check search results and their finite outcomes remain unchanged.",
        f"Positive-log repairs selected from the already-frozen source batch: {r['repairs_selected']}; fresh finite passes: {r['positive_log_repairs_passing_fresh_points']}.",
        f"Fresh integer interval: {r['fresh_integer_interval']}; complete independent point values: {r['fresh_complete_point_values_checked']}.",
        f"Independent checks: {sum(r['checks'].values())}/{len(r['checks'])}.","","Unproved repaired bounds:"]
    for row in r["repaired_uniform_proof_obligations"]:
        p,c=row["program"],row["candidate"];lines.append(f"c={p['coefficients']}; b={p['normalizers']}; |V_a(n)|<={c['constant']}*a^({c['parameter_power']})*n^({c['theta']})*log(e+n)^({c['log_power']}); every n and q required, except the degree-zero expression is independent of q.")
    lines.extend(["","Named dependency: https://arxiv.org/pdf/1610.08551v2, Theorem 6.1; proof import is explicit.",
        "No repaired signed uniform estimate has been proved. RH remains open in this project.","Proof: mertens_limit_proof.txt."])
    (directory/"report.txt").write_text("\n".join(lines)+"\n")
    (BASE/"mertens-limit-results/latest.json").write_text(json.dumps({"run_directory":str(directory),"summary_sha256":digest(r)},indent=2)+"\n")
    print("Published limit gate and positive-log repairs; RH uniform proofs remain open",flush=True)


def load_latest():
    p=BASE/"mertens-limit-results/latest.json"
    if not p.exists():return {"status":"not_run","uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    record=read(p);r=summary(record["run_directory"]);assert digest(r)==record["summary_sha256"]
    return r

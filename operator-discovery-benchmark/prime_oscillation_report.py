"""Imported oscillation obstructions supersede finite plausibility counts."""
from pathlib import Path
import json
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    directory=Path(directory).resolve()
    spec,seal,audit,gate,repairs,final=(read(directory/n) for n in ("protocol.json","seal.json","verification.json","compatibility.json","repairs.json","final_evaluation.json"))
    for name,h in spec["code_sha256"].items():assert sha(BASE/name)==h
    for name in spec["this_stage_source_files"]:assert sha(directory/"frozen_source"/name)==spec["code_sha256"][name]
    dep=spec["oscillation_dependency"];assert sha(dep["path"])==dep["sha256"]
    source=Path(spec["source_run"])
    for name,h in spec["source_sha256"].items():assert sha(source/name)==h
    from prime_twist_report import summary as parent_summary
    parent=parent_summary(source)
    if spec["source_coverage"]:
        from prime_twist_coverage_report import summary as coverage_summary
        coverage=coverage_summary(spec["source_coverage"]["run_directory"])
        assert coverage["verification_sha256"]==spec["source_coverage"]["verification_sha256"] and Path(coverage["source_run"])==source
    assert audit["all_passed"] and all(audit["checks"].values()) and audit["protocol_sha256"]==digest(spec)
    assert audit["final_sha256"]==sha(directory/"final_evaluation.json") and audit["checker_sha256"]==sha(BASE/"check_prime_oscillation.py")
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"] and not seal["final_cases_exist_at_seal"]
    for name,h in seal["files"].items():assert sha(directory/name)==h
    cases=read(directory/"final_cases.json");assert final["seal_sha256"]==digest(seal) and final["cases_sha256"]==digest(cases)
    assert cases["created_after_selection_closed"] and repairs["selection_closed"] and not repairs["final_data_used"]
    rejected=set(gate["archived_candidates_ruled_out"])
    survivors=[r for r in parent["surviving_uniform_proof_obligations"] if r["candidate"]["id"] not in rejected]
    false_finite=[r for r in parent["archive_results"] if r["candidate"]["id"] in rejected and r["final_outcome"]["finite_points_passed"]]
    assert len(repairs["repairs"])==len(final["outcomes"])
    repaired=[]
    for row,o in zip(repairs["repairs"],final["outcomes"]):
        assert row["candidate"]["id"]==o["candidate_id"] and not o["uniform_signed_premise_proved"]
        if o["finite_interval_passed"]:repaired.append(dict(row,final_outcome=o))
    assert dep["proof_imported_not_independently_reproved"] and not dep["machine_formalized"]
    assert audit["uniform_RH_sufficient_signed_controls_verified"]==final["uniform_RH_sufficient_signed_controls_verified"]==[] and not final["RH_proved"]
    return {"status":"independently_checked_Stieltjes_inversion_with_named_oscillation_import",
        "run_directory":str(directory),"source_run":str(source),"checks":audit["checks"],
        "complete_candidates_checked":audit["complete_candidates_checked"],"oscillation_certificates_checked":audit["oscillation_certificates_checked"],
        "distinct_eventual_inverse_programs_checked":audit["distinct_eventual_inverse_programs_checked"],
        "archived_candidates_ruled_out":len(rejected),"globally_false_original_finite_survivors":len(false_finite),
        "original_RH_compatible_survivors_after_new_gate":len(survivors),"retained_original_proof_obligations":survivors,
        "known_false_finite_survivors":false_finite,"repairs_selected":len(repairs["repairs"]),
        "positive_log_repairs_passing_fresh_interval":len(repaired),"repaired_uniform_proof_obligations":repaired,
        "fresh_integer_interval":[cases["start"],cases["endpoint"]],"fresh_complete_point_values_checked":audit["fresh_point_values_checked"],
        "complete_coefficient_cutoff":final["coefficient_cutoff"],"source_coverage":spec["source_coverage"],
        "oscillation_dependency":dep,"oscillation_theorem_is_named_external_import":True,
        "eventual_polynomial_and_Stieltjes_inversion_independently_checked":True,
        "analytic_proof_is_machine_formalized":False,"source_outcomes_modified":False,
        "all_earlier_final_and_coverage_data_is_development":True,
        "historical_priority_is_acceptance_gate":False,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False,
        "verification_sha256":sha(directory/"verification.json")}


def publish(directory):
    directory=Path(directory).resolve();r=summary(directory)
    (directory/"summary.json").write_text(json.dumps(r,indent=2)+"\n")
    lines=["OSCILLATION COMPATIBILITY: A FALSE FINITE SUCCESS AND AUTOMATIC LOG-LOSS REPAIR","",
        "A pure critical-power log-channel estimate implies psi(x)-x=O(sqrt(x)).",
        "The named Hardy-Littlewood oscillation theorem rules this out globally.",
        "The generic rejection applies to fractional monomials and signed polynomials with compensated real poles.",
        "Weighted lambda channels and positive log powers are retained.","",
        f"Full source candidate batch checked: {r['complete_candidates_checked']}; generic certificates: {r['oscillation_certificates_checked']}.",
        f"Distinct eventual-inverse program certificates: {r['distinct_eventual_inverse_programs_checked']}.",
        f"Archived candidates rejected by the new gate: {r['archived_candidates_ruled_out']}.",
        f"Previously successful finite archived bounds now known false: {r['globally_false_original_finite_survivors']}.",
        "The earlier source archive, audit and exhaustive finite results are preserved without modification.",
        f"Original RH-compatible finite survivors remaining after this gate: {r['original_RH_compatible_survivors_after_new_gate']}.","",
        "The repair selector uses eligible positive-log candidates already present in the original batch, source validation and charged costs.",
        "The new selections were sealed before drawing fresh final cases.",
        f"Repaired candidates selected: {r['repairs_selected']}; passing the complete fresh integer interval: {r['positive_log_repairs_passing_fresh_interval']}.",
        f"Fresh interval: {r['fresh_integer_interval']}; native interval point values independently checked: {r['fresh_complete_point_values_checked']}.",
        f"Independent checks: {sum(r['checks'].values())}/{len(r['checks'])}.","",
        "Repaired uniform SIGNED proof obligations (still unproved):"]
    for row in r["repaired_uniform_proof_obligations"]:
        p,c=row["program"],row["candidate"]
        lines.append(f"channel={p['channel']}, delta={p['delta']}, c={p['coefficients']}, b={p['normalizers']}; offset={c['offset']}; |E(n)-offset|<={c['constant']}*n^({c['theta']})*log(e+n)^({c['log_power']}) for EVERY integer n>=1.")
    lines.extend(["","The oscillation theorem is a named external import. Its classical proof has not been independently re-proved.",
        "The new exact eventual-inverse certificate and Stieltjes consequence are checked independently.",
        "No RH-strength uniform signed estimate is proved. RH remains open in this project.",
        "Proof: prime_oscillation_proof.txt. The new gate supersedes earlier plausibility counts, not their finite computations."])
    (directory/"report.txt").write_text("\n".join(lines)+"\n")
    pointer=BASE/"prime-oscillation-results/latest.json";pointer.write_text(json.dumps({"run_directory":str(directory),"summary_sha256":digest(r)},indent=2)+"\n")
    print("Published oscillation gate and fresh log-loss repair; uniform proof remains missing",flush=True)


def load_latest():
    pointer=BASE/"prime-oscillation-results/latest.json"
    if not pointer.exists():return {"status":"not_run","uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    record=read(pointer);r=summary(record["run_directory"]);assert digest(r)==record["summary_sha256"]
    return r

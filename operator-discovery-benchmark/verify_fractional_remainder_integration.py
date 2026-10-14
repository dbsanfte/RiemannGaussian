"""Read-only integration audit of nineteen separately scoped result loaders."""
import hashlib
import importlib
import json
from pathlib import Path

BASE=Path(__file__).resolve().parent


def sha(name):return hashlib.sha256((BASE/name).read_bytes()).hexdigest()


def main():
    registry=json.loads((BASE/"root-results/candidate_registry.json").read_text())
    modules=["autonomous_report","compensated_shift_report","signed_control_report",
        "stable_scale_report","signed_mellin_transfer","mellin_search_report","signed_defect_report",
        "fractional_moment_report","fractional_zeta_branch_audit","signed_global_calibration",
        "pole_neutral_report","parameter_jet_report","prime_error_report","prime_discrepancy_report",
        "prime_twist_report","prime_twist_coverage_report","prime_oscillation_report","fractional_remainder_report","mertens_limit_report"]
    records=[];loaded={}
    for name in modules:
        r=importlib.import_module(name).load_latest();loaded[name]=r
        assert r["status"]!="not_run" and not r.get("RH_proved",False)
        checks=r.get("checks");flat=bool(checks) and all(type(v)is bool for v in checks.values())
        if flat:assert all(checks.values())
        records.append({"loader":name,"status":r["status"],"verification_sha256":r.get("verification_sha256"),
            "checks_passed":sum(checks.values()) if flat else None,"checks_total":len(checks) if flat else None,
            "check_counts_omitted_for_nested_or_missing_schema":not flat})
    assert len(records)==19 and registry["verified_arithmetic_consequence_count"]==20 and registry["full_coefficient_origin_native_zeta_comparison_groups"]==150
    assert (BASE/"operator_candidates.txt").read_text().splitlines()[0].startswith("TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES")
    assert not registry["uniform_RH_sufficient_signed_controls_verified"] and not registry["uniform_sublinear_signed_controls_verified"]
    assert not registry["historical_priority_is_acceptance_gate"]
    r=loaded["fractional_remainder_report"];assert registry["fractional_arithmetic_remainder_family_search"]==r
    assert r["all_height_zero_recovery_argument_checked"] and r["zero_recovery_requires_infinite_parameter_premise"]
    assert not r["fixed_fractional_order_given_all_height_nonvanishing"] and not r["finite_parameter_grid_suffices_for_positive_degree"]
    assert r["proved_all_scale_signed_parameter_cancellation"] and r["proved_signed_parameter_growth_exponent"]=="1"
    assert not r["new_prime_distribution_estimate_proved"] and not r["prime_distribution_theorem_imported"]
    assert not r["detector_autonomously_invented_backends"] and not r["analytic_proof_is_machine_formalized"]
    assert not r["actual_prime_or_factor_oracle_used_by_coefficient_producer"]
    assert r["ablation_comparison"]["equal_promotion_slot_budgets"]
    assert r["generation_family_counts"]["promoted_composition"]==r["ablation_comparison"]["admitted_promotions"]
    assert r["uniform_RH_sufficient_signed_controls_verified"]==[]
    limits=loaded["mertens_limit_report"];assert registry["small_order_inverse_Mertens_compatibility_audit"]==limits
    assert Path(limits["source_run"])==Path(r["run_directory"])
    assert limits["published_numerical_extremum_theorem_is_named_import"] and not limits["imported_computation_independently_reproduced"]
    assert limits["derived_limit_and_Volterra_inverse_independently_checked"] and not limits["source_outcomes_modified"]
    assert limits["original_RH_compatible_survivors_after_new_gate"]+limits["globally_false_original_finite_survivors"]==r["RH_sufficient_family_obligations_passing_fresh_points"]
    limit_spec=json.loads((Path(limits["run_directory"])/"protocol.json").read_text())
    directory=Path(r["run_directory"]);spec=json.loads((directory/"protocol.json").read_text());audit=json.loads((directory/"verification.json").read_text())
    assert audit["replay_sha256"] and all(audit["checks"].values())
    assert audit["native_entire_numerators_checked"]==len(json.loads((directory/"numerator_data.json").read_text())["values"])+2
    assert audit["global_signed_parameter_and_unit_certificates_checked"]==r["proved_global_family_and_unit_bound_certificates"]
    prior_paths=[BASE/"prime-twist-results/pilot-001/integration_verification.json",BASE/"prime-oscillation-results/audit-001/integration_verification.json"]
    snapshots=[p.parent/"integration_snapshot" for p in prior_paths];prior_hashes=[]
    oldkeys={"driver_sha256":"run_expanded_probe.py","registry_sha256":"root-results/candidate_registry.json","report_sha256":"root-results/report.txt",
        "documentation_sha256":"SIGNED_ARITHMETIC_CONTROL.md","integration_checker_sha256":"verify_prime_twist_integration.py"}
    for i,(path,snap) in enumerate(zip(prior_paths,snapshots)):
        old=json.loads(path.read_text());keys=dict(oldkeys)
        if i:keys["integration_checker_sha256"]="verify_prime_oscillation_integration.py"
        for key,name in keys.items():assert hashlib.sha256((snap/name).read_bytes()).hexdigest()==old[key]
        prior_hashes.append({"path":str(path),"sha256":hashlib.sha256(path.read_bytes()).hexdigest(),"exact_five_file_snapshot_preserved":True})
    observations=json.loads((directory/"plot_observations.json").read_text())
    assert observations["source_final_sha256"]==hashlib.sha256((directory/"final_evaluation.json").read_bytes()).hexdigest()
    assert observations["source_archive_sha256"]==hashlib.sha256((directory/"archive.json").read_bytes()).hexdigest()
    assert observations["all_fresh_scales_enter_each_maximum"] and observations["finite_parameter_grid_is_not_uniform_evidence"]
    assert observations["right_panel_is_conditional"] and not observations["RH_proved"]
    assert {v["exact_parameter_order"] for v in observations["observations"]}=={0,1,2,3}
    assert observations["later_limit_gate_verification_sha256"]==limits["verification_sha256"]
    excluded={row["candidate"]["id"] for row in limits["known_false_original_finite_survivors"]}
    assert set(observations["later_rejected_source_candidate_ids_excluded"])==excluded
    assert all(row["candidate_id"] not in excluded for row in observations["observations"])
    report=(BASE/"root-results/report.txt").read_text();doc=(BASE/"SIGNED_ARITHMETIC_CONTROL.md").read_text()
    assert "FRACTIONAL ARITHMETIC REMAINDERS WITH INFINITE-PARAMETER RECOVERY" in report
    assert "every integer" in doc and "finite" in doc and "growth exponent" in doc
    result={"status":"integration_verified_research_goal_still_active","objective":registry["objective"],
        "driver_sha256":sha("run_expanded_probe.py"),"registry_sha256":sha("root-results/candidate_registry.json"),
        "report_sha256":sha("root-results/report.txt"),"documentation_sha256":sha("SIGNED_ARITHMETIC_CONTROL.md"),
        "integration_checker_sha256":sha("verify_fractional_remainder_integration.py"),"strict_loaders_checked":records,
        "legacy_catalogue_scoped_counts":{"families":10,"consequences":20,"native_groups":150},"legacy_catalogue_sha256":sha("operator_candidates.txt"),
        "prior_integration_milestones_and_snapshots":prior_hashes,
        "fractional_family_scope":{"all_height_zero_bridge":True,"requires_infinite_parameter_family":True,
            "proved_signed_parameter_growth_exponent":"1","RH_uniform_signed_premise_proved":False,
            "mathematical_backends_supplied_not_autonomously_invented":True,"machine_formalized":False,
            "programs":r["programs"],"growth_hypotheses":r["growth_hypotheses"],"RH_if_uniform_finite_survivors":r["RH_sufficient_family_obligations_passing_fresh_points"]},
        "independent_native_checks":{k:v for k,v in audit.items() if type(v)is int},
        "this_stage_frozen_source_sha256":{n:sha(n) for n in spec["this_stage_source_files"]},
        "Mertens_limit_frozen_source_sha256":{n:sha(n) for n in limit_spec["this_stage_source_files"]},
        "public_contract_checks":{"cases":5,"source_sha256":sha("test_fractional_remainder_contracts.py")},
        "Mertens_limit_public_contract_checks":{"cases":4,"source_sha256":sha("test_mertens_limit_contracts.py")},
        "Mertens_limit_compatibility":{"verification_sha256":limits["verification_sha256"],
            "archived_finite_successes_rejected":limits["globally_false_original_finite_survivors"],
            "original_RH_compatible_leads_retained":limits["original_RH_compatible_survivors_after_new_gate"],
            "positive_log_repairs_passing":limits["positive_log_repairs_passing_fresh_points"],
            "fresh_point_values_checked":limits["fresh_complete_point_values_checked"],
            "named_external_dependency":limits["named_external_dependency"],
            "imported_zero_phase_computation_independently_reproduced":False},
        "standalone_evidence_plot":{"source_sha256":sha("plot_fractional_remainders.py"),
            "pdf_sha256":hashlib.sha256((directory/"fractional_remainder_evidence.pdf").read_bytes()).hexdigest(),
            "png_sha256":hashlib.sha256((directory/"fractional_remainder_evidence.png").read_bytes()).hexdigest(),
            "observations_sha256":hashlib.sha256((directory/"plot_observations.json").read_bytes()).hexdigest()},
        "failed_predecessors_preserved_with_fresh_final_cases":spec["retained_failed_runs_are_development"],
        "failed_inverse_audit_preserved_with_fresh_final_cases":limit_spec["retained_failed_runs_are_development"],
        "historical_priority_is_acceptance_gate":False,"source_producer_reruns_for_integration":False,
        "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False,
        "completion_audit":"Not achieved: the new family retains all ordinary zeros conditionally and has true signed parameter bounds at every scale. Their x-growth is one; every RH-strength infinite-family estimate still lacks a uniform signed proof."}
    destination=directory/"integration_verification.json"
    if destination.exists():raise FileExistsError("Retain the integration milestone")
    destination.write_text(json.dumps(result,indent=2)+"\n")
    print("19 scoped loaders verified; exact fifteen- and seventeen-loader snapshots retained")
    print("Fractional family and weak signed bounds integrated; RH uniform premise remains open")


if __name__=="__main__":main()

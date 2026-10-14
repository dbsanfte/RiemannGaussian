"""Verify seventeen scoped loaders without rerunning any source producer."""
from pathlib import Path
import hashlib
import importlib
import json

BASE=Path(__file__).resolve().parent


def sha(name):return hashlib.sha256((BASE/name).read_bytes()).hexdigest()


def main():
    registry=json.loads((BASE/"root-results/candidate_registry.json").read_text())
    modules=["autonomous_report","compensated_shift_report","signed_control_report",
        "stable_scale_report","signed_mellin_transfer","mellin_search_report",
        "signed_defect_report","fractional_moment_report","fractional_zeta_branch_audit",
        "signed_global_calibration","pole_neutral_report","parameter_jet_report",
        "prime_error_report","prime_discrepancy_report","prime_twist_report",
        "prime_twist_coverage_report","prime_oscillation_report"]
    records=[];loaded={}
    for name in modules:
        r=importlib.import_module(name).load_latest();loaded[name]=r
        assert r["status"]!="not_run" and not r.get("RH_proved",False)
        checks=r.get("checks");flat=bool(checks) and all(type(v)is bool for v in checks.values())
        if flat:assert all(checks.values())
        records.append({"loader":name,"status":r["status"],"run_directory":r.get("run_directory"),
            "verification_sha256":r.get("verification_sha256"),"checks_passed":sum(checks.values()) if flat else None,
            "checks_total":len(checks) if flat else None,"check_counts_omitted_for_nested_or_missing_schema":not flat})
    assert len(records)==17 and registry["verified_arithmetic_consequence_count"]==20
    assert registry["full_coefficient_origin_native_zeta_comparison_groups"]==150
    assert (BASE/"operator_candidates.txt").read_text().splitlines()[0].startswith("TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES")
    assert not registry["historical_priority_is_acceptance_gate"] and not registry["uniform_RH_sufficient_signed_controls_verified"]
    assert not registry["uniform_sublinear_signed_controls_verified"] and registry["later_analytic_obstructions_supersede_archived_plausibility_counts"]
    keys={"prime_twist_report":"fractional_prime_twist_and_signed_decay_search",
        "prime_twist_coverage_report":"exhaustive_finite_prime_twist_coverage",
        "prime_oscillation_report":"prime_oscillation_compatibility_audit"}
    for module,key in keys.items():assert registry[key]==loaded[module]
    r=loaded["prime_oscillation_report"];cv=loaded["prime_twist_coverage_report"];tw=loaded["prime_twist_report"]
    assert r["oscillation_theorem_is_named_external_import"] and not r["analytic_proof_is_machine_formalized"]
    assert r["eventual_polynomial_and_Stieltjes_inversion_independently_checked"] and not r["source_outcomes_modified"]
    assert r["all_earlier_final_and_coverage_data_is_development"]
    assert r["original_RH_compatible_survivors_after_new_gate"]+r["globally_false_original_finite_survivors"]==tw["RH_sufficient_obligations_passing_fresh_points"]
    assert r["fresh_integer_interval"][0]==cv["cutoff"]+1
    assert tw["all_scale_signed_actual_prime_harmonic_theorem_proved"] and tw["all_scale_signed_actual_prime_reciprocal_tail_theorem_proved"]
    assert not tw["signed_global_calibrations_RH_sufficient"] and tw["proved_signed_tail_ordinary_zeta_exponent_after_recovery"]=="1"
    assert not tw["imported_prime_distribution_estimate"]
    prior_path=BASE/"prime-twist-results/pilot-001/integration_verification.json";prior=json.loads(prior_path.read_text())
    assert prior["integration_checker_sha256"]==sha("verify_prime_twist_integration.py")
    snapshot=BASE/"prime-twist-results/pilot-001/integration_snapshot"
    prior_files={"driver_sha256":"run_expanded_probe.py","registry_sha256":"root-results/candidate_registry.json",
        "report_sha256":"root-results/report.txt","documentation_sha256":"SIGNED_ARITHMETIC_CONTROL.md",
        "integration_checker_sha256":"verify_prime_twist_integration.py"}
    for key,name in prior_files.items():assert hashlib.sha256((snapshot/name).read_bytes()).hexdigest()==prior[key]
    for name,h in prior["frozen_stage_source_sha256"].items():assert sha(name)==h
    directory=Path(r["run_directory"]);observations=json.loads((directory/"plot_observations.json").read_text())
    assert observations["source_final_sha256"]==hashlib.sha256((directory/"final_evaluation.json").read_bytes()).hexdigest()
    assert observations["interval"]==r["fresh_integer_interval"] and observations["every_observation_represented_in_block_maxima"]
    assert observations["old_target_globally_false_by_named_oscillation_import"] and observations["new_target_uniform_proof_missing"]
    newfields=("complete_candidates_checked","oscillation_certificates_checked","distinct_eventual_inverse_programs_checked",
        "archived_candidates_ruled_out","globally_false_original_finite_survivors","original_RH_compatible_survivors_after_new_gate",
        "repairs_selected","positive_log_repairs_passing_fresh_interval","fresh_integer_interval","fresh_complete_point_values_checked",
        "complete_coefficient_cutoff","oscillation_theorem_is_named_external_import")
    result={"status":"integration_verified_research_goal_still_active","objective":registry["objective"],
        "driver_sha256":sha("run_expanded_probe.py"),"integration_checker_sha256":sha("verify_prime_oscillation_integration.py"),
        "registry_sha256":sha("root-results/candidate_registry.json"),"report_sha256":sha("root-results/report.txt"),
        "documentation_sha256":sha("SIGNED_ARITHMETIC_CONTROL.md"),"historical_priority_is_acceptance_gate":False,
        "strict_loaders_checked":records,"legacy_catalogue_scoped_counts":{"families":10,"consequences":20,"native_groups":150},
        "legacy_catalogue_sha256":sha("operator_candidates.txt"),"oscillation_compatibility_and_repair":{k:r[k] for k in newfields},
        "exhaustive_finite_coverage":{k:cv[k] for k in ("cutoff","complete_point_comparisons","complete_window_starts","complete_moment_comparisons")},
        "signed_all_scale_calibration_scope":{"proved":True,"ordinary_zeta_exponent":"1","RH_sufficient":False,
            "prime_distribution_estimate_imported":False},
        "named_oscillation_dependency":r["oscillation_dependency"],
        "public_contract_checks":{"test_prime_twist_contracts.py":{"cases":8,"source_sha256":sha("test_prime_twist_contracts.py")},
            "test_prime_twist_coverage.py":{"cases":2,"source_sha256":sha("test_prime_twist_coverage.py")},
            "test_prime_oscillation_contracts.py":{"cases":4,"source_sha256":sha("test_prime_oscillation_contracts.py")}},
        "coverage_loader_sha256":sha("prime_twist_coverage_report.py"),
        "proof_sources":{"prime_oscillation_proof.txt":sha("prime_oscillation_proof.txt")},
        "standalone_oscillation_evidence_plot":{"code_sha256":sha("plot_prime_oscillation.py"),
            "pdf_sha256":hashlib.sha256((directory/"prime_oscillation_evidence.pdf").read_bytes()).hexdigest(),
            "png_sha256":hashlib.sha256((directory/"prime_oscillation_evidence.png").read_bytes()).hexdigest(),
            "observations_sha256":hashlib.sha256((directory/"plot_observations.json").read_bytes()).hexdigest(),
            "scope":"all fresh points included in block maxima; the false target's rejection uses a named external theorem"},
        "prior_milestone_retained_sha256":hashlib.sha256(prior_path.read_bytes()).hexdigest(),
        "prior_five_file_snapshot_retained":True,"source_producer_reruns_for_integration":False,
        "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False,
        "completion_audit":"Not achieved: actual-prime signed calibrations hold at every scale but recover exponent one. One exhaustive finite success is globally false by imported oscillation. The remaining weighted estimates and the positive-log repair still lack uniform signed proofs."}
    destination=directory/"integration_verification.json"
    if destination.exists():raise FileExistsError("Retain the integration milestone")
    destination.write_text(json.dumps(result,indent=2)+"\n")
    print("17 scoped result loaders verified; prior fifteen-loader milestone and exact snapshot retained")
    print("Oscillation gate corrects a false finite success; RH-strength uniform proofs remain open")


if __name__=="__main__":main()

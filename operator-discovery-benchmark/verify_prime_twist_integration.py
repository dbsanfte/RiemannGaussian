"""Audit the fifteen-stage integration using strict read-only result loaders."""
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
        "prime_error_report","prime_discrepancy_report","prime_twist_report"]
    records=[];latest={}
    for name in modules:
        r=importlib.import_module(name).load_latest();latest[name]=r
        assert r["status"]!="not_run" and not r.get("RH_proved",False)
        checks=r.get("checks");flat=bool(checks) and all(type(v)is bool for v in checks.values())
        if flat:assert all(checks.values())
        records.append({"loader":name,"status":r["status"],"run_directory":r.get("run_directory"),
            "verification_sha256":r.get("verification_sha256"),"checks_passed":sum(checks.values()) if flat else None,
            "checks_total":len(checks) if flat else None,"check_counts_omitted_for_nested_or_missing_schema":not flat})
    assert len(records)==15
    assert registry["verified_arithmetic_consequence_count"]==20
    assert registry["full_coefficient_origin_native_zeta_comparison_groups"]==150
    assert (BASE/"operator_candidates.txt").read_text().splitlines()[0].startswith("TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES")
    assert not registry["historical_priority_is_acceptance_gate"]
    assert not registry["uniform_RH_sufficient_signed_controls_verified"] and not registry["uniform_sublinear_signed_controls_verified"]
    assert registry["prime_density_and_signed_prime_correlation_search"]==latest["prime_discrepancy_report"]
    r=registry["fractional_prime_twist_and_signed_decay_search"]
    assert r==latest["prime_twist_report"] and all(r["checks"].values()) and len(r["checks"])==14
    assert r["negative_growth_exponents_supported"] and r["negative_growth_requires_exact_Mellin_center"]
    assert r["all_shift_recovery_costs_charged"] and r["ordinary_zero_recovery_includes_arbitrary_multiplicities"]
    assert not r["all_height_scalar_nonvanishing_gate_required"]
    assert r["all_scale_signed_actual_prime_harmonic_theorem_proved"] and r["all_scale_signed_actual_prime_reciprocal_tail_theorem_proved"]
    assert r["signed_harmonic_interval"]==["-1",r["prime_density_constant"]]
    assert r["proved_signed_tail_ordinary_zeta_exponent_after_recovery"]=="1"
    assert not r["signed_global_calibrations_RH_sufficient"] and not r["imported_prime_distribution_estimate"]
    assert not r["proof_backend_autonomously_invented_by_detector"] and not r["analytic_proof_is_machine_formalized"]
    assert r["density_matched_controls_preserve_actual_prime_power_locations"]
    assert not r["density_matched_controls_preserve_original_prime_power_weights"]
    assert r["density_matched_controls_preserve_same_global_density_and_diagonal_bounds"]
    assert r["density_matched_controls_all_RH_strength_uniform_claims_ruled_out"]
    assert not r["uniform_RH_sufficient_signed_controls_verified"] and not r["RH_proved"]
    directory=Path(r["run_directory"])
    prior_path=BASE/"prime-discrepancy-results/pilot-001/integration_verification.json"
    prior=json.loads(prior_path.read_text())
    assert prior["integration_checker_sha256"]==sha("verify_prime_discrepancy_integration.py")
    for n,h in prior["proof_sources"].items():assert sha(n)==h
    assert prior["standalone_evidence_plot"]["code_sha256"]==sha("plot_prime_discrepancy.py")
    spec=json.loads((directory/"protocol.json").read_text())
    fields=("programs","estimates","archived","complete_coefficient_cutoff","exact_coefficients_checked",
        "complete_point_values_checked","generic_signed_response_values_checked","native_kernel_integrals_checked",
        "native_shift_log_checks","fractional_root_identity_cases","signed_fractional_tail_cases_checked",
        "all_scale_signed_actual_prime_harmonic_theorem_proved","all_scale_signed_actual_prime_reciprocal_tail_theorem_proved",
        "proved_signed_tail_ordinary_zeta_exponent_after_recovery","RH_sufficient_obligations_passing_fresh_points",
        "negative_decay_RH_sufficient_obligations_passing_fresh_points","complete_density_matched_control_windows_checked",
        "finite_density_matched_control_bound_passes")
    result={"status":"integration_verified_research_goal_still_active","objective":registry["objective"],
        "historical_priority_is_acceptance_gate":False,"driver_sha256":sha("run_expanded_probe.py"),
        "integration_checker_sha256":sha("verify_prime_twist_integration.py"),
        "registry_sha256":sha("root-results/candidate_registry.json"),"report_sha256":sha("root-results/report.txt"),
        "documentation_sha256":sha("SIGNED_ARITHMETIC_CONTROL.md"),
        "legacy_catalogue_scoped_counts":{"families":10,"consequences":20,"native_groups":150},
        "legacy_catalogue_sha256":sha("operator_candidates.txt"),"strict_loaders_checked":records,
        "fractional_prime_twist_stage":{k:r[k] for k in fields},
        "public_contract_checks":{"test_prime_twist_contracts.py":{"cases":8,"source_sha256":sha("test_prime_twist_contracts.py")}},
        "frozen_stage_source_sha256":{n:spec["code_sha256"][n] for n in spec["this_stage_source_files"]},
        "standalone_evidence_plot":{"code_sha256":sha("plot_prime_twists.py"),
            "pdf_sha256":hashlib.sha256((directory/"prime_twist_evidence.pdf").read_bytes()).hexdigest(),
            "png_sha256":hashlib.sha256((directory/"prime_twist_evidence.png").read_bytes()).hexdigest(),
            "scope":"finite point errors and complete control windows; learned decay curve is not a uniform theorem"},
        "fresh_evaluation_scope":{"fresh_points_and_windows_drawn_after_sealing":True,
            "large_window_start_lower_bound":spec["final_cases"]["large_range"][0],
            "prior_final_coefficient_cutoff":latest["prime_discrepancy_report"]["complete_coefficient_cutoff"],
            "unrelated_signed_inputs_generated_after_sealing":True,
            "cumulative_prefixes_overlap_development_data":True,"complete_disjointness_of_underlying_coefficients_claimed":False},
        "prior_milestone_retained_sha256":hashlib.sha256(prior_path.read_bytes()).hexdigest(),
        "source_producer_reruns_for_integration":False,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False,
        "completion_audit":"Not achieved: actual-prime harmonic and reciprocal-tail signed bounds are proved at every scale, but recover ordinary zeta only at exponent one. Stronger fractional decay and signed pair estimates remain finite leads with unproved uniform premises."}
    destination=directory/"integration_verification.json"
    if destination.exists():raise FileExistsError("Retain the existing integration milestone")
    destination.write_text(json.dumps(result,indent=2)+"\n")
    print("15 strict stages integrated; core 10 families / 20 consequences / 150 native groups retained")
    print("Signed all-scale prime calibrations verified; RH-strength uniform estimates remain open")


if __name__=="__main__":main()

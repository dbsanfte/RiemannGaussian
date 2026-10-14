"""Verify the prime-density/correlation integration without rerunning producers."""
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
        "prime_error_report","prime_discrepancy_report"]
    records=[]
    for name in modules:
        r=importlib.import_module(name).load_latest()
        assert r["status"]!="not_run" and not r.get("RH_proved",False)
        checks=r.get("checks");flat=bool(checks) and all(type(v)is bool for v in checks.values())
        if flat:assert all(checks.values())
        records.append({"loader":name,"status":r["status"],"run_directory":r.get("run_directory"),
            "verification_sha256":r.get("verification_sha256"),"checks_passed":sum(checks.values()) if flat else None,
            "checks_total":len(checks) if flat else None,"check_counts_omitted_for_nested_or_missing_schema":not flat})
    assert len(records)==14
    assert registry["verified_arithmetic_consequence_count"]==20
    assert registry["full_coefficient_origin_native_zeta_comparison_groups"]==150
    assert (BASE/"operator_candidates.txt").read_text().splitlines()[0].startswith("TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES")
    assert not registry["historical_priority_is_acceptance_gate"]
    assert not registry["uniform_RH_sufficient_signed_controls_verified"] and not registry["uniform_sublinear_signed_controls_verified"]
    r=registry["prime_density_and_signed_prime_correlation_search"]
    assert r["programs"]==228 and r["estimates"]==32357 and r["archived"]==24
    assert r["carry_proposals"]==16807 and r["universal_floor_certificates"]==16
    assert r["all_scale_prime_density_bound_proved"] and not r["all_scale_prime_density_bound_is_signed"]
    assert r["all_scale_diagonal_bound_proved"] and not r["imported_prime_distribution_estimate"]
    assert r["selected_prime_density_certificate"]["density"]["constant"]=="359/128"
    assert r["complete_coefficient_cutoff"]==16384
    assert r["finite_archived_passes"]==22 and r["RH_sufficient_obligations_passing_fresh_windows"]==19
    assert r["finite_passes_nevertheless_globally_ruled_out"]==0
    assert not r["support_controls_are_actual_prime_density_inputs"]
    assert not r["input_programs_selected_by_prior_final_outcomes"]
    assert not r["analytic_proof_is_machine_formalized"] and not r["uniform_signed_correlation_premise_proved"]
    prior=json.loads((BASE/"prime-error-results/pilot-001/integration_verification.json").read_text())
    assert prior["integration_checker_sha256"]==sha("verify_prime_error_integration.py")
    result={"status":"integration_verified_research_goal_still_active","objective":registry["objective"],
        "historical_priority_is_acceptance_gate":False,"driver_sha256":sha("run_expanded_probe.py"),
        "integration_checker_sha256":sha("verify_prime_discrepancy_integration.py"),
        "registry_sha256":sha("root-results/candidate_registry.json"),"report_sha256":sha("root-results/report.txt"),
        "documentation_sha256":sha("SIGNED_ARITHMETIC_CONTROL.md"),
        "legacy_catalogue_scoped_counts":{"families":10,"consequences":20,"native_groups":150},
        "legacy_catalogue_sha256":sha("operator_candidates.txt"),"strict_loaders_checked":records,
        "prime_density_correlation_stage":{k:r[k] for k in ("programs","estimates","archived","carry_proposals",
            "universal_floor_certificates","full_period_cells_checked","exact_coefficients_checked",
            "complete_actual_windows_checked","complete_support_control_windows_checked","complete_coefficient_cutoff",
            "polynomial_integration_cells_checked","independent_ramp_Gram_entries_checked",
            "all_scale_prime_density_bound_proved","all_scale_prime_density_bound_is_signed","all_scale_diagonal_bound_proved",
            "imported_prime_distribution_estimate","RH_sufficient_obligations_passing_fresh_windows")},
        "public_contract_checks":{"test_prime_discrepancy_contracts.py":{"cases":7,"source_sha256":sha("test_prime_discrepancy_contracts.py")}},
        "proof_sources":{"prime_discrepancy_proof.txt":sha("prime_discrepancy_proof.txt")},
        "standalone_evidence_plot":{"code_sha256":sha("plot_prime_discrepancy.py"),
            "pdf_sha256":sha("prime-discrepancy-results/pilot-001/prime_discrepancy_evidence.pdf"),
            "png_sha256":sha("prime-discrepancy-results/pilot-001/prime_discrepancy_evidence.png"),
            "scope":"finite complete-window observations; no extrapolated proof"},
        "fresh_evaluation_scope":{"fresh_window_starts_drawn_after_sealing":True,
            "development_prime_density_prefix":8192,"some_final_coefficients_overlap_development_proof_patch":True,
            "complete_disjointness_of_underlying_arithmetic_coefficients_claimed":False},
        "prior_milestone_retained_sha256":sha("prime-error-results/pilot-001/integration_verification.json"),
        "source_producer_reruns_for_integration":False,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False,
        "completion_audit":"Not achieved: the discovered floor certificates prove unsigned actual-prime density and diagonal control at every scale. The signed off-diagonal estimates are finite leads; all RH-strength uniform pair premises remain unproved."}
    destination=BASE/"prime-discrepancy-results/pilot-001/integration_verification.json"
    if destination.exists():raise FileExistsError("Retain prior integration milestone")
    destination.write_text(json.dumps(result,indent=2)+"\n")
    print("14 strict stages integrated; core 10 families / 20 consequences / 150 native groups retained")
    print("All-scale unsigned actual-prime inputs verified; 19 finite RH-sufficient signed pair obligations remain unproved")


if __name__=="__main__":main()

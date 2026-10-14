"""Verify the signed prime-error stage without rerunning arithmetic producers."""
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
             "signed_global_calibration","pole_neutral_report","parameter_jet_report","prime_error_report"]
    records=[]
    for name in modules:
        r=importlib.import_module(name).load_latest()
        assert r["status"]!="not_run" and not r.get("RH_proved",False)
        checks=r.get("checks")
        flat=bool(checks) and all(type(v)is bool for v in checks.values())
        if flat:assert all(checks.values())
        records.append({"loader":name,"status":r["status"],"run_directory":r.get("run_directory"),
                        "verification_sha256":r.get("verification_sha256"),
                        "checks_passed":sum(checks.values()) if flat else None,
                        "checks_total":len(checks) if flat else None,
                        "check_counts_omitted_for_nested_or_missing_schema":not flat})
    assert len(records)==13
    assert registry["verified_arithmetic_consequence_count"]==20
    assert registry["full_coefficient_origin_native_zeta_comparison_groups"]==150
    assert (BASE/"operator_candidates.txt").read_text().splitlines()[0].startswith("TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES")
    assert not registry["historical_priority_is_acceptance_gate"]
    assert not registry["uniform_RH_sufficient_signed_controls_verified"]
    assert not registry["uniform_sublinear_signed_controls_verified"]
    r=registry["signed_prime_error_filter_search"]
    assert not r["all_height_multiplier_nonvanishing_required"]
    assert r["isolated_multiplier_zeros_preserve_every_ordinary_zero_multiplicity"]
    assert r["whole_unit_integer_to_real_transfer_proved"]
    assert not r["analytic_proof_is_machine_formalized"]
    assert r["programs"]==228 and r["estimates"]==28691 and r["archived"]==12
    assert r["complete_coefficient_cutoff"]==30104
    assert r["RH_sufficient_obligations_passing_fresh_points"]==10
    assert r["surviving_filters_failing_old_gate_by_zero_at_one"]==3
    assert r["finite_passes_nevertheless_globally_ruled_out"]==0
    assert r["finite_support_control_passes_nevertheless_globally_ruled_out"]==0
    assert registry["imported_all_scale_signed_calibration"]["imported_dependency"]["analytic_source_proof_independently_reproved"] is False
    prior=json.loads((BASE/"parameter-jet-results/calibration-001/integration_verification.json").read_text())
    assert prior["integration_checker_sha256"]==sha("verify_signed_extensions_integration.py")
    result={"status":"integration_verified_research_goal_still_active",
        "objective":registry["objective"],"historical_priority_is_acceptance_gate":False,
        "driver_sha256":sha("run_expanded_probe.py"),"integration_checker_sha256":sha("verify_prime_error_integration.py"),
        "registry_sha256":sha("root-results/candidate_registry.json"),"report_sha256":sha("root-results/report.txt"),
        "documentation_sha256":sha("SIGNED_ARITHMETIC_CONTROL.md"),
        "legacy_catalogue_scoped_counts":{"families":10,"consequences":20,"native_groups":150},
        "legacy_catalogue_sha256":sha("operator_candidates.txt"),"strict_loaders_checked":records,
        "prime_error_stage":{k:r[k] for k in ("programs","estimates","archived","exact_coefficients_checked",
            "complete_signed_point_values_checked","complete_support_control_values_checked","complete_coefficient_cutoff",
            "RH_sufficient_obligations_passing_fresh_points","surviving_filters_failing_old_gate_by_zero_at_one",
            "all_height_multiplier_nonvanishing_required","whole_unit_integer_to_real_transfer_proved","quantitative_cost_scope")},
        "public_contract_checks":{"test_prime_error_contracts.py":{"cases":7,"source_sha256":sha("test_prime_error_contracts.py")}},
        "proof_sources":{"prime_error_proof.txt":sha("prime_error_proof.txt")},
        "retained_failed_preflight":{"path":"prime-error-results/native-preflight-001/failure.json",
                                    "sha256":sha("prime-error-results/native-preflight-001/failure.json"),
                                    "no_discovery_final_inputs_consumed":True},
        "prior_milestone_retained_sha256":sha("parameter-jet-results/calibration-001/integration_verification.json"),
        "source_producer_reruns_for_integration":False,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False,
        "completion_audit":"Not achieved: the broader logarithmic zero-faithfulness bridge and whole-unit increment theorem are verified conditional tools; all RH-strength signed integer growth estimates remain unproved."}
    destination=BASE/"prime-error-results/pilot-001/integration_verification.json"
    if destination.exists():raise FileExistsError("Retain prior integration milestone")
    destination.write_text(json.dumps(result,indent=2)+"\n")
    print("13 strict stages integrated; core 10 families / 20 consequences / 150 native groups retained")
    print("10 finite RH-sufficient prime-error obligations; three admit a multiplier zero at one; all uniform premises remain open")


if __name__=="__main__":main()

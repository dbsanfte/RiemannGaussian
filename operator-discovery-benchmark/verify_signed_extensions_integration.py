"""Read-only integration checks, retaining a milestone without producer reruns."""
from pathlib import Path
import hashlib
import importlib
import json

BASE = Path(__file__).resolve().parent


def sha(name):
    return hashlib.sha256((BASE/name).read_bytes()).hexdigest()


def main():
    registry = json.loads((BASE/"root-results/candidate_registry.json").read_text())
    modules = ["autonomous_report", "compensated_shift_report", "signed_control_report",
               "stable_scale_report", "signed_mellin_transfer", "mellin_search_report",
               "signed_defect_report", "fractional_moment_report", "fractional_zeta_branch_audit",
               "signed_global_calibration", "pole_neutral_report", "parameter_jet_report"]
    records = []
    for module in modules:
        r = importlib.import_module(module).load_latest()
        assert r["status"] != "not_run", module
        assert not r.get("RH_proved", False), module
        checks = r.get("checks")
        flat = bool(checks) and all(type(v) is bool for v in checks.values())
        if flat:
            assert all(checks.values()), module
        records.append({"loader": module, "status": r["status"],
                        "run_directory": r.get("run_directory"),
                        "verification_sha256": r.get("verification_sha256"),
                        "checks_passed": sum(checks.values()) if flat else None,
                        "checks_total": len(checks) if flat else None,
                        "check_counts_omitted_for_nested_or_missing_schema": not flat})
    assert len(records) == 12
    assert registry["verified_arithmetic_consequence_count"] == 20
    assert registry["full_coefficient_origin_native_zeta_comparison_groups"] == 150
    assert not registry["historical_priority_is_acceptance_gate"]
    assert not registry["uniform_RH_sufficient_signed_controls_verified"]
    assert not registry["uniform_sublinear_signed_controls_verified"]
    imported = registry["imported_all_scale_signed_calibration"]
    assert imported["imported_dependency"]["analytic_source_proof_independently_reproved"] is False
    assert len(imported["operators"]) == 8
    jets = registry["general_parameter_jets_and_prime_recovery_calibration"]
    assert not jets["proof_is_machine_formalized"] and not jets["new_prime_distribution_bound_proved"]
    pole = registry["fractional_coefficient_and_log_kernel_search"]
    assert pole["RH_sufficient_obligations_passing_fresh_points"] == 10
    assert (BASE/"operator_candidates.txt").read_text().splitlines()[0].startswith(
        "TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES")
    result = {
        "status": "integration_verified_research_goal_still_active",
        "objective": registry["objective"], "historical_priority_is_acceptance_gate": False,
        "driver_sha256": sha("run_expanded_probe.py"),
        "integration_checker_sha256": sha("verify_signed_extensions_integration.py"),
        "registry_sha256": sha("root-results/candidate_registry.json"),
        "report_sha256": sha("root-results/report.txt"),
        "documentation_sha256": sha("SIGNED_ARITHMETIC_CONTROL.md"),
        "legacy_catalogue_scoped_counts": {"families": 10, "consequences": 20, "native_groups": 150},
        "legacy_catalogue_sha256": sha("operator_candidates.txt"),
        "strict_loaders_checked": records,
        "public_contract_checks": {
            "test_parameter_jets.py": {"cases": 4, "source_sha256": sha("test_parameter_jets.py")},
            "test_pole_neutral_contracts.py": {"cases": 4, "source_sha256": sha("test_pole_neutral_contracts.py")}},
        "imported_global_signed_calibration": {
            "constant": "85/64", "uniform_bound": imported["uniform_bound"],
            "complete_finite_patch_cutoff": 1798118,
            "named_infinite_range_dependency": "Ramare and Zuniga Alterman, arXiv:2408.05969v2, Theorem 1.1",
            "external_analytic_proof_independently_reproved": False, "RH_sufficient": False},
        "current_fractional_coefficient_results": {
            "programs": pole["programs"], "estimates_generated": pole["estimates"],
            "archived": pole["archived"], "fresh_point_survivors": pole["finite_archived_passes"],
            "RH_sufficient_if_uniform": pole["RH_sufficient_obligations_passing_fresh_points"],
            "exact_coefficients_checked": pole["exact_coefficients_checked"],
            "complete_signed_point_values_checked": pole["complete_signed_values_checked"],
            "native_Mellin_checks": pole["native_Mellin_checks"], "uniform_signed_premise_proved": False},
        "current_parameter_jet_calibration": {
            "exact_coefficient_values_checked": jets["exact_coefficient_values_checked"],
            "rigorous_Cauchy_kernel_coefficients": jets["rigorous_Cauchy_kernel_coefficients"],
            "complete_family_jet_values_checked": jets["complete_family_jet_values_checked"],
            "decoded_prime_cases": jets["decoded_prime_cases"],
            "difference_quotient_cases": jets["complete_difference_quotient_cases"],
            "scope": jets["scope"], "uniform_coupled_premise_proved": False},
        "proof_sources": {n: sha(n) for n in ["signed_global_calibration_proof.txt",
                                              "pole_neutral_proof.txt", "parameter_jet_proof.txt"]},
        "source_producer_reruns_for_integration": False,
        "uniform_RH_sufficient_signed_controls_verified": [], "RH_proved": False,
        "completion_audit": "Not achieved: no RH-sufficient all-scale signed estimate. Named imported o(x) calibration is weaker; parameter jets recover an exact prime-error representation but its coupled bound remains unproved."}
    destinations = [BASE/"pole-neutral-results/pilot-001/integration_verification.json",
                    BASE/"parameter-jet-results/calibration-001/integration_verification.json"]
    for path in destinations:
        if path.exists():
            raise FileExistsError("Retain prior integration milestones: " + str(path))
    for path in destinations:
        path.write_text(json.dumps(result, indent=2)+"\n")
    print("12 strict stages integrated; core scope remains 10 families / 20 consequences / 150 native groups")
    print("Ten finite RH-sufficient leads and coupled prime-error premise remain unproved globally")


if __name__ == "__main__":
    main()

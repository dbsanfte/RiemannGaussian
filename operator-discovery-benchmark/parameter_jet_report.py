"""Strict publication of a guided parameter-jet calibration, with no bound."""
import json
from pathlib import Path
from parameter_jet_audit import BASE, read, sha, digest


def summary(directory):
    directory = Path(directory).resolve()
    spec,data,audit = (read(directory/n) for n in ("protocol.json","jet_data.json","verification.json"))
    for name,expected in spec["code_sha256"].items():
        assert sha(BASE/name) == expected
    source = Path(spec["source_run"])
    assert sha(source/"verification.json") == spec["source_verification_sha256"]
    assert audit["all_passed"] and all(audit["checks"].values())
    assert audit["protocol_sha256"] == data["protocol_sha256"] == digest(spec)
    assert audit["checker_sha256"] == sha(BASE/"check_parameter_jets.py")
    assert audit["jet_data_sha256"] == sha(directory/"jet_data.json")
    assert data["cases_sha256"] == digest(read(directory/"cases.json"))
    assert not data["new_prime_distribution_bound_proved"] and not data["RH_proved"]
    return {"status":"independently_verified_guided_parameter_jet_calibration",
            "run_directory":str(directory),"checks":audit["checks"],
            "general_grammar_extension":"arbitrary-order rational Dirichlet parameter jets and independent coefficient/kernel slopes",
            "identity":"lim_(a->0+) (G_a(x)-1)/a = li(x)-sum_(p^k<x)1/k, for every real x>1",
            "all_scale_identity_argument":"parameter_jet_proof.txt",
            "proof_is_machine_formalized":False,
            "exact_coefficient_values_checked":audit["exact_coefficient_values_checked"],
            "rigorous_Cauchy_kernel_coefficients":audit["rigorous_Cauchy_kernel_coefficients"],
            "complete_family_jet_values_checked":audit["complete_family_jet_values_checked"],
            "decoded_prime_cases":audit["decoded_prime_cases"],
            "complete_difference_quotient_cases":audit["complete_difference_quotient_cases"],
            "observed_convergence_cases":audit["observed_convergence_cases"],
            "observed_convergence_total":audit["observed_convergence_total"],
            "coupled_RH_sufficient_target":data["coupled_RH_sufficient_target"],
            "scope":"guided_identity_recovery_not_autonomous_prime_estimate_discovery",
            "new_prime_distribution_bound_proved":False,
            "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False,
            "verification_sha256":sha(directory/"verification.json")}


def publish(directory):
    directory = Path(directory).resolve()
    r = summary(directory)
    (directory/"summary.json").write_text(json.dumps(r,indent=2)+"\n")
    text = ["GENERAL PARAMETER JETS AND GUIDED ACTUAL-PRIME RECOVERY","",
            "The grammar differentiates general rational coefficient powers at any rational centre.",
            "Coefficient and kernel slopes may vary independently; matching them is not assumed.",
            "For the matched path, the proved fixed-x limit is li(x)-sum_(p^k<x)1/k, for x>1.",
            "Exact root-count inversion recovers the ordinary strict prime count.",
            "These are arithmetic identities, not new prime-distribution bounds.","",
            f"Independent checks: {sum(r['checks'].values())}/{len(r['checks'])}.",
            f"Exact coefficient values: {r['exact_coefficient_values_checked']}; rigorous Cauchy kernel coefficients: {r['rigorous_Cauchy_kernel_coefficients']}.",
            f"Complete family jet values: {r['complete_family_jet_values_checked']}; decoded prime cases: {r['decoded_prime_cases']}.",
            f"Complete finite-difference probes: {r['complete_difference_quotient_cases']}; observed improvement as a decreases: {r['observed_convergence_cases']}/{r['observed_convergence_total']}.","",
            "RH-sufficient target: "+r["coupled_RH_sufficient_target"]["premise"],
            "The required coupled all-scale, all-small-exponent bound remains unproved.",
            "Finite exponents or constants independent of a do not supply derivative control.",
            "Guided calibration: no autonomous discovery, historical novelty or RH proof claimed.",
            "The universal argument is mathematical prose, not a machine-formalized analytic proof.",
            "Proof: parameter_jet_proof.txt."]
    (directory/"report.txt").write_text("\n".join(text)+"\n")
    pointer = BASE/"parameter-jet-results/latest.json"
    pointer.parent.mkdir(exist_ok=True)
    pointer.write_text(json.dumps({"run_directory":str(directory),"summary_sha256":digest(r)},indent=2)+"\n")
    print("Published guided parameter-jet calibration; uniform prime-error bound remains open",flush=True)


def load_latest():
    p = BASE/"parameter-jet-results/latest.json"
    if not p.exists():
        return {"status":"not_run","uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    pointer = read(p)
    r = summary(pointer["run_directory"])
    assert digest(r) == pointer["summary_sha256"]
    return r

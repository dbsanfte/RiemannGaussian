"""Strict reporting of signed prime-error leads and logarithmic faithfulness."""
from collections import Counter
from pathlib import Path
import json
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    directory=Path(directory).resolve()
    spec,seal,audit,arc,final=(read(directory/n) for n in ("protocol.json","seal.json","verification.json","archive.json","final_evaluation.json"))
    for n,h in spec["code_sha256"].items():assert sha(BASE/n)==h
    source=Path(spec["source_run"])
    assert sha(source/"verification.json")==spec["source_verification_sha256"]
    assert sha(source/"jet_data.json")==spec["source_data_sha256"]
    assert audit["all_passed"] and all(audit["checks"].values()) and audit["protocol_sha256"]==digest(spec)
    assert audit["final_sha256"]==sha(directory/"final_evaluation.json") and audit["checker_sha256"]==sha(BASE/"check_prime_error.py")
    for n,h in seal["files"].items():assert sha(directory/n)==h
    assert final["seal_sha256"]==digest(seal) and final["cases_sha256"]==digest(read(directory/"final_cases.json"))
    ps={p["id"]:p for p in read(directory/"candidate_batch.json")["programs"]}
    survivors=[];false_finite=0;control_finite=0
    for c,o in zip(arc["archive"],final["outcomes"]):
        assert c["id"]==o["candidate_id"]
        if o["finite_points_passed"] and c["analytic_status"].startswith("RH_sufficient"):
            survivors.append({"program":ps[c["program_id"]],"candidate":c})
        if o["finite_points_passed"] and c["analytic_status"].startswith("uniform_claim_ruled_out"):
            false_finite+=1
        if o["support_control_uniform_claims_ruled_out"]:
            control_finite+=sum(all(v=="pass" for v in states.values()) for states in o["support_control_comparisons"].values())
    return {"status":"independently_verified_signed_prime_error_filter_search",
            "run_directory":str(directory),"checks":audit["checks"],"programs":len(ps),
            "estimates":audit["estimates_checked"],"archived":len(arc["archive"]),
            "statuses":dict(Counter(c["analytic_status"] for c in read(directory/"validation_data.json")["candidates"])),
            "exact_coefficients_checked":audit["exact_coefficients_checked"],
            "complete_signed_point_values_checked":audit["complete_signed_point_values_checked"],
            "complete_support_control_values_checked":audit["complete_support_control_values_checked"],
            "native_logarithmic_bridge_checks":audit["native_logarithmic_bridge_checks"],
            "complete_coefficient_cutoff":final["coefficient_cutoff"],
            "finite_archived_passes":sum(o["finite_points_passed"] for o in final["outcomes"]),
            "RH_sufficient_obligations_passing_fresh_points":len(survivors),
            "finite_passes_nevertheless_globally_ruled_out":false_finite,
            "finite_support_control_passes_nevertheless_globally_ruled_out":control_finite,
            "surviving_uniform_proof_obligations":survivors,
            "surviving_filters_failing_old_gate_by_zero_at_one":sum(r["program"]["multiplier_at_one"]=="0" for r in survivors),
            "all_height_multiplier_nonvanishing_required":False,
            "isolated_multiplier_zeros_preserve_every_ordinary_zero_multiplicity":True,
            "whole_unit_integer_to_real_transfer_proved":True,
            "native_zero_calibration_scope":"guided analytic multiplier F^k vanishes at the enclosed actual zero, separate from finite-dilation discovery",
            "analytic_proof_is_machine_formalized":False,
            "quantitative_cost_scope":"full exponential reconstruction at one declared point; no all-height removable-division certificate",
            "historical_priority_is_acceptance_gate":False,
            "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False,
            "verification_sha256":sha(directory/"verification.json")}


def publish(directory):
    directory=Path(directory).resolve();r=summary(directory)
    (directory/"summary.json").write_text(json.dumps(r,indent=2)+"\n")
    lines=["SIGNED PRIME-ERROR FILTERS WITH LOGARITHMIC ZERO-FAITHFULNESS","",
        "The arithmetic input is the first parameter jet: li(x)-sum_(p^k<x)1/k, truncated below two.",
        "The coefficient producer uses factor-free inversion and logarithms; an independent sieve checks actual prime powers.",
        "Finite signed dilations may have multiplier zeros inside the critical half-plane.",
        "A meromorphic derivative has zero residue; zeta'/zeta has a nonzero residue at every zero multiplicity.",
        "The resulting conditional zero bridge needs a non-identically-zero multiplier, not all-height nonvanishing.","",
        f"Programs: {r['programs']}; learned estimates: {r['estimates']}; archived: {r['archived']}.",
        f"Independent checks: {sum(r['checks'].values())}/{len(r['checks'])}.",
        f"Exact coefficients: {r['exact_coefficients_checked']}; complete signed point values: {r['complete_signed_point_values_checked']}.",
        f"Final complete coefficient prefix: {r['complete_coefficient_cutoff']}; native logarithmic bridge checks: {r['native_logarithmic_bridge_checks']}.",
        f"Finite archive passes: {r['finite_archived_passes']}/{r['archived']}; RH-sufficient if uniform: {r['RH_sufficient_obligations_passing_fresh_points']}.",
        f"Surviving filters whose multiplier is zero at one: {r['surviving_filters_failing_old_gate_by_zero_at_one']}.",
        f"Actual finite passes nevertheless globally false: {r['finite_passes_nevertheless_globally_ruled_out']}.",
        f"Support-control finite passes nevertheless globally false: {r['finite_support_control_passes_nevertheless_globally_ruled_out']}.",
        json.dumps(r["statuses"],indent=2),"","Surviving uniform proof obligations:"]
    for row in r["surviving_uniform_proof_obligations"]:
        p,c=row["program"],row["candidate"]
        lines.append(f"beta={p['beta']}; atoms={p['atoms']}; for EVERY integer n>=1, |R(n)-{c['offset']}|<={c['constant']}*n^{c['theta']}*log(e+n)^{c['log_power']}")
    lines.extend(["","All required uniform signed integer premises remain unproved. RH remains unproved.",
        "Whole-unit increments transfer an integer estimate to every real scale without changing theta.",
        "Costs charge exponential logarithmic reconstruction at a fixed point, not an all-height division bound.",
        "The analytic argument is mathematical prose; no machine-formalized RH proof is claimed.",
        "Proof: prime_error_proof.txt. Native actual-zero multiplier calibration is guided and separately scoped."])
    (directory/"report.txt").write_text("\n".join(lines)+"\n")
    pointer=BASE/"prime-error-results/latest.json";pointer.parent.mkdir(exist_ok=True)
    pointer.write_text(json.dumps({"run_directory":str(directory),"summary_sha256":digest(r)},indent=2)+"\n")
    print("Published signed prime-error search; global signed premises remain open",flush=True)


def load_latest():
    p=BASE/"prime-error-results/latest.json"
    if not p.exists():return {"status":"not_run","uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    pointer=read(p);r=summary(pointer["run_directory"])
    assert digest(r)==pointer["summary_sha256"]
    return r

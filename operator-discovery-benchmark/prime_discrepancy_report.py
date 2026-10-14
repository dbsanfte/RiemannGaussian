"""Strictly separate proved unsigned prime inputs from signed proof obligations."""
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
    assert sha(source/"candidate_batch.json")==spec["source_batch_sha256"]
    from prime_error_report import summary as parent_summary
    parent_summary(source)
    assert audit["all_passed"] and all(audit["checks"].values()) and audit["protocol_sha256"]==digest(spec)
    assert audit["final_sha256"]==sha(directory/"final_evaluation.json") and audit["checker_sha256"]==sha(BASE/"check_prime_discrepancy.py")
    for n,h in seal["files"].items():assert sha(directory/n)==h
    assert final["seal_sha256"]==digest(seal) and final["cases_sha256"]==digest(read(directory/"final_cases.json"))
    development=read(directory/"discovery_data.json");ps={p["id"]:p for p in spec["input_programs"]}
    survivors=[];finite_false=0;control_passes=0
    for c,o in zip(arc["archive"],final["outcomes"]):
        assert c["id"]==o["candidate_id"]
        if o["finite_windows_passed"] and c["analytic_status"].startswith("RH_sufficient"):
            survivors.append({"program":ps[c["program_id"]],"candidate":c})
        if o["finite_windows_passed"] and c["analytic_status"].startswith("uniform_claim_ruled_out"):
            finite_false+=1
        control_passes+=sum(all(v=="pass" for v in states.values()) for states in o["support_control_comparisons"].values())
    selected=development["carry_search"]["selected"]
    return {"status":"independently_verified_floor_density_and_signed_prime_correlation_search",
        "run_directory":str(directory),"checks":audit["checks"],"programs":len(ps),"estimates":audit["estimates_checked"],
        "archived":len(arc["archive"]),"carry_proposals":audit["carry_proposals_checked"],
        "universal_floor_certificates":audit["universal_floor_certificates_checked"],
        "full_period_cells_checked":audit["full_period_cells_checked"],"carry_statuses":development["carry_search"]["statuses"],
        "selected_prime_density_certificate":selected,
        "all_scale_prime_density_bound_proved":True,"all_scale_prime_density_bound_is_signed":False,
        "all_scale_coefficient_density_certificates":{beta:r["selected"] for beta,r in development["coefficient_densities"].items()},
        "all_scale_diagonal_bound_proved":True,"imported_prime_distribution_estimate":False,
        "prime_density_finite_patch_values_checked":audit["prime_density_finite_patch_values_checked"],
        "coefficient_density_finite_patch_values_checked":audit["coefficient_density_finite_patch_values_checked"],
        "exact_coefficients_checked":audit["exact_coefficients_checked"],"complete_coefficient_cutoff":final["coefficient_cutoff"],
        "complete_actual_windows_checked":audit["complete_actual_windows_checked"],
        "complete_support_control_windows_checked":audit["complete_support_control_windows_checked"],
        "polynomial_integration_cells_checked":audit["polynomial_integration_cells_checked"],
        "independent_ramp_Gram_entries_checked":audit["independent_ramp_Gram_entries_checked"],
        "finite_archived_passes":sum(o["finite_windows_passed"] for o in final["outcomes"]),
        "RH_sufficient_obligations_passing_fresh_windows":len(survivors),
        "finite_passes_nevertheless_globally_ruled_out":finite_false,
        "finite_support_control_passes":control_passes,
        "support_controls_are_actual_prime_density_inputs":False,
        "surviving_uniform_proof_obligations":survivors,
        "statuses":dict(Counter(c["analytic_status"] for c in read(directory/"validation_data.json")["candidates"])),
        "input_programs_selected_by_prior_final_outcomes":False,"analytic_proof_is_machine_formalized":False,
        "historical_priority_is_acceptance_gate":False,"uniform_signed_correlation_premise_proved":False,
        "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False,"verification_sha256":sha(directory/"verification.json")}


def publish(directory):
    directory=Path(directory).resolve();r=summary(directory)
    (directory/"summary.json").write_text(json.dumps(r,indent=2)+"\n")
    c=r["selected_prime_density_certificate"];density=c["density"]
    lines=["ACTUAL-PRIME DENSITY CERTIFICATES AND SIGNED PRIME-DISCREPANCY CORRELATIONS","",
        "The new unconditional results are unsigned all-scale prime and diagonal bounds.",
        "Every RH-strength signed off-diagonal premise remains unproved.","",
        f"Enumerated floor programs: {r['carry_proposals']}; universal nonnegative periodic certificates: {r['universal_floor_certificates']}.",
        f"Selected coefficients (delays 1..6): {c['coefficients']}.",
        f"For EVERY real x>=1: psi(x)<={density['constant']}*x.",
        "The proof uses a factorial trace, a complete periodic floor certificate, and monotone dyadic tails.",
        "No prime-distribution theorem is imported; no historical novelty is claimed.","",
        "For signed increments a_n of the interpolated prime error:"]
    for beta,v in r["all_scale_coefficient_density_certificates"].items():
        lines.append(f"beta={beta}: for EVERY integer N>=1, sum_(n<=N) a_n^2 <= {v['constant']}*N/log(e+N).")
    lines.extend(["For EVERY real X>=1, D(X)<=3*C_a*(sum|c_d|)^2*X^2/log(e+X).",
        "D is the same-increment Gram diagonal; C_off=A2-D contains the signed pair information.","",
        f"Source filter programs: {r['programs']}; learned estimates: {r['estimates']}; archived: {r['archived']}.",
        f"Independent checks: {sum(r['checks'].values())}/{len(r['checks'])}.",
        f"Complete actual windows: {r['complete_actual_windows_checked']}; support-control windows: {r['complete_support_control_windows_checked']}.",
        f"Independent per-increment Gram entries: {r['independent_ramp_Gram_entries_checked']}; full polynomial cells: {r['polynomial_integration_cells_checked']}.",
        f"Final complete coefficient prefix: {r['complete_coefficient_cutoff']}.",
        f"Finite archive passes: {r['finite_archived_passes']}/{r['archived']}; RH-sufficient if uniform: {r['RH_sufficient_obligations_passing_fresh_windows']}.",
        f"Actual finite passes nevertheless globally false: {r['finite_passes_nevertheless_globally_ruled_out']}.",
        f"Finite support-control passes: {r['finite_support_control_passes']} (actual-prime density theorems do not apply to these controls).",
        json.dumps(r["statuses"],indent=2),"","Surviving uniform SIGNED proof obligations:"])
    for row in r["surviving_uniform_proof_obligations"]:
        p,c=row["program"],row["candidate"]
        lines.append(f"beta={p['beta']}; atoms={p['atoms']}; for EVERY integer X>=1, C_off(X)<={c['rho']}*D(X)+{c['constant']}*X^{c['gamma']}")
    lines.extend(["","The zero bridge remains the logarithmic meromorphic residue argument, including multiplier zeros.",
        "Bounded interpolation error preserves that bridge. Quadratic moments here are evaluated on complete windows.",
        "Uniform signed pair bounds remain open. RH remains unproved. Proof: prime_discrepancy_proof.txt."])
    (directory/"report.txt").write_text("\n".join(lines)+"\n")
    pointer=BASE/"prime-discrepancy-results/latest.json";pointer.parent.mkdir(exist_ok=True)
    pointer.write_text(json.dumps({"run_directory":str(directory),"summary_sha256":digest(r)},indent=2)+"\n")
    print("Published all-scale unsigned prime inputs and finite signed-correlation leads; RH remains open",flush=True)


def load_latest():
    p=BASE/"prime-discrepancy-results/latest.json"
    if not p.exists():return {"status":"not_run","uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    pointer=read(p);r=summary(pointer["run_directory"])
    assert digest(r)==pointer["summary_sha256"]
    return r

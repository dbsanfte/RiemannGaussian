"""Strict reporting for fractional prime twists and signed decay obligations."""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import json
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    directory=Path(directory).resolve()
    spec,seal,audit,arc,final=(read(directory/n) for n in ("protocol.json","seal.json","verification.json","archive.json","final_evaluation.json"))
    for n,h in spec["code_sha256"].items():assert sha(BASE/n)==h
    for n in spec["this_stage_source_files"]:assert sha(directory/"frozen_source"/n)==spec["code_sha256"][n]
    source=Path(spec["source_run"])
    for name,key in (("verification.json","source_verification_sha256"),("archive.json","source_archive_sha256"),("final_evaluation.json","source_final_sha256")):
        assert sha(source/name)==spec[key]
    from prime_discrepancy_report import summary as parent_summary
    parent=parent_summary(source)
    assert spec["prime_density_constant"]==parent["selected_prime_density_certificate"]["density"]["constant"]
    assert audit["all_passed"] and all(audit["checks"].values()) and audit["protocol_sha256"]==digest(spec)
    assert audit["final_sha256"]==sha(directory/"final_evaluation.json") and audit["checker_sha256"]==sha(BASE/"check_prime_twists.py")
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"] and not seal["final_cases_exist_at_seal"]
    for n,h in seal["files"].items():assert sha(directory/n)==h
    cases=read(directory/"final_cases.json")
    assert final["seal_sha256"]==digest(seal) and final["cases_sha256"]==digest(cases)
    assert cases["created_after_selection_closed"] and not arc["final_data_used"] and all(arc["worker_access_denials"].values())
    batch=read(directory/"candidate_batch.json");ps={p["id"]:p for p in batch["programs"]}
    assert len(arc["archive"])==len(final["outcomes"])
    survivors=[];false_passes=[];all_rows=[]
    for c,o in zip(arc["archive"],final["outcomes"]):
        assert c["id"]==o["candidate_id"] and not o["uniform_signed_premise_proved"] and not o["reselected"]
        row={"program":ps[c["program_id"]],"candidate":c,"final_outcome":o};all_rows.append(row)
        if o["finite_points_passed"] and c["analytic_status"].startswith("RH_sufficient"):survivors.append(row)
        if o["finite_points_passed"] and c["analytic_status"].startswith("uniform_claim_ruled_out"):false_passes.append(row)
    cal=final["signed_harmonic_calibration"]
    assert cal["signed_harmonic_global_theorem_proved"] and cal["signed_reciprocal_prime_tail_theorem_proved"] and not cal["RH_sufficient"]
    assert not audit["RH_proved"] and not final["RH_proved"] and not arc["RH_proved"]
    assert audit["uniform_RH_sufficient_signed_controls_verified"]==final["uniform_RH_sufficient_signed_controls_verified"]==[]
    ctrl_passes=sum(all(s=="pass" for s in states.values()) for ctrl in final["density_matched_delayed_controls"] for states in ctrl["source_bound_comparisons"].values())
    return {"status":"independently_verified_fractional_prime_twists_and_signed_decay_search",
        "run_directory":str(directory),"checks":audit["checks"],"programs":audit["programs_checked"],"estimates":audit["estimates_checked"],
        "archived":len(all_rows),"channels":spec["channels"],"pilot_fractional_shifts":spec["deltas"],"semantic_denominator_ceiling":None,
        "negative_growth_exponents_supported":True,"negative_growth_requires_exact_Mellin_center":True,
        "all_shift_recovery_costs_charged":True,"ordinary_zero_recovery_includes_arbitrary_multiplicities":True,
        "all_height_scalar_nonvanishing_gate_required":False,"complete_coefficient_cutoff":final["coefficient_cutoff"],
        "exact_coefficients_checked":audit["exact_coefficients_checked"],"complete_point_values_checked":audit["complete_point_values_checked"],
        "generic_signed_response_values_checked":audit["generic_signed_response_values_checked"],
        "native_kernel_integrals_checked":audit["native_kernel_integrals_checked"],"native_shift_log_checks":audit["native_shift_log_checks"],
        "fractional_root_identity_cases":audit["fractional_root_identity_cases"],"signed_fractional_tail_cases_checked":audit["signed_fractional_tail_cases_checked"],
        "prime_density_constant":spec["prime_density_constant"],"signed_harmonic_interval":cal["harmonic_interval"],
        "mertens_logarithmic_constant":cal["mertens_logarithmic_constant"],
        "all_scale_signed_actual_prime_harmonic_theorem_proved":True,
        "all_scale_signed_actual_prime_reciprocal_tail_theorem_proved":True,
        "signed_reciprocal_tail_domain":"every real x>=2 and every real fractional order nu>=1",
        "proved_signed_tail_ordinary_zeta_exponent_after_recovery":"1",
        "signed_global_calibrations_RH_sufficient":False,"imported_prime_distribution_estimate":False,
        "proof_backend_autonomously_invented_by_detector":False,"analytic_proof_is_machine_formalized":False,
        "finite_archived_passes":sum(o["finite_points_passed"] for o in final["outcomes"]),
        "RH_sufficient_obligations_passing_fresh_points":len(survivors),
        "negative_decay_RH_sufficient_obligations_passing_fresh_points":sum(Q(r["candidate"]["theta"])<0 for r in survivors),
        "finite_passes_nevertheless_globally_ruled_out":len(false_passes),
        "complete_density_matched_control_windows_checked":audit["complete_density_matched_control_windows_checked"],
        "density_matched_controls_preserve_actual_prime_power_locations":True,
        "density_matched_controls_preserve_original_prime_power_weights":False,
        "density_matched_controls_preserve_same_global_density_and_diagonal_bounds":True,
        "finite_density_matched_control_bound_passes":ctrl_passes,
        "density_matched_controls_all_RH_strength_uniform_claims_ruled_out":True,
        "density_matched_control_results":final["density_matched_delayed_controls"],
        "surviving_uniform_proof_obligations":survivors,"globally_false_finite_passes":false_passes,"archive_results":all_rows,
        "statuses":dict(Counter(c["analytic_status"] for c in batch["candidates"])),
        "historical_priority_is_acceptance_gate":False,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False,
        "remaining_assumptions":spec["remaining_assumptions"],"verification_sha256":sha(directory/"verification.json")}


def publish(directory):
    directory=Path(directory).resolve();r=summary(directory)
    (directory/"summary.json").write_text(json.dumps(r,indent=2)+"\n")
    lines=["FRACTIONAL PRIME TWISTS AND SIGNED DECAY: VERIFIED RESULTS AND OPEN RH PREMISES","",
        "Actual-prime signed harmonic and reciprocal-tail bounds are proved at every scale.",
        "They recover ordinary zeta only at exponent one. RH remains unproved.","",
        f"For EVERY real x>=2: -1 <= sum_(p^k<x) log(p)/p^k - log x <= {r['prime_density_constant']}.",
        f"For EVERY real x>=2: |sum_(p^k<x) 1/(k p^k) - log(log x) - gamma| <= {r['mertens_logarithmic_constant']}/log x.",
        "For EVERY real nu>=1: |J_(1-nu)(x)-sum_(n<x)lambda(n)n^(-nu)-K_nu|",
        f"  <= {r['mertens_logarithmic_constant']}*x^(1-nu)/log x, EVERY real x>=2.",
        "The proof uses the factorial trace and the preceding certified density bound; no prime-distribution estimate is imported.",
        "These supplied proof backends are calibration theorems, not claims of autonomous proof invention or historical novelty.","",
        "The general search has two channels: lambda and Lambda=lambda*log(n).",
        "Finite rational polynomials in fractional arithmetic shifts have independently chosen smooth normalizers.",
        "Negative rational growth exponents require exact Mellin finite-part centers, including gamma where dictated by the formula.",
        "Output decay is charged for its leading arithmetic shift before judging its ordinary-zeta exponent.",
        "The right-shift multiplicity proof recovers every ordinary zero, allowing shifted coincidences.",
        "All recurrence paths, Euler endpoints and horizontal-integration costs are independently checked.","",
        f"Programs: {r['programs']}; estimates: {r['estimates']}; archived: {r['archived']}.",
        f"Independent checks: {sum(r['checks'].values())}/{len(r['checks'])}; complete coefficient prefix: {r['complete_coefficient_cutoff']}.",
        f"Finite archive passes: {r['finite_archived_passes']}/{r['archived']}; RH-sufficient if uniform: {r['RH_sufficient_obligations_passing_fresh_points']}.",
        f"Negative-decay RH obligations passing fresh points: {r['negative_decay_RH_sufficient_obligations_passing_fresh_points']}.",
        f"Actual finite passes nevertheless globally ruled out: {r['finite_passes_nevertheless_globally_ruled_out']}.","",
        "Stronger false controls retain every actual prime-power location, agree through 8192, and have weights <= actual lambda.",
        "They satisfy the same proved all-scale prime-density and diagonal bounds.",
        "Their original 1/k weights change above that cutoff; this is recorded explicitly.",
        "With the original li normalizer, the shifted pole at 1-delta rules out a uniform RH-strength estimate.",
        f"Complete matched-control windows checked: {r['complete_density_matched_control_windows_checked']};",
        f"source moment bounds passed on all fresh windows by controls: {r['finite_density_matched_control_bound_passes']}.","",
        "Surviving uniform SIGNED proof obligations (numerical evidence only):"]
    for row in r["surviving_uniform_proof_obligations"]:
        p,c=row["program"],row["candidate"]
        center="0" if c["offset"]["kind"]=="rational" else "exact compiled Mellin finite part"
        lines.append(f"channel={p['channel']}, delta={p['delta']}, c={p['coefficients']}, b={p['normalizers']}; center={center}; |E(n)-center|<={c['constant']}*n^({c['theta']})*log(e+n)^({c['log_power']}) for EVERY integer n>=1.")
    lines.extend(["",json.dumps(r["statuses"],indent=2),"",
        "Finite successes are open universal proof obligations. No RH-strength uniform signed premise has been proved.",
        "Written proof: prime_twist_proof.txt. These analytic arguments are independently audited but not machine-formalized."])
    (directory/"report.txt").write_text("\n".join(lines)+"\n")
    pointer=BASE/"prime-twist-results/latest.json";pointer.parent.mkdir(exist_ok=True)
    pointer.write_text(json.dumps({"run_directory":str(directory),"summary_sha256":digest(r)},indent=2)+"\n")
    print("Published signed all-scale prime calibrations and fractional-decay leads; RH remains open",flush=True)


def load_latest():
    path=BASE/"prime-twist-results/latest.json"
    if not path.exists():return {"status":"not_run","uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    pointer=read(path);r=summary(pointer["run_directory"])
    assert digest(r)==pointer["summary_sha256"]
    return r

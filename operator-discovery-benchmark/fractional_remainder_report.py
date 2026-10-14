"""Strict loader for conditional infinite-order fractional remainder evidence."""
from collections import Counter
from pathlib import Path
import json
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    directory=Path(directory).resolve()
    spec,seal,checked,batch,archive,final,cases=(read(directory/n) for n in
        ["protocol.json","seal.json","verification.json","candidate_batch.json","archive.json","final_evaluation.json","final_cases.json"])
    for n,h in spec["code_sha256"].items():assert sha(BASE/n)==h
    for n in spec["this_stage_source_files"]:assert sha(directory/"frozen_source"/n)==spec["code_sha256"][n]
    assert checked["all_passed"] and all(checked["checks"].values()) and checked["protocol_sha256"]==digest(spec)
    assert checked["checker_sha256"]==sha(BASE/"check_fractional_remainders.py") and checked["final_sha256"]==sha(directory/"final_evaluation.json")
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"] and not seal["final_cases_exist_at_seal"]
    for n,h in seal["files"].items():assert sha(directory/n)==h
    assert checked["replay_sha256"]==seal["files"]
    assert final["cases_sha256"]==digest(cases) and final["seal_sha256"]==cases["seal_sha256"]==digest(seal)
    assert cases["created_after_selection_closed"] and archive["selection_closed"] and not archive["final_data_used"]
    source=Path(spec["source_run"])
    for n,h in spec["source_sha256"].items():assert sha(source/n)==h
    from prime_oscillation_report import summary as parent_summary
    parent_summary(source)
    assert checked["uniform_RH_sufficient_signed_controls_verified"]==final["uniform_RH_sufficient_signed_controls_verified"]==[]
    assert not final["RH_proved"] and spec["not_autonomous_proof_invention"] and not spec["imported_prime_distribution_estimate"]
    ps={p["id"]:p for p in batch["programs"]};outcomes={o["candidate_id"]:o for o in final["outcomes"]};records=[];survivors=[]
    for c in archive["archive"]:
        o=outcomes[c["id"]];p=ps[c["program_id"]];assert not o["uniform_signed_premise_proved"]
        row={"program":p,"candidate":c,"final_outcome":o};records.append(row)
        if o["finite_points_passed"] and c["transfer"]["RH_sufficient_if_uniform"]:survivors.append(row)
    controls=[dict(row,program=ps[row["candidate"]["program_id"]],final_outcome=outcomes[row["candidate"]["id"]]) for row in archive["negative_controls"]]
    backend=read(directory/"backend_certificates.json")
    counts={k:v for k,v in checked.items() if type(v) is int}
    return {"status":"independently_checked_fractional_remainders_with_conditional_infinite_parameter_recovery",
        "run_directory":str(directory),"source_run":str(source),"checks":checked["checks"],**counts,
        "programs":len(batch["programs"]),"ablation_programs":len(batch["ablation_programs"]),"growth_hypotheses":len(batch["candidates"]),
        "generation_family_counts":dict(Counter(p["family"] for p in batch["programs"])),
        "exact_parameter_order_counts":dict(Counter(str(p["parameter_vanishing_order"]) for p in batch["programs"])),
        "analytic_status_counts":dict(Counter(c["analytic_status"] for c in batch["candidates"])),
        "archive_size":len(records),"archived_finite_passes":sum(r["final_outcome"]["finite_points_passed"] for r in records),
        "RH_sufficient_family_obligations_passing_fresh_points":len(survivors),"surviving_uniform_proof_obligations":survivors,
        "archive_results":records,"negative_control_results":controls,"known_false_controls_passing_fresh_points":sum(r["final_outcome"]["finite_points_passed"] for r in controls),
        "ablation_comparison":archive["ablation_comparison"],"complete_coefficient_cutoff":final["complete_coefficient_cutoff"],
        "fresh_integer_scales":cases["integers"],"fresh_order_parameters_q":cases["fresh_q"],"all_final_order_parameters_q":cases["qs"],
        "all_height_zero_recovery_argument_checked":True,"zero_recovery_requires_infinite_parameter_premise":True,
        "fixed_fractional_order_given_all_height_nonvanishing":False,"finite_parameter_grid_suffices_for_positive_degree":False,
        "proved_all_scale_signed_parameter_cancellation":True,"proved_signed_parameter_growth_exponent":"1",
        "proved_global_family_and_unit_bound_certificates":len(backend["global_certificates"]),
        "all_scale_signed_certificate_scope":"parameter cancellation and polynomial-log coefficient/unit bounds for actual Mobius/fractional prime structure; x-growth exponent one",
        "new_prime_distribution_estimate_proved":False,"prime_distribution_theorem_imported":False,
        "supplied_mathematical_backends":spec["supplied_backends"],"detector_autonomously_invented_backends":False,
        "analytic_proof_is_machine_formalized":False,"actual_prime_or_factor_oracle_used_by_coefficient_producer":False,
        "freshness_scope":spec["final_freshness_scope"],"historical_priority_is_acceptance_gate":False,
        "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False,"verification_sha256":sha(directory/"verification.json")}


def publish(directory):
    directory=Path(directory).resolve();r=summary(directory)
    (directory/"summary.json").write_text(json.dumps(r,indent=2)+"\n")
    lines=["FRACTIONAL ARITHMETIC REMAINDERS AND INFINITE-PARAMETER ZERO RECOVERY","",
        "T_beta = mu * ((log n)^beta for n>=2; zero at n=1).",
        "J_beta(y) = integral_1^y (log t)^beta dt.",
        "R_beta(x) = sum_(n<=x) T_beta(n) - sum_(d<=x) mu(d) J_beta(x/d).",
        "V_a has independent fixed rational arithmetic coefficients c_j and continuous normalizers b_j at orders j*a.",
        "At beta=0, R_0(x)=1-x sum_(d<=x)mu(d)/d. The alpha=0 index-one convention is explicit.","",
        "The continuous correction removes the fractional singularity at zeta's pole.",
        "Its entire numerator is verified by different native difference/derivative integrals with rigorous infinite tails.",
        "A parameter pole at a=-1/D with nonzero residue -c_D/D prevents every ordinary zero from being erased by ALL orders at once.",
        "The identity theorem requires infinitely many a_q=1/(D*q), q>=2; a finite parameter grid cannot establish the premise.",
        "This includes high-pass families whose small-order limit vanishes.","",
        f"Primary programs: {r['programs']}; complete estimates: {r['growth_hypotheses']}; archive: {r['archive_size']}.",
        f"Generation families: {r['generation_family_counts']}.",
        f"Exact parameter vanishing orders: {r['exact_parameter_order_counts']}.",
        f"Native numerator checks: {r['native_entire_numerators_checked']}; full reciprocal-gamma subboxes: {r['native_reciprocal_gamma_subboxes_checked']}.",
        f"Global weak-family certificates: {r['proved_global_family_and_unit_bound_certificates']}.",
        "The proved all-scale parameter cancellation has x-growth exponent ONE, not one half.",
        "Every conditional reciprocal cost charges the numerator, fractional normalization and integer-to-real unit correction.","",
        f"Fresh scales: {r['fresh_integer_scales']}; fresh q values: {r['fresh_order_parameters_q']}; complete coefficients through {r['complete_coefficient_cutoff']}.",
        f"Archive finite passes: {r['archived_finite_passes']}; conditional RH-family leads passing: {r['RH_sufficient_family_obligations_passing_fresh_points']}.",
        f"Known false family bounds passing finite final probes: {r['known_false_controls_passing_fresh_points']} (if positive, not universal proof).",
        f"Independent checks: {sum(r['checks'].values())}/{len(r['checks'])}.",
        f"Equal-proposal-slot promotion ablation: {r['ablation_comparison']}.","",
        "Surviving unproved obligations, each for EVERY n>=1 AND EVERY q>=2:"]
    for row in r["surviving_uniform_proof_obligations"]:
        p,c=row["program"],row["candidate"]
        lines.append(f"c={p['coefficients']}; b={p['normalizers']}; D={p['degree']}; |V_(1/(max(1,D)*q))(n)|<={c['constant']}*a_q^({c['parameter_power']})*n^({c['theta']})*log(e+n)^({c['log_power']}).")
    lines.extend(["","The mathematical backends are supplied by us, then checked independently. The selector is deterministic and isolated; it learns combinations and exponents without expected-answer assertions.",
        "Native computations and reviewed generic analytic arguments are not a machine-formalized proof.",
        "Mobius coefficients overlap prior research data; the fresh tests use new observables, scales and parameter values.",
        "No new prime-distribution estimate or RH-strength all-scale bound has been proved. RH remains open in this project.",
        "Proof source: fractional_remainder_proof.txt. Original earlier-stage results are retained."])
    (directory/"report.txt").write_text("\n".join(lines)+"\n")
    pointer=BASE/"fractional-remainder-results/latest.json";pointer.write_text(json.dumps({"run_directory":str(directory),"summary_sha256":digest(r)},indent=2)+"\n")
    print("Published fractional remainder family; infinite-order RH premise remains unproved",flush=True)


def load_latest():
    pointer=BASE/"fractional-remainder-results/latest.json"
    if not pointer.exists():return {"status":"not_run","uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    rec=read(pointer);r=summary(rec["run_directory"]);assert digest(r)==rec["summary_sha256"]
    return r

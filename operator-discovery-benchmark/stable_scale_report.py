#!/usr/bin/env python3
"""Strict publication of signed scale-polynomial search results."""
from collections import Counter
import hashlib
import json
from pathlib import Path

BASE=Path(__file__).resolve().parent


def read(path): return json.loads(Path(path).read_text())
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def digest(data): return hashlib.sha256(json.dumps(data,sort_keys=True,separators=(",", ":"),allow_nan=False).encode()).hexdigest()


def summary(directory):
    directory=Path(directory).resolve(); spec=read(directory/"protocol.json"); audit=read(directory/"verification.json")
    seal=read(directory/"seal.json"); final=read(directory/"final_evaluation.json"); archive=read(directory/"archive.json")
    assert audit["all_passed"] and all(audit["checks"].values())
    assert audit["final_sha256"]==sha(directory/"final_evaluation.json")
    assert audit["protocol_sha256"]==digest(spec) and final["seal_sha256"]==digest(seal)
    assert audit["checker_sha256"]==sha(BASE/"check_stable_scale.py")
    for name,expected in spec["code_sha256"].items(): assert sha(BASE/name)==expected
    for name,expected in seal["files"].items(): assert sha(directory/name)==expected
    cases=read(directory/"final_cases.json"); assert final["cases_sha256"]==digest(cases)
    batch=read(directory/"candidate_batch.json"); validation=read(directory/"validation_data.json")
    certified=[p for p in batch["programs"] if p["operator_certificate"]["all_height_critical_multiplier_certified"]]
    outside=[p for p in certified if p["operator_certificate"]["outside_triangle_domain_certified"]]
    statuses=Counter(e["status"] for r in validation["records"] for e in r["estimates"])
    return {"status":"independently_verified_signed_scale_polynomial_search","run_directory":str(directory),
            "objective":spec["objective"],"historical_priority_is_acceptance_gate":False,
            "generated":len(batch["programs"]),"rejected":len(batch["rejected"]),
            "automatic_compositions":len(batch["promotions"]),
            "all_height_certified":len(certified),"certified_outside_triangle_domain":len(outside),
            "retained_without_available_global_certificate":len(batch["programs"])-len(certified),
            "archived":len(archive["archive"]),"exact_complete_moment_values":audit["exact_complete_moment_values"],
            "finite_estimates_passed":sum(o["finite_windows_passed"] for r in final["records"] for o in r["outcomes"]),
            "finite_estimates_total":sum(len(r["outcomes"]) for r in final["records"]),
            "statuses":dict(statuses),"checks":audit["checks"],"final_cases":cases["scales"],
            "archive":[{"program":r["program"],"best_full_cost_log_score":r["best_full_cost_log_score"]} for r in archive["archive"]],
            "proof_scope":"all-scale signed operator identities, all-height root preservation and weighted inverse bounds; moment cancellation premises remain unproved",
            "uniform_sublinear_signed_controls_verified":[],"RH_proved":False,
            "verification_sha256":sha(directory/"verification.json"),"protocol_sha256":digest(spec)}


def publish(directory):
    directory=Path(directory).resolve(); result=summary(directory)
    write=json.dumps(result,indent=2)+"\n"; (directory/"summary.json").write_text(write)
    lines=["SIGNED SCALE POLYNOMIALS: FULL COST AND NONCONTRACTIVE GRAMMAR","",
           result["objective"],"Historical novelty is an annotation, not an acceptance gate.","",
           f"Generated {result['generated']} programs, including {result['automatic_compositions']} automatic composition proposals.",
           f"All-height disk certificates: {result['all_height_certified']}; outside the triangle domain: {result['certified_outside_triangle_domain']}.",
           f"Unsupported programs retained: {result['retained_without_available_global_certificate']}.",
           f"Independent checks: {sum(result['checks'].values())}/{len(result['checks'])}.",
           f"Exact complete final-window moments: {result['exact_complete_moment_values']}.",
           f"Finite estimates passed: {result['finite_estimates_passed']}/{result['finite_estimates_total']}.","",
           "Signed coefficients are learned or sampled without a stability projection.",
           "Rational Schur certificates permit polynomials beyond triangle contraction.",
           "The ranking charges the full inverse cost when estimating a bound on M.",
           "Development moments and delayed-positive controls are labelled sampled cells.",
           "Actual arithmetic final moments include every unit interval.","",
           "No sublinear uniform signed moment estimate is proved. RH remains unproved.",
           "All-scale operator safety is distinct from all-scale arithmetic cancellation.",
           "The limiting or alternative RH-sufficient arithmetic premise remains the target.","",
           "Proof: stable_scale_proof.txt. Detailed obligations: archive.json and final_evaluation.json.","",
           "Archived polynomial coefficients and full-cost scores:"]
    for row in result["archive"]:
        p=row["program"]; c=p["operator_certificate"]
        lines.append(f"{p['family']}: b={p['base']}, P={p['polynomial']}; all-height={c['all_height_critical_multiplier_certified']}; score={row['best_full_cost_log_score']}")
    (directory/"report.txt").write_text("\n".join(lines)+"\n")
    path=BASE/"stable-scale-results/latest.json"; path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps({"run_directory":str(directory),"summary_sha256":digest(result)},indent=2)+"\n")
    print("Published stable-scale search; uniform signed cancellation remains open",flush=True)
    return result


def load_latest():
    path=BASE/"stable-scale-results/latest.json"
    if not path.exists(): return {"status":"not_run","uniform_sublinear_signed_controls_verified":[],"RH_proved":False}
    pointer=read(path); result=summary(pointer["run_directory"])
    assert digest(result)==pointer["summary_sha256"]
    return result

#!/usr/bin/env python3
"""Strict publication of the primary direct-Mellin signed search."""
from collections import Counter
from fractions import Fraction as Q
import json
from pathlib import Path
from stable_scale_report import read,sha,digest,BASE


def summary(directory):
    directory=Path(directory).resolve(); spec=read(directory/"protocol.json"); audit=read(directory/"verification.json")
    seal=read(directory/"seal.json"); archive=read(directory/"archive.json"); final=read(directory/"final_evaluation.json")
    for name,expected in spec["code_sha256"].items(): assert sha(BASE/name)==expected
    for name,expected in seal["files"].items(): assert sha(directory/name)==expected
    assert audit["all_passed"] and all(audit["checks"].values())
    assert audit["protocol_sha256"]==digest(spec) and audit["final_sha256"]==sha(directory/"final_evaluation.json")
    assert audit["checker_sha256"]==sha(BASE/"check_mellin_search.py")
    assert audit["moment_verification_sha256"]==sha(directory/"moment_verification.json")
    cases=read(directory/"final_cases.json"); assert final["cases_sha256"]==digest(cases)
    assert final["seal_sha256"]==cases["seal_sha256"]==digest(seal)
    batch=read(directory/"candidate_batch.json"); data=read(directory/"validation_data.json")
    statuses=Counter(e["direct_mellin_transfer"]["status"] for r in data["records"] for e in r["estimates"])
    viable=[]; surviving=[]
    for r,z in zip(archive["archive"],final["records"]):
        assert r["program"]["id"]==z["program_id"]
        for e,o in zip(r["estimates"],z["outcomes"]):
            direct=e["direct_mellin_transfer"]
            if direct["status"]=="numerical_lead_missing_uniform_signed_moment_proof":
                leaf={"program":r["program"],"estimate":direct,"finite_windows_passed":o["finite_windows_passed"],
                      "complete_final_failure_windows":o["complete_final_failure_windows"]}
                viable.append(leaf)
                if o["finite_windows_passed"]: surviving.append(leaf)
    return {"status":"independently_verified_direct_Mellin_signed_search","run_directory":str(directory),
            "objective":spec["objective"],"historical_priority_is_acceptance_gate":False,
            "generated":len(batch["programs"]),"archived":len(archive["archive"]),
            "automatic_compositions":len(batch["promotions"]),"statuses":dict(statuses),"checks":audit["checks"],
            "coefficient_cutoff":audit["independent_full_inverse_coefficients"],
            "exact_complete_moment_values":audit["exact_complete_moment_values"],"final_cases":cases["scales"],
            "viable_archived_moment_obligations":len(viable),"viable_obligations_passing_fresh_windows":len(surviving),
            "RH_sufficient_obligations_passing_fresh_windows":sum(Q(r["estimate"]["certificate"]["mellin_exponent"])<=Q(1,2) for r in surviving),
            "surviving_uniform_proof_obligations":surviving,"viable_obligations":viable,
            "archive":[{"program":r["program"],"primary_mellin_score":r["primary_mellin_score"]} for r in archive["archive"]],
            "uniform_sublinear_signed_controls_verified":[],"RH_proved":False,
            "verification_sha256":sha(directory/"verification.json"),"protocol_sha256":digest(spec)}


def publish(directory):
    directory=Path(directory).resolve(); result=summary(directory)
    (directory/"summary.json").write_text(json.dumps(result,indent=2)+"\n")
    lines=["PRIMARY SIGNED SEARCH: DIRECT ORDINARY-ZETA MOMENT CONTROL","",
           "Rank uses eta=(beta-1)/q and the full quantitative reciprocal cost.",
           "A single fixed q with a proved uniform beta=q/2+1 bound would suffice for RH.",
           "Candidates with eta<1/2 and a certified nonzero critical-zero multiplier are rejected as proof leads; baseline and coverage controls remain labelled.","",
           f"Generated {result['generated']} programs; archived {result['archived']}.",
           f"Independent checks: {sum(result['checks'].values())}/{len(result['checks'])}.",
           f"Full arithmetic prefix: {result['coefficient_cutoff']}; exact complete final moments: {result['exact_complete_moment_values']}.",
           f"Viable archived moment obligations: {result['viable_archived_moment_obligations']}.",
           f"Viable obligations passing fresh windows: {result['viable_obligations_passing_fresh_windows']}.",
           f"RH-sufficient obligations passing fresh windows: {result['RH_sufficient_obligations_passing_fresh_windows']}.",
           json.dumps(result["statuses"],indent=2),"","Surviving uniform proof obligations:"]
    for row in result["surviving_uniform_proof_obligations"]:
        p=row["program"]; c=row["estimate"]["certificate"]
        lines.append(f"b={p['base']}, P={p['polynomial']}; q={c['order']}, beta={c['beta']}, eta={c['mellin_exponent']}, C={c['constant']}")
    lines.extend(["","No uniform arithmetic premise is proved by this pilot. RH remains unproved.",
                  "Complete-window verification is finite evidence. Proof templates: signed_mellin_proof.txt and stable_scale_proof.txt."])
    (directory/"report.txt").write_text("\n".join(lines)+"\n")
    path=BASE/"mellin-search-results/latest.json"; path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps({"run_directory":str(directory),"summary_sha256":digest(result)},indent=2)+"\n")
    print("Published direct-Mellin signed search; uniform proof premises remain open",flush=True)
    return result


def load_latest():
    path=BASE/"mellin-search-results/latest.json"
    if not path.exists(): return {"status":"not_run","uniform_sublinear_signed_controls_verified":[],"RH_proved":False}
    pointer=read(path); result=summary(pointer["run_directory"])
    assert digest(result)==pointer["summary_sha256"]
    return result

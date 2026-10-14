#!/usr/bin/env python3
"""Publish precisely scoped learned global signed-defect obligations."""
from collections import Counter
from pathlib import Path
import json
from stable_scale_report import read,sha,digest,BASE


def summary(directory):
    directory=Path(directory).resolve(); spec=read(directory/"protocol.json"); audit=read(directory/"verification.json")
    seal=read(directory/"seal.json"); archive=read(directory/"archive.json"); final=read(directory/"final_evaluation.json")
    assert audit["all_passed"] and all(audit["checks"].values())
    assert audit["protocol_sha256"]==digest(spec) and audit["source_final_sha256"]==sha(directory/"final_evaluation.json")
    assert audit["checker_sha256"]==sha(BASE/"check_signed_defects.py")
    for name,expected in spec["code_sha256"].items(): assert sha(BASE/name)==expected
    for name,expected in seal["files"].items(): assert sha(directory/name)==expected
    assert final["seal_sha256"]==digest(seal) and final["cases_sha256"]==digest(read(directory/"final_cases.json"))
    source=Path(spec["source_run"])
    assert sha(source/"archive.json")==spec["source_archive_sha256"] and sha(source/"verification.json")==spec["source_verification_sha256"]
    validation=read(directory/"validation_data.json")["candidates"]
    statuses=Counter(c["analytic_status"] for c in validation); survivors=[]
    programs={p["id"]:p for p in spec["input_operators"]}
    for c,out in zip(archive["archive"],final["outcomes"]):
        assert c["id"]==out["candidate_id"]
        if c["analytic_status"]=="RH_sufficient_recurrence_missing_uniform_arithmetic_proof" and out["finite_windows_passed"]:
            survivors.append({"program":programs[c["program_id"]],"candidate":c,"outcome":out})
    return {"status":"independently_verified_signed_moment_defect_search","run_directory":str(directory),
            "operators":len(spec["input_operators"]),"recurrences_generated":len(validation),"archived":len(archive["archive"]),
            "orders":spec["orders"],"statuses":dict(statuses),"checks":audit["checks"],
            "exact_actual_moment_values_checked":audit["exact_actual_moment_values_checked"],
            "exact_delayed_positive_moment_values_checked":audit["exact_delayed_positive_moment_values_checked"],
            "complete_coefficient_cutoff":audit["complete_coefficient_cutoff"],
            "finite_archived_passes":sum(o["finite_windows_passed"] for o in final["outcomes"]),
            "RH_sufficient_recurrences_passing_fresh_windows":len(survivors),
            "source_final_data_is_development_only":True,"final_cases":read(directory/"final_cases.json")["scales"],
            "surviving_uniform_recurrence_obligations":survivors,
            "generic_magnitude_defect_bounds_proved":sum(c["generic_magnitude_premise_proved"] for c in validation),
            "uniform_sublinear_signed_controls_verified":[],"RH_proved":False,"historical_priority_is_acceptance_gate":False,
            "verification_sha256":sha(directory/"verification.json")}


def publish(directory):
    directory=Path(directory).resolve(); result=summary(directory)
    (directory/"summary.json").write_text(json.dumps(result,indent=2)+"\n")
    lines=["LEARNED SIGNED MOMENT DEFECTS: ALL-SCALE PROOF OBLIGATIONS","",
           "Recurrence parameters and positive defect exponents are inferred from exact arithmetic moments.",
           "No particular recurrence coefficient or expected growth exponent is nominated.",
           "Alternative exponent margins are retained; original Mobius sums are explicit baseline operators.",
           "The universal target is A_q(2X)-rho*A_q(X)<=B X^gamma for every integer X>=1.",
           "Integer-scale control implies the dyadic recurrence needed by the RH transfer theorem.","",
           f"Operators: {result['operators']}; moment orders: {result['orders']}.",
           f"Learned recurrence estimates: {result['recurrences_generated']}; archived: {result['archived']}.",
           f"Independent checks: {sum(result['checks'].values())}/{len(result['checks'])}.",
           f"Exact actual moment values checked: {result['exact_actual_moment_values_checked']}.",
           f"Exact delayed-positive control moment values checked: {result['exact_delayed_positive_moment_values_checked']}.",
           f"Complete inverse coefficient cutoff: {result['complete_coefficient_cutoff']}.",
           f"Finite archived recurrence passes: {result['finite_archived_passes']}/{result['archived']}.",
           f"RH-sufficient recurrences passing fresh windows: {result['RH_sufficient_recurrences_passing_fresh_windows']}.",
           json.dumps(result["statuses"],indent=2),"","Surviving RH-sufficient uniform recurrence obligations:"]
    for row in result["surviving_uniform_recurrence_obligations"]:
        p,c=row["program"],row["candidate"]
        lines.append(f"{p['family']} b={p['base']}, P={p['polynomial']}: q={c['order']}, rho={c['rho']}, gamma={c['gamma']}, B={c['B']}, origin={c['rho_origin']}")
    lines.extend(["","The unknown uniform signed recurrence premises remain unproved. RH remains unproved.",
                  "Generic magnitude certificates, when available, have exponent q+1 and do not meet the RH target.",
                  "Earlier source final cases are development evidence. This run's final cases were drawn after sealing with new OS entropy.",
                  "Proof template: signed_recurrence_proof.txt. Frozen protocol and independent audit: protocol.json and verification.json."])
    (directory/"report.txt").write_text("\n".join(lines)+"\n")
    path=BASE/"signed-defect-results/latest.json"; path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps({"run_directory":str(directory),"summary_sha256":digest(result)},indent=2)+"\n")
    print("Published signed-defect search; required uniform signed recurrences remain open",flush=True)
    return result


def load_latest():
    path=BASE/"signed-defect-results/latest.json"
    if not path.exists(): return {"status":"not_run","uniform_sublinear_signed_controls_verified":[],"RH_proved":False}
    pointer=read(path); result=summary(pointer["run_directory"])
    assert digest(result)==pointer["summary_sha256"]
    return result

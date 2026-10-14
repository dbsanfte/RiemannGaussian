"""Read-only strict loader for exhaustive finite evaluator extensions."""
import argparse
from pathlib import Path
import json
from check_prime_twists import read,sha,digest

BASE=Path(__file__).resolve().parent


def summary(directory):
    directory=Path(directory).resolve();spec=read(directory/"protocol.json");audit=read(directory/"verification.json")
    for name,h in spec["code_sha256"].items():assert sha(BASE/name)==h
    assert sha(directory/"frozen_source.py")==spec["code_sha256"]["prime_twist_coverage.py"]==audit["code_sha256"]
    assert audit["all_passed"] and all(audit["checks"].values()) and audit["protocol_sha256"]==digest(spec)
    source=Path(spec["source_run"])
    for name,key in (("verification.json","source_verification_sha256"),("archive.json","source_archive_sha256"),("final_evaluation.json","source_final_sha256")):
        assert sha(source/name)==spec[key]
    assert digest(read(source/"protocol.json"))==spec["source_protocol_sha256"]
    from prime_twist_report import summary as source_summary
    parent=source_summary(source)
    assert not spec["candidate_reselection_or_refitting"] and not spec["fresh_discovery_run"]
    assert spec["cumulative_prefixes_overlap_development_data"] and not audit["RH_proved"] and not audit["uniform_RH_sufficient_signed_controls_verified"]
    archive={r["candidate"]["id"]:r for r in parent["archive_results"]}
    points={r["candidate_id"]:r for r in audit["point_bound_records"]};moments={r["candidate_id"]:r for r in audit["moment_bound_records"]}
    assert set(points)==set(archive) and set(moments)=={r["id"] for r in spec["source_unfiltered_moment_obligations"]}
    N=spec["cutoff"];assert N==audit["exact_coefficients_checked"]>parent["complete_coefficient_cutoff"]
    assert all(r["comparisons"]==N for r in points.values()) and all(r["comparisons"]==N//2 for r in moments.values())
    assert audit["point_comparisons"]==len(points)*N and audit["moment_comparisons"]==len(moments)*(N//2)
    new_survivors=[];lost=[]
    for cid,record in points.items():
        row=archive[cid];assert record["analytic_status"]==row["candidate"]["analytic_status"]
        passed=record["failures"]==record["unresolved"]==0
        if passed and record["analytic_status"].startswith("RH_sufficient"):new_survivors.append({"source_candidate":row,"coverage":record})
        if row["final_outcome"]["finite_points_passed"] and not passed:lost.append({"source_candidate":row,"coverage":record})
    assert len(new_survivors)==audit["RH_sufficient_if_uniform_point_bounds_passing_every_tested_integer"]
    return {"status":"independently_audited_exhaustive_finite_prime_twist_coverage","run_directory":str(directory),
        "source_run":str(source),"checks":audit["checks"],"cutoff":N,"archived_point_bounds":len(points),
        "complete_point_comparisons":audit["point_comparisons"],"complete_window_starts":N//2,"complete_moment_comparisons":audit["moment_comparisons"],
        "point_bounds_passing_every_integer":audit["point_bounds_passing_every_tested_integer"],
        "RH_sufficient_if_uniform_point_bounds_passing_every_integer":len(new_survivors),
        "moment_bounds_passing_every_integer_window":audit["moment_bounds_passing_every_tested_integer_window"],
        "sparse_point_survivors_lost_under_exhaustive_coverage":len(lost),"lost_sparse_survivors":lost,
        "surviving_uniform_proof_obligations":new_survivors,"candidate_reselection_or_refitting":False,
        "fresh_discovery_run":False,"cumulative_prefixes_overlap_development_data":True,
        "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False,
        "verification_sha256":sha(directory/"verification.json")}


def publish(directory):
    directory=Path(directory).resolve();result=summary(directory)
    (directory/"summary.json").write_text(json.dumps(result,indent=2)+"\n")
    pointer=BASE/"prime-twist-coverage-results/latest.json"
    pointer.write_text(json.dumps({"run_directory":str(directory),"summary_sha256":digest(result)},indent=2)+"\n")
    print("Published exhaustive finite coverage:",result["RH_sufficient_if_uniform_point_bounds_passing_every_integer"],"RH-compatible leads; uniform proof missing",flush=True)


def load_latest():
    pointer=BASE/"prime-twist-coverage-results/latest.json"
    if not pointer.exists():return {"status":"not_run","uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    record=read(pointer);result=summary(record["run_directory"])
    assert digest(result)==record["summary_sha256"]
    return result


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--run-dir",type=Path,required=True)
    publish(parser.parse_args().run_dir)

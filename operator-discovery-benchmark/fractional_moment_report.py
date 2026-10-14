"""Strict publication of fractional powers and unproved signed RH obligations."""
from collections import Counter
import json
from pathlib import Path
from fractions import Fraction as Q
from stable_scale_report import read,sha,digest,BASE


def summary(directory):
    directory=Path(directory).resolve(); spec=read(directory/"protocol.json"); audit=read(directory/"verification.json")
    archive=read(directory/"archive.json"); final=read(directory/"final_evaluation.json"); seal=read(directory/"seal.json")
    assert audit["all_passed"] and all(audit["checks"].values())
    assert audit["protocol_sha256"]==digest(spec) and audit["source_final_sha256"]==sha(directory/"final_evaluation.json")
    assert audit["checker_sha256"]==sha(BASE/"check_fractional_moments.py")
    for name,expected in spec["code_sha256"].items(): assert sha(BASE/name)==expected
    for name,expected in seal["files"].items(): assert sha(directory/name)==expected
    assert final["seal_sha256"]==digest(seal) and final["cases_sha256"]==digest(read(directory/"final_cases.json"))
    source=Path(spec["source_run"])
    assert sha(source/"archive.json")==spec["source_archive_sha256"] and sha(source/"verification.json")==spec["source_verification_sha256"]
    candidates=read(directory/"validation_data.json")["candidates"]
    survivors=[]
    for c,o in zip(archive["archive"],final["outcomes"]):
        assert c["id"]==o["candidate_id"]
        if c["analytic_status"]=="RH_sufficient_obligation_missing_uniform_signed_proof" and o["finite_windows_passed"]:
            survivors.append(c)
    return {"status":"independently_verified_fractional_power_and_moment_search","run_directory":str(directory),
        "operators":len(spec["input_operators"]),"effective_orders":spec["orders"],"max_denominator_in_run":spec["max_denominator"],
        "semantic_denominator_ceiling":None,"estimates_generated":len(candidates),"archived":len(archive["archive"]),
        "archived_root_exponents":sorted({c["root_exponent"] for c in archive["archive"]},key=Q),
        "statuses":dict(Counter(c["analytic_status"] for c in candidates)),"checks":audit["checks"],
        "certified_actual_moment_values_checked":audit["certified_actual_moment_values_checked"],
        "certified_delayed_positive_values_checked":audit["certified_delayed_positive_values_checked"],
        "exact_Dirichlet_coefficients_checked":audit["exact_Dirichlet_coefficients_checked"],"native_zeta_root_checks":audit["native_zeta_root_checks"],
        "complete_coefficient_cutoff":audit["complete_coefficient_cutoff"],
        "finite_archived_passes":sum(o["finite_windows_passed"] for o in final["outcomes"]),
        "RH_sufficient_obligations_passing_fresh_windows":len(survivors),"surviving_uniform_obligations":survivors,
        "uniform_sublinear_signed_controls_verified":[],"RH_proved":False,"historical_priority_is_acceptance_gate":False,
        "fractional_moments_are_exact_rationals":False,"coefficient_Dirichlet_roots_are_exact_rationals":True,
        "verification_sha256":sha(directory/"verification.json")}


def publish(directory):
    directory=Path(directory).resolve(); result=summary(directory)
    (directory/"summary.json").write_text(json.dumps(result,indent=2)+"\n")
    lines=["RATIONAL ROOTS AND FRACTIONAL SIGNED MOMENTS TOWARD RH","",
        "Pointwise real, signed and absolute powers and declared complex branches have distinct semantics.",
        "Dirichlet rational powers use the existing exact coefficient backend, independently audited by log/exp.",
        "The proof search audits root recovery: a root moment is tested at its effective order on the original signed residual.",
        "Whole-window fractional moments are certified algebraic balls, not sampled quadrature or exact rational values.",
        "Holder transfer is used only for effective order >=1; orders below one have an explicit Lipschitz loss.","",
        f"Effective orders: {result['effective_orders']}",f"Archived root exponents: {result['archived_root_exponents']}",
        f"Input operators: {result['operators']}; inferred estimates: {result['estimates_generated']}; archived: {result['archived']}.",
        f"Independent checks: {sum(result['checks'].values())}/{len(result['checks'])}.",
        f"Certified actual moment values independently recomputed: {result['certified_actual_moment_values_checked']}.",
        f"Exact independently checked Dirichlet coefficients: {result['exact_Dirichlet_coefficients_checked']}.",
        f"Native zeta fractional-root checks with proved tails: {result['native_zeta_root_checks']}.",
        f"Fresh finite archive passes: {result['finite_archived_passes']}/{result['archived']}.",
        f"RH-sufficient obligations passing fresh windows: {result['RH_sufficient_obligations_passing_fresh_windows']}.",
        json.dumps(result['statuses'],indent=2),"","Surviving uniform RH proof obligations:"]
    for c in result["surviving_uniform_obligations"]:
        lines.append(f"q={c['effective_order']}, root={c['root_exponent']}, outer={c['outer_moment_order']}, beta={c['beta']}, C={c['constant']}; program={c['program_id']}")
    lines.extend(["","A smaller root amplitude is not extra cancellation. The inverse and effective moment order remain in the certificate.",
        "The uniform signed arithmetic premises are unproved. RH remains unproved.",
        "Finite root recovery and the Dirichlet-series convergence theorem do not close the signed RH obligation.",
        "Proof and domains: rational_power_proof.txt. Frozen protocol, cases and independent audit are retained in this directory."])
    (directory/"report.txt").write_text("\n".join(lines)+"\n")
    pointer=BASE/"fractional-moment-results/latest.json"; pointer.parent.mkdir(exist_ok=True)
    pointer.write_text(json.dumps({"run_directory":str(directory),"summary_sha256":digest(result)},indent=2)+"\n")
    print("Published fractional-power search; all-scale signed premises remain open",flush=True)
    return result


def load_latest():
    path=BASE/"fractional-moment-results/latest.json"
    if not path.exists(): return {"status":"not_run","uniform_sublinear_signed_controls_verified":[],"RH_proved":False}
    pointer=read(path); result=summary(pointer["run_directory"]); assert digest(result)==pointer["summary_sha256"]
    return result

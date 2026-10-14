#!/usr/bin/env python3
"""Independent full-moment audit plus the direct-Mellin selection audit."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import subprocess
import sys
import flint

from check_stable_scale import main as check_moments, read, sha, digest, BASE
from check_signed_mellin_transfer import zero_disk, independent_bound, real


def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--run-dir",type=Path,required=True)
    args=parser.parse_args(); directory=args.run_dir.resolve(); spec=read(directory/"protocol.json")
    # Replay uses the new selector, then the existing independent moment audit
    # checks the replay hashes. The old checker never generates a different
    # selector's replay. Mathematical audits still import no production code.
    replay=directory/"replay"
    if not replay.exists():
        replay.mkdir(); (replay/"protocol.json").write_bytes((directory/"protocol.json").read_bytes())
        subprocess.run([sys.executable,str(BASE/"mellin_search.py"),"discover","--run-dir",str(replay)],check=True,cwd=BASE)
    check_moments()
    old=read(directory/"verification.json")
    (directory/"moment_verification.json").write_text(json.dumps(old,indent=2)+"\n")
    flint.ctx.prec=768; archive=read(directory/"archive.json"); z,margin=zero_disk(archive["known_zero_dependency"])
    validation=read(directory/"validation_data.json")["records"]
    for row in validation:
        p=row["program"]; cert=p["operator_certificate"]; base=p["base"]
        w=(-z*real(base).log()).exp(); F=flint.acb(0)
        for c in reversed(p["polynomial"]): F=F*w+real(Q(c))
        nonzero=bool(F.abs_lower()>0); all_height=cert["all_height_critical_multiplier_certified"]
        scores=[]
        for e in row["estimates"]:
            direct=e["direct_mellin_transfer"]; leaf=direct["certificate"]
            q,beta,C=e["order"],Q(e["beta"]),Q(e["constant"]); eta=(beta-1)/q
            assert leaf["order"]==q and Q(leaf["beta"])==beta and Q(leaf["constant"])==C
            assert Q(leaf["mellin_exponent"])==eta
            assert leaf["RH_sufficient_if_uniform_and_all_height_multiplier_nonzero"]==(eta<=Q(1,2))
            assert not leaf["uniform_signed_moment_premise_proved"] and not leaf["RH_proved"]
            if nonzero and eta<Q(1,2): status="ruled_out_by_actual_zeta_zero"
            elif e["sampled_validation_failure_windows"]: status="failed_sampled_validation"
            elif not all_height: status="numerical_lead_missing_global_multiplier_and_uniform_proof"
            else: status="numerical_lead_missing_uniform_signed_moment_proof"
            assert direct["status"]==status and direct["critical_zero_multiplier_nonzero"]==nonzero
            if status=="numerical_lead_missing_uniform_signed_moment_proof":
                delta=Q(cert["selected_schur_certificate"]["uniform_multiplier_lower_bound"])
                assert Q(direct["global_multiplier_lower_bound"])==delta
                sigma=eta+Q(1,8); assert Q(direct["cost_line"])==sigma
                bound=independent_bound(cert["atoms"],delta,q,beta,C,sigma)
                assert flint.arb(direct["conditional_reciprocal_bound_ball"]).contains(bound)
                assert abs(float(bound.upper().log())-direct["log_cost"])<1e-10
                scores.append((eta,direct["log_cost"],q))
        expected=None
        if scores:
            best=min(scores); expected=[str(best[0]),best[1],best[2]]
        assert row["primary_mellin_score"]==expected
    assert not archive["final_data_used"]
    checks=dict(old["checks"])
    checks.update({"primary_direct_Mellin_exponent_and_actual_zero_obstruction_checked":True,
                   "quantitative_reciprocal_cost_and_primary_rank_checked":True,
                   "new_selector_replayed_before_reusing_independent_moment_checker":True})
    result={"all_passed":True,"checks":checks,"exact_complete_moment_values":old["exact_complete_moment_values"],
            "independent_full_inverse_coefficients":old["independent_full_inverse_coefficients"],
            "moment_verification_sha256":sha(directory/"moment_verification.json"),
            "final_sha256":sha(directory/"final_evaluation.json"),"protocol_sha256":digest(spec),
            "checker_sha256":sha(Path(__file__)),"independent_nested_Rouche_margin":margin,
            "mathematical_audit_imports_production_code":False,"replay_invokes_production_generator":True,
            "uniform_sublinear_signed_controls_verified":[],"RH_proved":False}
    (directory/"verification.json").write_text(json.dumps(result,indent=2)+"\n")
    print("Independent direct-Mellin search audit",sum(checks.values()),"/",len(checks),flush=True)


if __name__=="__main__": main()

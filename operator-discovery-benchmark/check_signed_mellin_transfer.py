#!/usr/bin/env python3
"""Independent direct-Mellin exponent, cost and ordinary-zero audit."""
from collections import Counter
from fractions import Fraction as Q
import argparse
import hashlib
import json
from pathlib import Path
import flint

BASE=Path(__file__).resolve().parent


def read(path): return json.loads(Path(path).read_text())
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def digest(data): return hashlib.sha256(json.dumps(data,sort_keys=True,separators=(",", ":"),allow_nan=False).encode()).hexdigest()
def real(x): x=Q(x); return flint.arb(x.numerator)/x.denominator


def zero_disk(dependency):
    assert Q(dependency["centre"][0])==Q(1,2)
    old=BASE/"shift-ratio-results/shift_ratio_analytic_verification.json"; data=read(old)
    assert data["all_passed"] and sha(old)==dependency["verification_sha256"]
    assert data["source_artifact_sha256"]==sha(BASE/"shift-ratio-results/shift_ratio_analytic.json")==dependency["source_sha256"]
    centre=flint.acb(real(Q(1,2)),dependency["centre"][1]); radius=real(Q(dependency["radius"])/8)
    rectangle=centre+flint.acb(flint.arb(0,radius),flint.arb(0,radius)); flint.ctx.cap=24
    derivatives=flint.acb_series([centre,1],prec=2).zeta()
    second=2*flint.acb_series([rectangle,1],prec=3).zeta()[2]
    margin=derivatives[1].abs_lower()*radius-centre.zeta().abs_upper()-second.abs_upper()*radius*radius/2
    assert margin>0
    return rectangle,margin.str(40)


def independent_bound(atoms,delta,q,beta,C,sigma):
    # Reconstruct the Holder exponent from the three separate powers of X.
    eta=beta/Q(q)+Q(1)-Q(1,q)-1
    assert eta==(beta-1)/q and sigma>eta and sigma>0
    ratio=real(2)**real(eta-sigma)
    norm=real(C)**real(Q(1,q))
    tail=norm/(1-ratio)
    # Check the geometric majorant also covers a finite 64-block prefix.
    assert sum((norm*ratio**j for j in range(64)),flint.arb(0))<tail
    compact=flint.arb(0)
    for d,a in atoms:
        if sigma==1:
            correction=real(d).log()/d
        else:
            correction=(real(d)**real(-sigma)-real(Q(1,d)))/real(1-sigma)
        compact+=real(abs(Q(a)))*correction
    return tail/real(delta)+compact/real(delta)+1/real(sigma)


def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--run-dir",type=Path,required=True)
    args=parser.parse_args(); directory=args.run_dir.resolve(); flint.ctx.prec=768
    spec,data=read(directory/"protocol.json"),read(directory/"transfer_audit.json")
    assert data["protocol_sha256"]==digest(spec)
    for name,expected in spec["code_sha256"].items(): assert sha(BASE/name)==expected
    sources={}; all_source_ids=[]; source_zero={}; margins=[]
    for source in spec["sources"]:
        path=Path(source["run_directory"]); sources[str(path)]=source
        for name,expected in source["files"].items(): assert sha(path/name)==expected
        audit=read(path/"verification.json"); assert audit["all_passed"] and all(audit["checks"].values())
        original_spec=read(path/"protocol.json"); seal=read(path/"seal.json")
        for name,expected in original_spec["code_sha256"].items(): assert sha(BASE/name)==expected
        for name,expected in seal["files"].items(): assert sha(path/name)==expected
        actual_final_sha=sha(path/"final_evaluation.json")
        assert actual_final_sha==audit.get("final_sha256",audit.get("source_final_sha256"))
        archive=read(path/"archive.json"); source_zero[str(path)],margin=zero_disk(archive["known_zero_dependency"]); margins.append(margin)
        validation=read(path/"validation_data.json")["records"]
        for r in validation: all_source_ids.append((str(path),r["program"]["id"]))
    assert [(r["source_run"],r["program_id"]) for r in data["records"]]==all_source_ids
    assert len(data["zero_audits"])==len(sources)
    statuses=Counter(); finite_false=finite_true=0; records_by_key={}
    for row in data["records"]:
        source=row["source_run"]; path=Path(source); program=row["program"]; p=program.get("polynomial")
        original=next(r for r in read(path/"validation_data.json")["records"] if r["program"]["id"]==row["program_id"])
        assert program==original["program"]
        cert=program["operator_certificate"]; atoms=cert["atoms"]; z=source_zero[source]
        if p is not None:
            # Horner in b^(-s); production adds individual d^(-s) terms.
            base=program["base"]; w=(-z*real(base).log()).exp(); F=flint.acb(0)
            for c in reversed(p): F=F*w+real(Q(c))
            all_height=cert["all_height_critical_multiplier_certified"]
            delta=Q(cert["selected_schur_certificate"]["uniform_multiplier_lower_bound"]) if all_height else None
        else:
            F=1+sum((real(-Q(a))*real(d)**(-z) for d,a in atoms),flint.acb(0))
            all_height=cert["nonvanishing_multiplier_Re_s_ge_half_certified"]
            delta=None
        nonzero=bool(F.abs_lower()>0)
        assert row["critical_zero_multiplier_nonzero"]==nonzero
        assert row["all_height_multiplier_nonzero"]==all_height
        assert len(row["estimates"])==len(original["estimates"])
        final=read(path/"final_evaluation.json"); old_final=next((r for r in final["records"] if r["program_id"]==row["program_id"]),None)
        for e,old in zip(row["estimates"],original["estimates"]):
            transfer=e["certificate"]; q,beta,C=old["order"],Q(old["beta"]),Q(old["constant"])
            assert transfer["order"]==q and Q(transfer["beta"])==beta and Q(transfer["constant"])==C
            eta=(beta-1)/q
            assert Q(transfer["mellin_exponent"])==eta
            assert transfer["RH_sufficient_if_uniform_and_all_height_multiplier_nonzero"]==(eta<=Q(1,2))
            assert transfer["contradicted_if_critical_zero_multiplier_nonzero"]==(eta<Q(1,2))
            assert not transfer["uniform_signed_moment_premise_proved"] and not transfer["RH_proved"]
            impossible=nonzero and eta<Q(1,2)
            expected=("uniform_estimate_ruled_out_by_actual_zeta_zero" if impossible else
                      "numerical_lead_missing_uniform_signed_moment_proof" if all_height else
                      "numerical_lead_missing_global_multiplier_and_uniform_moment_proof")
            assert e["status"]==expected; statuses[expected]+=1
            if all_height:
                supplied_delta=Q(e["global_multiplier_lower_bound"])
                if p is not None: assert supplied_delta==delta
                else:
                    triangle=sum((real(abs(Q(a)))/real(d).sqrt() for d,a in atoms),flint.arb(0))
                    assert real(supplied_delta)<=1-triangle and supplied_delta>0
                if not impossible:
                    sigma=Q(e["reciprocal_test_line"])
                    assert sigma==max(Q(3,4),eta+Q(1,16))
                    bound=independent_bound(atoms,supplied_delta,q,beta,C,sigma)
                    assert flint.arb(e["conditional_reciprocal_bound_ball"]).contains(bound)
            else: assert e["global_multiplier_lower_bound"] is None
            if old_final is not None:
                outcomes=old_final["outcomes"] if p is not None else old_final["estimate_outcomes"]
                outcome=next(o for o in outcomes if o["order"]==q)
                passed=outcome["finite_windows_passed"] if p is not None else outcome["finite_validation_passed"]
                assert e["original_final_windows_passed"]==passed
                if impossible: finite_false+=int(passed)
                elif passed: finite_true+=1
        records_by_key[source,row["program_id"]]=row
    for row in data["archived_records"]:
        assert row==records_by_key[row["source_run"],row["program_id"]]
    expected_archived=[(s["run_directory"],r["program"]["id"]) for s in spec["sources"]
                       for r in read(Path(s["run_directory"])/"archive.json")["archive"]]
    assert [(r["source_run"],r["program_id"]) for r in data["archived_records"]]==expected_archived
    assert dict(statuses)==data["statuses"]
    assert finite_false==data["archived_estimates_passing_finite_windows_but_globally_ruled_out"]
    assert finite_true==data["archived_estimates_passing_finite_windows_without_this_obstruction"]
    assert data["no_candidate_reselection"] and data["no_fresh_finite_validation_claim"]
    assert not data["RH_proved"] and data["uniform_sublinear_signed_controls_verified"]==[]
    checks={"source_code_archive_final_moment_and_previous_independent_audit_provenance":True,
            "direct_Holder_exponent_and_dyadic_geometric_cost_checked":True,
            "independent_actual_zero_disk_and_Horner_multiplier_obstructions":True,
            "all_height_multiplier_cost_and_compact_interpolation_correction_checked":True,
            "single_fixed_order_RH_sufficiency_kept_conditional":True,
            "all_generated_estimates_reclassified_without_reselection_or_new_held_out_claim":True}
    result={"all_passed":True,"checks":checks,"programs_checked":len(data["records"]),
            "estimates_checked":sum(len(r["estimates"]) for r in data["records"]),
            "independent_nested_Rouche_margins":margins,"source_sha256":sha(directory/"transfer_audit.json"),
            "protocol_sha256":digest(spec),"checker_sha256":sha(Path(__file__)),
            "proof_sha256":sha(BASE/"signed_mellin_proof.txt"),"mathematical_audit_imports_production_code":False,
            "classical_dependencies":["Holder inequality", "dominated holomorphy of Mellin transforms", "Rouche theorem", "ordinary-zeta functional equation and zero reflection"],
            "uniform_signed_moment_premises_proved":[],"RH_proved":False}
    (directory/"verification.json").write_text(json.dumps(result,indent=2)+"\n")
    print("Independent direct signed-moment audit",sum(checks.values()),"/",len(checks),flush=True)


if __name__=="__main__": main()

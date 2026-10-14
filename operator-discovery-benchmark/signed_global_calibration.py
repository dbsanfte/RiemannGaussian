#!/usr/bin/env python3
"""Named signed all-scale calibration, separately scoped below RH strength."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import subprocess
import sys
import flint
from estimate_grammar import inverse_one_prefix
from signed_control_grammar import prefix
from stable_scale_search import BASE,read,write,sha,digest

CODE=["signed_global_calibration.py","check_signed_global_calibration.py","signed_global_calibration_proof.txt"]
PDF="literature/signed-global/ramare_zuniga_2024_v2.pdf"
def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def produce(directory,source):
    from mellin_search_report import summary as source_summary
    source=Path(source).resolve();source_summary(source)
    if directory.exists():raise ValueError("A fresh calibration directory is required")
    directory.mkdir(parents=True);old=read(source/"protocol.json")
    hashes=dict(old["code_sha256"]);hashes.update({n:sha(BASE/n) for n in CODE})
    spec={"purpose":"imported global signed calibration with independent complete finite patch; not a new arithmetic theorem or RH bound",
        "code_sha256":hashes,"source_run":str(source),"source_archive_sha256":sha(source/"archive.json"),"source_verification_sha256":sha(source/"verification.json"),
        "operators":[r["program"] for r in read(source/"archive.json")["archive"]],"precision":320,
        "imported_dependency":{"title":"From explicit estimates for the primes to explicit estimates for the Mobius function II",
            "authors":["Olivier Ramare","Sebastian Zuniga Alterman"],"version":"arXiv:2408.05969v2",
            "url":"https://arxiv.org/pdf/2408.05969v2","pdf_path":PDF,"pdf_sha256":sha(BASE/PDF),
            "theorem":"Theorem 1.1","threshold":1798118,"coarse_constant":"418/62500",
            "statement":"|M(x)| <= (0.006688 log x - 0.039) x/log(x)^2 for all real x>=1798118",
            "analytic_source_proof_independently_reproved":False},
        "training_cutoff":1024,"constant_grid_denominator":64,
        "constant_inference":"maximum |M(n)| log(e+n)/n, upward rational rounding; no nominated constant",
        "finite_patch_scope":"every integer through the imported threshold; exact M(n)^2<=n",
        "coefficient_producer":"factor-free constant-one Dirichlet inversion","checker_coefficient_source":"independent prime sieve",
        "historical_priority_is_acceptance_gate":False,"RH_proved":False}
    write(directory/"protocol.json",spec);flint.ctx.prec=spec["precision"]
    training=inverse_one_prefix(spec["training_cutoff"]);M=prefix(training); e=real(1).exp()
    top=max((real(abs(M[n]))*(e+n).log()/n).upper() for n in range(1,len(M)))
    C=Q(int((top*spec["constant_grid_denominator"]).ceil().fmpz()),spec["constant_grid_denominator"])
    write(directory/"learned_constant.json",{"constant":str(C),"training_coefficient_sha256":digest(training),"frozen_before_full_patch":True})
    T=spec["imported_dependency"]["threshold"];mu=inverse_one_prefix(T);M=prefix(mu)
    failures=[n for n in range(1,T+1) if M[n]*M[n]>n]
    assert not failures
    assert C>=1 and real(C)>=(e+1).log() and real(C)>=real(abs(M[3]))*(e+3).log()/3
    assert 2>(e+4).log()
    required=real(Q(spec["imported_dependency"]["coarse_constant"]))*(1+e/(real(T)*real(T).log()))
    assert real(C)>=required
    operators=[]
    for p in spec["operators"]:
        cost=sum((real(abs(Q(c)))*(1+real(p["base"]**j).log())/p["base"]**j for j,c in enumerate(p["polynomial"])),flint.arb(0))
        K=real(C)*cost
        slope=sum((Q(c)/p["base"]**j for j,c in enumerate(p["polynomial"])),Q(0))
        operators.append({"program_id":p["id"],"constant_ball":K.str(45),"uniform_bound":"|R(t)|<=K*t/log(e+t) for every real t>=0",
            "universal_signed_control_is_imported_consequence":True,"extra_filter_cancellation_proved":False,
            "positive_and_delayed_positive_uniform_claims_false":bool(slope),"RH_sufficient":False})
    write(directory/"calibration.json",{"protocol_sha256":digest(spec),"constant":str(C),"complete_coefficient_cutoff":T,
        "inverse_coefficient_sha256":digest(mu),"finite_sqrt_patch_failures":failures,"large_range_required_constant_ball":required.str(45),
        "operators":operators,"uniform_bound":"|M_tilde(t)|<=C*t/log(e+t) for every real t>=0",
        "universal_moment_consequence":"A_q(X)<=(2K)^q*X^(q+1)/log(e+X)^q for every rational q>0 and real X>=1",
        "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False})
    subprocess.run([sys.executable,str(BASE/"check_signed_global_calibration.py"),"--run-dir",str(directory)],check=True,cwd=BASE)
    publish(directory)


def summary(directory):
    directory=Path(directory).resolve();spec=read(directory/"protocol.json");data=read(directory/"calibration.json");audit=read(directory/"verification.json")
    assert audit["all_passed"] and all(audit["checks"].values()) and audit["protocol_sha256"]==digest(spec)
    assert audit["source_sha256"]==sha(directory/"calibration.json") and audit["checker_sha256"]==sha(BASE/"check_signed_global_calibration.py")
    for n,h in spec["code_sha256"].items():assert sha(BASE/n)==h
    dep=spec["imported_dependency"];assert sha(BASE/dep["pdf_path"])==dep["pdf_sha256"]
    source=Path(spec["source_run"]);assert sha(source/"archive.json")==spec["source_archive_sha256"] and sha(source/"verification.json")==spec["source_verification_sha256"]
    return {"status":"verified_imported_signed_global_calibration_with_independent_finite_patch","run_directory":str(directory),"checks":audit["checks"],
        "constant":data["constant"],"uniform_bound":data["uniform_bound"],"imported_dependency":dep,
        "independent_complete_coefficient_cutoff":data["complete_coefficient_cutoff"],"operators":data["operators"],
        "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False,"verification_sha256":sha(directory/"verification.json")}


def publish(directory):
    directory=Path(directory);r=summary(directory);write(directory/"summary.json",r)
    (directory/"report.txt").write_text("SIGNED ALL-SCALE CALIBRATION: IMPORTED PROOF DEPENDENCY\n\n"
        f"Independent checks: {sum(r['checks'].values())}/{len(r['checks'])}.\n"
        f"Every mu coefficient and exact square-root finite patch through {r['independent_complete_coefficient_cutoff']} independently checked.\n"
        f"Inferred constant C={r['constant']}: {r['uniform_bound']}.\n"
        "The infinite range relies on Ramare and Zuniga Alterman, arXiv:2408.05969v2, Theorem 1.1.\n"
        "The detector does not independently re-prove that source's analytic argument or imported prime estimates.\n"
        "The eight signed residuals inherit global logarithmic bounds with their full dilation costs.\n"
        "These are genuine signed o(t) bounds, below RH strength; they do not verify new independent prime information.\n"
        "No RH-sufficient uniform signed estimate and no RH proof have been obtained.\n")
    path=BASE/"signed-global-results/latest.json";path.parent.mkdir(exist_ok=True);write(path,{"run_directory":str(directory.resolve()),"summary_sha256":digest(r)})
    print("Published imported all-scale signed calibration, below RH strength",flush=True)


def load_latest():
    path=BASE/"signed-global-results/latest.json"
    if not path.exists():return {"status":"not_run","uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    pointer=read(path);r=summary(pointer["run_directory"]);assert digest(r)==pointer["summary_sha256"];return r


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--run-dir",type=Path,required=True);parser.add_argument("--source-run",type=Path,required=True)
    a=parser.parse_args();produce(a.run_dir.resolve(),a.source_run)

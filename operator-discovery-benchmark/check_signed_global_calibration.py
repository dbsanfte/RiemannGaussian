#!/usr/bin/env python3
"""Independent finite arithmetic and exact imported-bound scope audit."""
import argparse
from fractions import Fraction as Q
import hashlib,json
from pathlib import Path
import flint
from check_signed_control import independent_inverse

BASE=Path(__file__).resolve().parent
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(data):return hashlib.sha256(json.dumps(data,sort_keys=True,separators=(",",":"),allow_nan=False).encode()).hexdigest()
def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--run-dir",type=Path,required=True)
    directory=parser.parse_args().run_dir.resolve();spec=read(directory/"protocol.json");data=read(directory/"calibration.json")
    for n,h in spec["code_sha256"].items():assert sha(BASE/n)==h
    dep=spec["imported_dependency"]
    assert dep["version"]=="arXiv:2408.05969v2" and dep["theorem"]=="Theorem 1.1" and dep["threshold"]==1798118
    assert Q(dep["coarse_constant"])==Q(6688,1000000) and sha(BASE/dep["pdf_path"])==dep["pdf_sha256"]
    assert not dep["analytic_source_proof_independently_reproved"]
    assert data["protocol_sha256"]==digest(spec)
    source=Path(spec["source_run"]);assert sha(source/"archive.json")==spec["source_archive_sha256"] and sha(source/"verification.json")==spec["source_verification_sha256"]
    assert spec["operators"]==[r["program"] for r in read(source/"archive.json")["archive"]]
    flint.ctx.prec=640;T=dep["threshold"];mu,M=independent_inverse(T)
    assert data["complete_coefficient_cutoff"]==T and data["inverse_coefficient_sha256"]==digest(mu)
    assert all(M[n]**2<=n for n in range(1,T+1)) and not data["finite_sqrt_patch_failures"]
    learned=read(directory/"learned_constant.json");assert learned["frozen_before_full_patch"]
    assert learned["training_coefficient_sha256"]==digest(mu[:spec["training_cutoff"]+1])
    e=real(1).exp();top=max((real(abs(M[n]))*(e+n).log()/n).upper() for n in range(1,spec["training_cutoff"]+1))
    denominator=spec["constant_grid_denominator"];C=Q(int((top*denominator).ceil().fmpz()),denominator)
    assert Q(data["constant"])==Q(learned["constant"])==C>=1
    for n in (1,2,3):assert real(abs(M[n]))*(e+n).log()<=real(C*n)
    assert (e+4).log()<2 and e>1
    required=real(Q(dep["coarse_constant"]))*(1+e/(real(T)*real(T).log()))
    assert real(C)>=required and flint.arb(data["large_range_required_constant_ball"]).contains(required)
    assert len(data["operators"])==len(spec["operators"])
    for p,r in zip(spec["operators"],data["operators"]):
        cost=flint.arb(0);slope=Q(0)
        for j,c in enumerate(p["polynomial"]):
            d=p["base"]**j;cost+=real(abs(Q(c))/d)*(1+real(d).log());slope+=Q(c)/d
        assert r["program_id"]==p["id"] and flint.arb(r["constant_ball"]).contains(real(C)*cost)
        assert r["universal_signed_control_is_imported_consequence"] and not r["extra_filter_cancellation_proved"] and not r["RH_sufficient"]
        assert r["positive_and_delayed_positive_uniform_claims_false"]==bool(slope)
    assert not data["RH_proved"] and not data["uniform_RH_sufficient_signed_controls_verified"]
    checks={"frozen_sources_and_precise_named_import_scope_checked":True,"every_finite_patch_coefficient_and_sqrt_inequality_independently_checked":True,
        "training_constant_independently_relearned_before_full_patch":True,"threshold_coverage_and_concave_interpolation_proof_constants_checked":True,
        "all_scale_signed_dilation_costs_and_positive_controls_checked":True,"below_RH_strength_and_external_dependency_retained":True}
    result={"all_passed":True,"checks":checks,"protocol_sha256":digest(spec),"source_sha256":sha(directory/"calibration.json"),
        "checker_sha256":sha(Path(__file__)),"independent_complete_coefficient_cutoff":T,
        "external_analytic_proof_independently_reproved":False,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    (directory/"verification.json").write_text(json.dumps(result,indent=2)+"\n")
    print("Independent imported signed calibration audit",sum(checks.values()),"/",len(checks),flush=True)


if __name__=="__main__":main()

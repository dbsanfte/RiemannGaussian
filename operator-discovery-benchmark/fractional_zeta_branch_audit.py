#!/usr/bin/env python3
"""Certified local branch gate for fractional ordinary-zeta operators."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import subprocess
import sys
import flint

from stable_scale_search import read,write,sha,digest,BASE
from signed_mellin_transfer import known_zero_rectangle
from rational_power_grammar import real

CODE=["fractional_zeta_branch_audit.py","check_fractional_zeta_branches.py","fractional_zeta_branch_proof.txt"]


def contour(radius, subdivisions, tolerance_bits):
    r=real(radius); c=flint.acb(1)
    vertices=[c+flint.acb(-r,-r),c+flint.acb(r,-r),c+flint.acb(r,r),c+flint.acb(-r,r)]
    edges=[]; boundary=[]; total=flint.acb(0)
    def logarithmic_derivative(z, analytic):
        # Meromorphic operations return nonfinite balls when an analytic
        # test disk includes a singularity; native integration subdivides.
        return flint.acb_series([z,1],prec=2).zeta()[1]/z.zeta()
    for i,start in enumerate(vertices):
        end=vertices[(i+1)%4]
        for j in range(subdivisions):
            left=start+(end-start)*real(Q(j,subdivisions))
            right=start+(end-start)*real(Q(j+1,subdivisions))
            midpoint=(left+right)/2; half=(right-left)/2
            segment=midpoint+flint.acb(flint.arb(0,abs(half.real).upper()),flint.arb(0,abs(half.imag).upper()))
            lower=segment.zeta().abs_lower(); assert lower>0
            boundary.append({"edge":i,"cell":j,"zeta_abs_lower_ball":lower.str(45)})
        integral=flint.acb.integral(logarithmic_derivative,start,end,
            abs_tol=real(Q(1,2**tolerance_bits)),rel_tol=real(Q(1,2**tolerance_bits)),eval_limit=20000,depth_limit=30)
        assert integral.is_finite(); total+=integral
        edges.append([integral.real.str(45),integral.imag.str(45)])
    winding=total/(2*flint.arb.pi()*flint.acb(0,1))
    assert winding.is_finite() and winding.imag.contains(0) and abs(winding.imag).upper()<real(Q(1,8))
    lo=int(winding.real.lower().ceil().fmpz()); hi=int(winding.real.upper().floor().fmpz())
    assert lo==hi
    return {"radius":str(radius),"boundary_cells":boundary,"edge_integral_balls":edges,
        "winding_ball":[winding.real.str(45),winding.imag.str(45)],"unique_integer_winding":lo,
        "known_enclosed_poles":1,"enclosed_zeros":lo+1}


def classification(exponent, multiplicity):
    a=Q(exponent); order=a*multiplicity
    return {"power_divisor_order":str(order),"nontrivial_monodromy":order.denominator!=1,
        "holomorphic_at_this_divisor":bool(order.denominator==1 and order>=0)}


def produce(directory,source):
    from fractional_moment_report import summary as source_summary
    source=Path(source).resolve(); source_summary(source)
    if directory.exists(): raise ValueError("A fresh branch-audit directory is required")
    directory.mkdir(parents=True); previous=read(source/"protocol.json")
    exponents=sorted({Q(r["exponent"]) for r in read(source/"final_evaluation.json")["Dirichlet_root_calibrations"]}|{Q(n) for n in range(-2,3)})
    hashes=dict(previous["code_sha256"]); hashes.update({name:sha(BASE/name) for name in CODE})
    spec={"purpose":"guided local analytic calibration and general rational-divisor obstruction; no new arithmetic search or RH claim",
        "code_sha256":hashes,"source_run":str(source),"source_protocol_sha256":sha(source/"protocol.json"),
        "source_verification_sha256":sha(source/"verification.json"),"source_final_sha256":sha(source/"final_evaluation.json"),
        "precision":384,"radius":"1/64","boundary_subdivisions":16,"tolerance_bits":140,
        "independent_radius":"1/48","independent_precision":640,"independent_boundary_subdivisions":32,"independent_tolerance_bits":200,
        "known_zero_dependency":previous["known_zero_dependency"],"exponents":list(map(str,exponents)),
        "named_dependency":"ordinary zeta meromorphic with its unique simple pole at one; argument principle; existing independently certified simple critical zero",
        "historical_priority_is_acceptance_gate":False,"uniform_signed_control_proved":False}
    write(directory/"protocol.json",spec); flint.ctx.prec=spec["precision"]; flint.ctx.cap=24
    pole=contour(Q(spec["radius"]),spec["boundary_subdivisions"],spec["tolerance_bits"])
    assert pole["enclosed_zeros"]==0 and pole["unique_integer_winding"]==-1
    zero,zero_audit=known_zero_rectangle(spec["known_zero_dependency"])
    rows=[]
    for a in exponents:
        pole_class=classification(a,-1); zero_class=classification(a,1)
        phase=(flint.acb(0,2*flint.arb.pi()*real(-a))).exp()
        if pole_class["nontrivial_monodromy"]: assert (phase-1).abs_lower()>0
        rows.append({"exponent":str(a),"pole_at_one":pole_class,"simple_critical_zero":zero_class,
            "pole_monodromy_ball":[phase.real.str(45),phase.imag.str(45)],
            "single_valued_integer_order_multiplier_can_remove_pole_branch":not pole_class["nontrivial_monodromy"],
            "joint_product_pole_compensation_local_order":str(a*(-1+1)),
            "negative_power_retains_singularity_at_every_zero_multiplicity":bool(a<0),
            "uncompensated_power_holomorphic_Re_s_gt_half_ruled_out":not pole_class["holomorphic_at_this_divisor"],
            "local_repair_is_global_RH_proof":False})
    write(directory/"branch_audit.json",{"protocol_sha256":digest(spec),"pole_contour":pole,"simple_zero_audit":zero_audit,
        "classifications":rows,"uniform_sublinear_signed_controls_verified":[],"RH_proved":False})
    subprocess.run([sys.executable,str(BASE/"check_fractional_zeta_branches.py"),"--run-dir",str(directory)],check=True,cwd=BASE)
    publish(directory)


def summary(directory):
    directory=Path(directory).resolve(); spec=read(directory/"protocol.json"); data=read(directory/"branch_audit.json"); audit=read(directory/"verification.json")
    assert audit["all_passed"] and all(audit["checks"].values()) and audit["protocol_sha256"]==digest(spec)
    assert audit["source_sha256"]==sha(directory/"branch_audit.json") and audit["checker_sha256"]==sha(BASE/"check_fractional_zeta_branches.py")
    for name,expected in spec["code_sha256"].items(): assert sha(BASE/name)==expected
    source=Path(spec["source_run"])
    for name,key in (("protocol.json","source_protocol_sha256"),("verification.json","source_verification_sha256"),("final_evaluation.json","source_final_sha256")):
        assert sha(source/name)==spec[key]
    return {"status":"independently_verified_fractional_zeta_local_branch_gate","run_directory":str(directory),"checks":audit["checks"],
        "rational_exponents_audited":len(data["classifications"]),
        "fractional_pole_branches_detected":sum(c["pole_at_one"]["nontrivial_monodromy"] for c in data["classifications"]),
        "native_pole_winding":data["pole_contour"]["unique_integer_winding"],"native_enclosed_zero_count":data["pole_contour"]["enclosed_zeros"],
        "negative_calibration_is_guided":True,"uniform_sublinear_signed_controls_verified":[],"RH_proved":False,
        "verification_sha256":sha(directory/"verification.json")}


def publish(directory):
    result=summary(directory); directory=Path(directory)
    write(directory/"summary.json",result)
    (directory/"report.txt").write_text("RATIONAL ZETA POWERS: LOCAL POLE AND ZERO BRANCH GATE\n\n"
        f"Independent checks: {sum(result['checks'].values())}/{len(result['checks'])}.\n"
        f"Rational exponents audited: {result['rational_exponents_audited']}; fractional pole branches: {result['fractional_pole_branches_detected']}.\n"
        "The certified contour around one has winding -1 and encloses one pole and zero zeros.\n"
        "Every noninteger zeta exponent has an uncompensated branch obstruction at one, inside Re(s)>1/2.\n"
        "An integer-order multiplier outside the power cannot remove that fractional order.\n"
        "Taking the fractional power after joint pole compensation repairs the local order only.\n"
        "Negative powers retain singularities at every zero multiplicity; positive roots require additional zero-faithfulness obligations.\n"
        "This is a guided analytic calibration, separate from the fresh arithmetic search.\n"
        "Uniform signed arithmetic premises remain unproved. RH remains unproved.\n")
    pointer=BASE/"fractional-branch-results/latest.json"; pointer.parent.mkdir(exist_ok=True)
    write(pointer,{"run_directory":str(directory.resolve()),"summary_sha256":digest(result)})
    print("Published independently verified fractional zeta branch gate",flush=True)


def load_latest():
    path=BASE/"fractional-branch-results/latest.json"
    if not path.exists(): return {"status":"not_run","uniform_sublinear_signed_controls_verified":[],"RH_proved":False}
    pointer=read(path); result=summary(pointer["run_directory"]); assert digest(result)==pointer["summary_sha256"]
    return result


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--run-dir",type=Path,required=True); parser.add_argument("--source-run",type=Path,required=True)
    args=parser.parse_args(); produce(args.run_dir.resolve(),args.source_run)

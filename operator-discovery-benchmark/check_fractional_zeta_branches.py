#!/usr/bin/env python3
"""Independent larger-contour and exact divisor-order audit."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import flint
from check_signed_mellin_transfer import zero_disk

BASE=Path(__file__).resolve().parent
def read(path): return json.loads(Path(path).read_text())
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def digest(data): return hashlib.sha256(json.dumps(data,sort_keys=True,separators=(",",":"),allow_nan=False).encode()).hexdigest()
def real(x):
    x=Q(x); return flint.arb(x.numerator)/x.denominator


def independent_contour(spec):
    r=Q(spec["independent_radius"]); step=2*r/spec["independent_boundary_subdivisions"]
    coordinates=[(1-r,-r),(1+r,-r),(1+r,r),(1-r,r)]
    points=[flint.acb(real(x),real(y)) for x,y in coordinates]
    total=flint.acb(0); minimum=None
    def integrand(z,analytic):
        expansion=flint.acb_series([z,flint.acb(1)],prec=2).zeta()
        return expansion[1]/expansion[0]
    # Independent boundary construction uses rational coordinate rectangles.
    for i,(x,y) in enumerate(coordinates):
        endx,endy=coordinates[(i+1)%4]; N=spec["independent_boundary_subdivisions"]
        for j in range(N):
            midx=x+(endx-x)*Q(2*j+1,2*N); midy=y+(endy-y)*Q(2*j+1,2*N)
            ball=flint.acb(flint.arb(real(midx),real(abs(endx-x)/N/2)),flint.arb(real(midy),real(abs(endy-y)/N/2)))
            bound=ball.zeta().abs_lower(); assert bound>0
            if minimum is None or bound<minimum: minimum=bound
        integral=flint.acb.integral(integrand,points[i],points[(i+1)%4],
            abs_tol=real(Q(1,2**spec["independent_tolerance_bits"])),rel_tol=real(Q(1,2**spec["independent_tolerance_bits"])),eval_limit=40000,depth_limit=40)
        assert integral.is_finite(); total+=integral
    value=total/(flint.acb(0,2)*flint.arb.pi())
    assert value.real.contains(-1) and abs(value.real+1).upper()<real(Q(1,16))
    assert value.imag.contains(0) and abs(value.imag).upper()<real(Q(1,16))
    return [value.real.str(50),value.imag.str(50)],minimum.str(50)


def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--run-dir",type=Path,required=True)
    directory=parser.parse_args().run_dir.resolve(); spec=read(directory/"protocol.json"); data=read(directory/"branch_audit.json")
    for name,expected in spec["code_sha256"].items(): assert sha(BASE/name)==expected
    source=Path(spec["source_run"])
    for name,key in (("protocol.json","source_protocol_sha256"),("verification.json","source_verification_sha256"),("final_evaluation.json","source_final_sha256")):
        assert sha(source/name)==spec[key]
    assert read(source/"verification.json")["all_passed"] and data["protocol_sha256"]==digest(spec)
    flint.ctx.prec=spec["independent_precision"]; flint.ctx.cap=24
    assert 0<Q(spec["radius"])<Q(spec["independent_radius"])<Q(1,4)
    winding,minimum=independent_contour(spec)
    pole=data["pole_contour"]
    assert pole["unique_integer_winding"]==-1 and pole["known_enclosed_poles"]==1 and pole["enclosed_zeros"]==0
    assert Q(pole["radius"])==Q(spec["radius"])
    assert len(pole["boundary_cells"])==4*spec["boundary_subdivisions"] and len(pole["edge_integral_balls"])==4
    for i,c in enumerate(pole["boundary_cells"]):
        assert (c["edge"],c["cell"])==divmod(i,spec["boundary_subdivisions"])
        assert flint.arb(c["zeta_abs_lower_ball"])>0
    assert flint.arb(pole["winding_ball"][0]).contains(-1) and flint.arb(pole["winding_ball"][1]).contains(0)
    assert abs(flint.arb(pole["winding_ball"][0])+1).upper()<real(Q(1,16))
    zero,margin=zero_disk(spec["known_zero_dependency"])
    expected={Q(r["exponent"]) for r in read(source/"final_evaluation.json")["Dirichlet_root_calibrations"]}|{Q(n) for n in range(-2,3)}
    assert list(map(Q,spec["exponents"]))==sorted(expected)
    assert [Q(c["exponent"]) for c in data["classifications"]]==sorted(expected)
    for c in data["classifications"]:
        a=Q(c["exponent"])
        for key,m in (("pole_at_one",-1),("simple_critical_zero",1)):
            order=a*m; integral=order.numerator%order.denominator==0
            assert c[key]["power_divisor_order"]==str(order)
            assert c[key]["nontrivial_monodromy"]==(not integral)
            assert c[key]["holomorphic_at_this_divisor"]==(integral and order>=0)
        phase=flint.acb(0,-2*flint.arb.pi()*real(a)).exp()
        # Nonintegral phases are separated from one; integer controls are
        # checked against the exact value one to avoid rounded sine zeros.
        if a.denominator!=1:
            assert (phase-1).abs_lower()>0
            assert flint.arb(c["pole_monodromy_ball"][0]).contains(phase.real)
            assert flint.arb(c["pole_monodromy_ball"][1]).contains(phase.imag)
        else:
            assert flint.arb(c["pole_monodromy_ball"][0]).contains(1)
            assert flint.arb(c["pole_monodromy_ball"][1]).contains(0)
        assert c["single_valued_integer_order_multiplier_can_remove_pole_branch"]==(a.denominator==1)
        assert Q(c["joint_product_pole_compensation_local_order"])==0
        assert c["negative_power_retains_singularity_at_every_zero_multiplicity"]==(a<0)
        assert c["uncompensated_power_holomorphic_Re_s_gt_half_ruled_out"]==(a.denominator!=1 or a>0)
        assert not c["local_repair_is_global_RH_proof"]
    assert not data["RH_proved"] and not data["uniform_sublinear_signed_controls_verified"]
    checks={"frozen_code_and_verified_fractional_search_dependencies_checked":True,
        "larger_independent_contour_nonzero_boundary_and_integer_winding_certified":True,
        "unique_pole_and_zero_census_independently_confirmed":True,"simple_ordinary_zero_recertified":True,
        "rational_divisor_orders_monodromy_and_integer_controls_checked":True,
        "pole_compensation_and_all_multiplicity_zero_obligations_separated":True}
    result={"all_passed":True,"checks":checks,"protocol_sha256":digest(spec),"source_sha256":sha(directory/"branch_audit.json"),
        "checker_sha256":sha(Path(__file__)),"independent_winding_ball":winding,"independent_boundary_minimum_lower_ball":minimum,
        "independent_zero_Rouche_margin":margin,"mathematical_audit_imports_production_code":False,
        "uniform_sublinear_signed_controls_verified":[],"RH_proved":False}
    (directory/"verification.json").write_text(json.dumps(result,indent=2)+"\n")
    print("Independent fractional zeta branch audit",sum(checks.values()),"/",len(checks),flush=True)


if __name__=="__main__": main()

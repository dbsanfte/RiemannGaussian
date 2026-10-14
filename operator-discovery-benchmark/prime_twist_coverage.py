#!/usr/bin/env python3
"""Independent exhaustive finite coverage of frozen signed-prime estimates."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import flint
from check_prime_twists import (real,prime_coefficients,power,kernel,offset,read,sha,digest)

BASE=Path(__file__).resolve().parent


def square_prefix(values):
    squares=[real(0)];weighted=[real(0)];energies=[real(0)]
    for n in range(1,len(values)):
        a=values[n]-values[n-1];aa=a*a
        squares.append(squares[-1]+aa);weighted.append(weighted[-1]+n*aa)
        u,v=values[n-1],values[n]
        energies.append(energies[-1]+(u*u+u*v+v*v)/3)
    return squares,weighted,energies


def whole_moment(values,prefixes,X):
    squares,weighted,energies=prefixes
    D=X*squares[X]+real(Q(2*X)+Q(1,3))*(squares[2*X]-squares[X])-(weighted[2*X]-weighted[X])
    A2=energies[2*X]-energies[X]
    return A2,D,A2-D


def classify(value,bound):
    return "pass" if value<=bound else "fail" if value>bound else "unresolved"


def starting_record(candidate):
    return {"candidate_id":candidate["id"],"analytic_status":candidate["analytic_status"],
        "comparisons":0,"failures":0,"unresolved":0,"first_failure":None,"first_unresolved":None,
        "maximum_ratio_point":None,"maximum_ratio_upper_ball":"0"}


def update_record(record,n,value,bound):
    state=classify(value,bound);record["comparisons"]+=1
    if state=="fail":
        record["failures"]+=1
        if record["first_failure"] is None:record["first_failure"]=n;record["_first_failure_native_value"]=value
    if state=="unresolved":
        record["unresolved"]+=1
        if record["first_unresolved"] is None:record["first_unresolved"]=n
    upper=(value/bound).upper()
    old=record.pop("_peak_upper",real(0))
    if record["maximum_ratio_point"] is None or upper>old:
        record["maximum_ratio_point"]=n;record["maximum_ratio_upper_ball"]=upper.str(50)
        record["_peak_native_value"]=value
        old=upper
    record["_peak_upper"]=old
    record["_last_native_value"]=value


def direct_point(p,f,n):
    """Higher-precision roots and native integrals, independent of streaming."""
    value=real(0);delta=Q(p["delta"])
    for j,(c,b) in enumerate(zip(p["coefficients"],p["normalizers"])):
        c,b=Q(c),Q(b);a=j*delta
        if c:
            partial=sum((real(f[m])*real(m).root(a.denominator)**(-a.numerator)*(real(m).log() if p["channel"]=="log" else 1)
                for m in range(2,n) if f[m]),real(0))
            value-=real(c)*partial
        if b and n>2:
            alpha=1-a
            def integrand(u,analytic):return (real(alpha)*u).exp()/(u if p["channel"]=="weighted" else 1)
            integral=flint.acb.integral(integrand,real(2).log(),real(n).log(),abs_tol=real(Q(1,2**220)),rel_tol=real(Q(1,2**220)),depth_limit=28,eval_limit=20000)
            assert integral.is_finite() and integral.imag.contains(0)
            value+=real(b)*integral.real
    return value


def execute(directory,spec,source_summary):
    flint.ctx.prec=spec["precision"];N=spec["cutoff"]
    source=Path(spec["source_run"]);batch=read(source/"candidate_batch.json")
    ps={p["id"]:p for p in batch["programs"]};archive=read(source/"archive.json")["archive"]
    candidates=[dict(c) for c in archive]
    programs=[ps[pid] for pid in sorted({c["program_id"] for c in candidates})]
    f=prime_coefficients(N)
    keys={(p["channel"],j*Q(p["delta"])) for p in programs for j,c in enumerate(p["coefficients"]) if Q(c)}
    prefixes={key:real(0) for key in keys}
    kernels={(p["channel"],Q(a)) for p in programs for a,b in zip(p["normalizer_exponents"],p["normalizers"]) if Q(b)}
    offsets={c["id"]:offset(c["offset"],ps[c["program_id"]]) for c in candidates}
    records={c["id"]:starting_record(c) for c in candidates}
    values=[real(0)]*(N+1);li2=real(2).li()
    scales={(Q(c["theta"]),Q(c["log_power"])) for c in candidates}
    prime_indices=0
    for n in range(1,N+1):
        normalizers={key:kernel(key[1],n,key[0]) for key in kernels}
        outputs={}
        for p in programs:
            channel,delta=p["channel"],Q(p["delta"])
            value=sum((real(b)*normalizers[channel,Q(a)] for b,a in zip(p["normalizers"],p["normalizer_exponents"]) if Q(b)),real(0))
            value-=sum((real(c)*prefixes[channel,j*delta] for j,c in enumerate(p["coefficients"]) if Q(c)),real(0))
            outputs[p["id"]]=value
        scale_values={(theta,ell):real(n)**real(theta)*(flint.arb.const_e()+n).log()**real(ell) for theta,ell in scales}
        for c in candidates:
            value=abs(outputs[c["program_id"]]-offsets[c["id"]]);B=real(c["constant"])*scale_values[Q(c["theta"]),Q(c["log_power"])]
            update_record(records[c["id"]],n,value,B)
        if n>=2:values[n]=normalizers["weighted",Q(1)]+li2-prefixes["weighted",Q(0)]
        if f[n]:
            prime_indices+=1
            for channel,a in keys:prefixes[channel,a]+=real(f[n])*power(n,a)*(real(n).log() if channel=="log" else 1)
        if n%16384==0:print("Exhaustive frozen point bounds checked through",n,flush=True)
    prefixes_moment=square_prefix(values)
    moment_candidates=spec["source_unfiltered_moment_obligations"]
    moment_records={c["id"]:starting_record(c) for c in moment_candidates}
    for X in range(1,N//2+1):
        A2,D,off=whole_moment(values,prefixes_moment,X);assert A2>=0 and D>=0
        for c in moment_candidates:
            # Ratio <=1 is exactly the frozen signed off-diagonal premise.
            value=off-real(c["rho"])*D;B=real(c["constant"])*real(X)**real(c["gamma"])
            update_record(moment_records[c["id"]],X,value,B)
    print("Exhaustive complete moment windows checked through",N//2,flush=True)
    probes=[];flint.ctx.prec=768
    for c in candidates:
        row=records[c["id"]];p=ps[c["program_id"]]
        for n in sorted({row["maximum_ratio_point"],N}|({row["first_failure"]} if row["first_failure"] else set())):
            v=direct_point(p,f,n);A=offset(c["offset"],p)
            B=real(c["constant"])*real(n)**real(c["theta"])*(flint.arb.const_e()+n).log()**real(c["log_power"])
            state=classify(abs(v-A),B)
            for location,key in ((row["maximum_ratio_point"],"_peak_native_value"),(row["first_failure"],"_first_failure_native_value"),(N,"_last_native_value")):
                if n==location:assert abs(v-A).overlaps(row[key])
            if n==row["first_failure"]:assert state=="fail"
            if row["failures"]==row["unresolved"]==0:assert state=="pass"
            probes.append({"candidate_id":c["id"],"n":n,"state":state,"value_ball":v.str(50)})
    # Independent per-cell integration and per-ramp diagonal at extremal windows.
    moment_probes=[]
    for c in moment_candidates:
        X=moment_records[c["id"]]["maximum_ratio_point"]
        U=[flint.arb(v) for v in values[:2*X+1]]
        energy=sum(((U[n]*U[n]+4*((U[n]+U[n+1])/2)*((U[n]+U[n+1])/2)+U[n+1]*U[n+1])/6 for n in range(X,2*X)),real(0))
        diagonal=sum(((U[n]-U[n-1])*(U[n]-U[n-1])*real(X if n<=X else Q(2*X-n)+Q(1,3)) for n in range(1,2*X+1)),real(0))
        expected=whole_moment(values,prefixes_moment,X)
        assert energy.overlaps(expected[0]) and diagonal.overlaps(expected[1])
        state=classify(energy-real(1+Q(c["rho"]))*diagonal,real(c["constant"])*real(X)**real(c["gamma"]))
        assert (energy-real(1+Q(c["rho"]))*diagonal).overlaps(moment_records[c["id"]]["_peak_native_value"])
        if moment_records[c["id"]]["failures"]==moment_records[c["id"]]["unresolved"]==0:assert state=="pass"
        moment_probes.append({"candidate_id":c["id"],"X":X,"state":state,"energy_ball":energy.str(50),"diagonal_ball":diagonal.str(50)})
    for row in list(records.values())+list(moment_records.values()):
        for key in list(row):
            if key.startswith("_"):row.pop(key)
    point_passes=[r for r in records.values() if r["failures"]==r["unresolved"]==0]
    point_RH=[r for r in point_passes if r["analytic_status"].startswith("RH_sufficient")]
    checks={"sealed_verified_source_and_frozen_coverage_protocol":True,
        "all_archived_candidates_including_rejections_tested_without_reselection":len(records)==len(archive),
        "every_integer_point_has_a_native_interval_comparison":all(r["comparisons"]==N for r in records.values()),
        "every_integer_window_has_a_complete_native_moment_comparison":all(r["comparisons"]==N//2 for r in moment_records.values()),
        "actual_prime_power_sieve_and_strict_endpoint_semantics_used":True,
        "higher_precision_roots_and_independent_native_kernel_integrals_checked":bool(probes),
        "separate_cell_and_per_increment_moment_extremum_probes_checked":bool(moment_probes),
        "finite_coverage_retains_uniform_proof_obligations":True}
    result={"all_passed":all(checks.values()),"checks":checks,"protocol_sha256":digest(spec),
        "code_sha256":sha(BASE/"prime_twist_coverage.py"),"exact_coefficients_checked":N,"coefficient_sha256":digest(list(map(str,f))),
        "nonzero_prime_power_indices":prime_indices,"point_comparisons":N*len(records),"complete_moment_windows":N//2,
        "moment_comparisons":N//2*len(moment_records),"point_bound_records":list(records.values()),"moment_bound_records":list(moment_records.values()),
        "point_bounds_passing_every_tested_integer":len(point_passes),"RH_sufficient_if_uniform_point_bounds_passing_every_tested_integer":len(point_RH),
        "moment_bounds_passing_every_tested_integer_window":sum(r["failures"]==r["unresolved"]==0 for r in moment_records.values()),
        "higher_precision_point_probes":probes,"separate_moment_probes":moment_probes,
        "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    assert result["all_passed"]
    (directory/"verification.json").write_text(json.dumps(result,indent=2)+"\n")
    lines=["EXHAUSTIVE FINITE COVERAGE OF FROZEN PRIME-TWIST AND PAIR ESTIMATES","",
        f"Every integer point 1..{N} tested for ALL {len(records)} frozen archived estimates.",
        f"Every integer complete window start 1..{N//2} tested for ALL {len(moment_records)} frozen unfiltered signed moment estimates.",
        f"Interval comparisons: {result['point_comparisons']} point / {result['moment_comparisons']} moment.",
        f"Point bounds passing the entire prefix: {len(point_passes)}; RH-sufficient if uniform: {len(point_RH)}.",
        f"Moment bounds passing the entire finite window range: {result['moment_bounds_passing_every_tested_integer_window']}.",
        "The cutoff is frozen before this exhaustive audit. The archived formulas and constants are unchanged.",
        "This is an evaluator extension, not a fresh discovery run. Cumulative prefixes overlap development data.",
        "The upper interval includes fresh scales beyond the source final cutoff. No complete coefficient independence is claimed.",
        "No finite coverage proves the uniform premise or RH.","","Point records:"]
    for c in candidates:
        row=records[c["id"]];lines.append(f"{c['id']}: failures={row['failures']}, first failure={row['first_failure']}, peak ratio at {row['maximum_ratio_point']}: {row['maximum_ratio_upper_ball']}; {row['analytic_status']}")
    lines.extend(["","Moment records:"])
    for row in moment_records.values():lines.append(f"{row['candidate_id']}: failures={row['failures']}, first failure={row['first_failure']}, peak signed ratio at {row['maximum_ratio_point']}: {row['maximum_ratio_upper_ball']}")
    (directory/"report.txt").write_text("\n".join(lines)+"\n")
    print("Exhaustive finite coverage passed:",len(point_RH),"RH-compatible point leads and",result["moment_bounds_passing_every_tested_integer_window"],"moment leads survive; uniform proofs remain missing",flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--source-run",type=Path,required=True);parser.add_argument("--run-dir",type=Path,required=True);parser.add_argument("--cutoff",type=int)
    args=parser.parse_args();source=args.source_run.resolve();directory=args.run_dir.resolve()
    if directory.exists():raise FileExistsError("Retain completed or failed coverage audit")
    from prime_twist_report import summary
    source_summary=summary(source);source_spec=read(source/"protocol.json")
    cutoff=args.cutoff or 2**(source_summary["complete_coefficient_cutoff"].bit_length()+1)
    if cutoff<=source_summary["complete_coefficient_cutoff"]:raise ValueError("Coverage extension must reach beyond the sealed source cutoff")
    spec={"schema":1,"source_run":str(source),"precision":384,"higher_precision":768,"cutoff":cutoff,
        "cutoff_rule":"twice the next power of two above source cutoff, unless an explicit resource cutoff is supplied",
        "source_verification_sha256":sha(source/"verification.json"),"source_archive_sha256":sha(source/"archive.json"),
        "source_final_sha256":sha(source/"final_evaluation.json"),"source_protocol_sha256":digest(source_spec),
        "code_sha256":dict(source_spec["code_sha256"],**{"prime_twist_coverage.py":sha(BASE/"prime_twist_coverage.py")}),
        "point_selection":"every integer from 1 through cutoff; every archived candidate, irrespective of source final outcome",
        "window_selection":"every integer X from 1 through cutoff//2; complete interpolation windows [X,2X]",
        "probe_selection":"every point candidate's maximum ratio, first failure and final cutoff; every moment candidate's maximum signed ratio window",
        "source_unfiltered_moment_obligations":source_spec["source_unfiltered_moment_obligations"],
        "candidate_reselection_or_refitting":False,"fresh_discovery_run":False,
        "cumulative_prefixes_overlap_development_data":True,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    directory.mkdir(parents=True);(directory/"protocol.json").write_text(json.dumps(spec,indent=2)+"\n")
    (directory/"frozen_source.py").write_bytes((BASE/"prime_twist_coverage.py").read_bytes())
    execute(directory,spec,source_summary)


if __name__=="__main__":main()

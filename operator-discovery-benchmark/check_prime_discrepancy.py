#!/usr/bin/env python3
"""Independent full-period, actual-prime density and signed Gram audit."""
import argparse
from collections import Counter
from fractions import Fraction as Q
import hashlib
from itertools import product
import json
from math import ceil,floor,lcm
from pathlib import Path
import random
import subprocess
import sys
import flint
from check_signed_mellin_transfer import zero_disk

BASE=Path(__file__).resolve().parent


def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(d):return hashlib.sha256(json.dumps(d,sort_keys=True,separators=(",",":"),allow_nan=False).encode()).hexdigest()
def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def prime_coefficients(N):
    spf=list(range(N+1))
    for p in range(2,N+1):
        if spf[p]==p:
            for n in range(p*p,N+1,p):
                if spf[n]==n:spf[n]=p
    result=[Q(0)]*(N+1)
    for n in range(2,N+1):
        p,r,k=spf[n],n,0
        while r%p==0:r//=p;k+=1
        if r==1:result[n]=Q(1,k)
    return result


def enclosure(stored,value):
    b=flint.arb(stored)
    assert b.is_finite() and value.is_finite() and b.contains(value),(stored,value)
    assert b.rad()<real(Q(1,10**35))*(1+abs(value))


def check_carries(data,spec,f):
    rule=spec["carry_grammar"];rows=data["carry_search"]["all_proposals"]
    tuples=product(range(rule["free_integer_range"][0],rule["free_integer_range"][1]+1),repeat=len(rule["delays"])-1)
    assert len(rows)==(rule["free_integer_range"][1]-rule["free_integer_range"][0]+1)**(len(rule["delays"])-1)
    psi=[real(0)]
    for n in range(1,len(f)):psi.append(psi[-1]+real(f[n])*real(n).log())
    proved=[];period_cells=0;initial_values=0
    for row,tail in zip(rows,tuples):
        cs=[Q(1)]+list(map(Q,tail));certificate=row["certificate"]
        assert row["coefficients"]==list(map(str,cs)) and row["id"]==digest(row["coefficients"])
        drift=sum((v/(j+1) for j,v in enumerate(cs)),Q(0))
        if drift:
            assert certificate=={"status":"nonzero_linear_drift","drift":str(drift)}
            assert "density" not in row
            continue
        period=lcm(*(j+1 for j,c in enumerate(cs) if c))
        # Quotient/remainder evaluation provides an independent period table.
        cells=[sum((c*Q(u-u%(j+1),j+1) for j,c in enumerate(cs)),Q(0)) for u in range(period)]
        if min(cells)<0:
            assert certificate=={"status":"negative_period_cell","cell":next(u for u,v in enumerate(cells) if v<0)}
            assert "density" not in row
            continue
        H=sum((real(-c)*real(j+1).log()/real(j+1) for j,c in enumerate(cs)),real(0))
        assert H>0 and certificate["status"]=="proved_nonnegative_periodic_carry"
        assert certificate["period"]==period and certificate["period_cells"]==list(map(str,cells))
        assert certificate["coefficients"]==row["coefficients"] and cells[1]==1
        assert Q(certificate["coefficient_cost"])==sum(map(abs,cs),Q(0))
        assert certificate["unit_interval_coverage"]==["1","2"]
        assert certificate["universal_domain"]=="every real u>=0"
        enclosure(certificate["entropy_ball"],H)
        # Explicit rational noninteger inputs and multiple periods, in addition
        # to the complete-cell proof (which already covers all real inputs).
        for u in range(3*period):
            for offset in (Q(0),Q(1,7),Q(6,7)):
                x=u+offset
                K=sum((c*floor(x/(j+1)) for j,c in enumerate(cs)),Q(0))
                assert K==cells[u%period]>=0
        density=row["density"];k=density["tail_index"];cut=density["initial_cutoff"]
        assert k==rule["tail_index"]>=4 and cut==2**(k-1)<len(psi)
        S=real(sum(map(abs,cs),Q(0)))
        tail_bound=4*H+real(Q(2,2**k))*S*(k+real(2).log()*real(Q(k*(k+1),2)))
        enclosure(density["tail_constant_ball"],tail_bound)
        maximum=max((psi[n]/n).upper() for n in range(1,cut+1))
        enclosure(density["initial_maximum_ball"],maximum)
        C=Q(density["constant"])
        assert real(C)>max(maximum,tail_bound.upper())
        assert real(C)-max(maximum,tail_bound.upper())<real(Q(1,1024))
        assert all(psi[n]<=real(C)*n for n in range(1,cut+1));initial_values+=cut
        # Discrete monotonicity of both tail terms follows by cross products.
        for j in range(k,k+33):
            assert (j+1)*2**j<=j*2**(j+1)
            assert (j+1)*(j+2)*2**j<=j*(j+1)*2**(j+1)
        assert density["uniform_prime_weight_bound_proved"] and not density["RH_sufficient"]
        assert not density["imported_prime_distribution_estimate"]
        period_cells+=period;proved.append(row)
    statuses=Counter(row["certificate"]["status"] for row in rows)
    assert dict(statuses)==data["carry_search"]["statuses"] and proved
    selected=min(proved,key=lambda r:(Q(r["density"]["constant"]),Q(r["certificate"]["coefficient_cost"]),tuple(map(Q,r["coefficients"]))))
    assert data["carry_search"]["selected_id"]==selected["id"] and data["carry_search"]["selected"]==selected
    assert not data["carry_search"]["expected_named_formula_supplied"]
    cs=list(map(Q,selected["coefficients"]))
    assert [r["N"] for r in data["factorial_traces"]]==spec["factorial_trace_points"]
    for r in data["factorial_traces"]:
        N=r["N"]
        left=sum((real(f[n])*real(n).log()*real(sum((c*floor(Q(N,n*(j+1))) for j,c in enumerate(cs)),Q(0))) for n in range(1,N+1) if f[n]),real(0))
        # Independent special-function factorial representation.
        right=sum((real(c)*real(N//(j+1)+1).lgamma() for j,c in enumerate(cs) if c),real(0))
        enclosure(r["prime_weighted_carry_ball"],left);enclosure(r["factorial_combination_ball"],right)
        assert left.overlaps(right)
        assert psi[N]-psi[N//2]<=right or abs(psi[N]-psi[N//2]-right)<real(Q(1,10**80))
    return selected,len(rows),len(proved),period_cells,initial_values


def tables(f,betas):
    li=[real(0),real(0)]+[real(n).li() for n in range(2,len(f))]
    count=[Q(0)]
    for v in f[1:]:count.append(count[-1]+v)
    out={}
    for beta in betas:
        values=[real(0),real(0)]+[li[n]-real(Q(beta)*count[n-1]) for n in range(2,len(f))]
        a=[real(0),real(0)]+[values[n]-values[n-1] for n in range(2,len(f))]
        out[beta]=(values,a,[v*v for v in a])
    return out


def check_coefficient_density(data,spec,selected,table):
    Cp=Q(selected["density"]["constant"]);count=0
    for beta,record in data["coefficient_densities"].items():
        a=table[beta][1]
        assert [r["initial_cutoff"] for r in record["proposals"]]==spec["coefficient_density_thresholds"]
        for r in record["proposals"]:
            n=r["initial_cutoff"];b=Q(beta)
            assert n>=8 and Q(r["beta"])==b
            top=real(0);sq=real(0)
            for j in range(1,n+1):
                sq+=a[j]*a[j]
                v=sq*(flint.arb.const_e()+j).log()/j
                top=max(top,v.upper())
                assert v<=real(r["constant"])
                count+=1
            enclosure(r["initial_maximum_ball"],top)
            logn=real(n).log();loge=(real(n)+flint.arb.const_e()).log()
            tail=real(2).li()**2*loge/n+2*(1/real(2).log()**2+real(b*b))*loge/real(n).sqrt()+8*loge/logn**2+4*real(b*b*Cp)*loge/logn
            enclosure(r["tail_majorant_ball"],tail)
            C=real(r["constant"])
            assert C>max(top,tail.upper()) and C-max(top,tail.upper())<real(Q(1,1024))
            assert r["all_scale_coefficient_square_bound_proved"] and not r["signed_pair_bound_proved"]
            assert real(8).log()>2 # proves square-root term monotonicity on N>=8
        best=min(record["proposals"],key=lambda r:(Q(r["constant"]),r["initial_cutoff"]))
        assert record["selected"]==best
    return count


def interp(values,t):
    if t<=1:return real(0)
    n=floor(t);v=t-n
    return values[n] if not v else values[n]+real(v)*(values[n+1]-values[n])


def energy(atoms,values,X):
    points={Q(X),Q(2*X)}
    for d,c in atoms:
        d=Q(d)
        for n in range(floor(Q(X)/d)+1,ceil(Q(2*X)/d)):
            points.add(d*n)
    points=sorted(points)
    def value(t):return sum((real(c)*interp(values,t/Q(d)) for d,c in atoms),real(0))
    result=real(0);left=value(points[0])
    for l,r in zip(points,points[1:]):
        mid=value((l+r)/2);right=value(r)
        result+=real((r-l)/6)*(left*left+4*mid*mid+right*right);left=right
    return result,len(points)-1


def diagonal_entries(atoms,X):
    """Independent exact Simpson integration of each squared ramp sum."""
    atoms=[(Q(d),Q(c)) for d,c in atoms];out=[Q(0)];X=Q(X)
    for n in range(1,ceil(2*X)+1):
        constant=Q(0);active=[]
        for d,c in atoms:
            if d*n<=X:constant+=c
            elif d*(n-1)<2*X:active.append((d,c))
        if not active:
            out.append(X*constant*constant);continue
        points={X,2*X}
        for d,c in active:
            points|={t for t in (d*(n-1),d*n) if X<t<2*X}
        points=sorted(points)
        def value(t):return constant+sum((c*max(Q(0),min(Q(1),t/d-(n-1))) for d,c in active),Q(0))
        total=Q(0);left=value(points[0])
        for l,r in zip(points,points[1:]):
            mid=value((l+r)/2);right=value(r)
            total+=(r-l)*(left*left+4*mid*mid+right*right)/6;left=right
        assert total>=0;out.append(total)
    return out


def moments(ps,table,scales,stored):
    out={};cells=0;entries=0
    # Cache only the small discovery/validation kernels. Final kernels can
    # be large and are evaluated directly without holding every program.
    cache={}
    for p in ps:
        pid=p["id"];values,a,squares=table[p["beta"]];rows={}
        assert set(stored[pid])==set(map(str,scales))
        for X in scales:
            A,ncells=energy(p["atoms"],values,X);cells+=ncells
            key=(tuple(tuple(t) for t in p["atoms"]),X)
            if X<=521:
                if key not in cache:cache[key]=diagonal_entries(p["atoms"],X)
                K=cache[key]
            else:K=diagonal_entries(p["atoms"],X)
            D=sum((squares[n]*real(K[n]) for n in range(1,len(K)) if K[n]),real(0));entries+=len(K)-1
            row={"A2":A,"D":D,"C_off":A-D};rows[str(X)]=row
            for k,v in row.items():enclosure(stored[pid][str(X)][k],v)
        out[pid]=rows
    return out,cells,entries


def status(v,b):return "pass" if v<=b else ("fail" if v>b else "unresolved")


def check_candidate(c,p,density,training=None):
    rho,gamma,B=map(Q,(c[k] for k in ("rho","gamma","constant")))
    eta=max(Q(0),Q(gamma-1,2)) if rho<=-1 else max(Q(1,2),Q(gamma-1,2))
    assert gamma>=0 and B>0
    beta=Q(p["beta"])
    expected=("uniform_claim_ruled_out_by_pole_logarithm" if beta!=1 and eta<1 else
        "uniform_claim_ruled_out_by_actual_critical_zero" if beta==1 and eta<Q(1,2) else
        "RH_sufficient_signed_correlation_obligation_missing_uniform_proof" if beta==1 and eta<=Q(1,2) else
        "signed_correlation_obligation_above_RH_threshold")
    tr=c["transfer"]
    assert c["analytic_status"]==tr["analytic_status"]==expected
    assert Q(tr["mellin_exponent"])==eta and tr["RH_sufficient_if_uniform"]==(beta==1 and eta<=Q(1,2))
    S=sum((abs(Q(v)) for d,v in p["atoms"]),Q(0))
    assert Q(tr["diagonal_coefficient"])==3*Q(density["constant"])*S*S
    assert tr["all_scale_diagonal_bound_proved"] and not tr["uniform_signed_correlation_premise_proved"] and not tr["RH_proved"]
    for k,v in (("rho",rho),("gamma",gamma),("constant",B)):assert Q(tr[k])==v
    assert c["id"]==digest({k:c[k] for k in ("program_id","rho","gamma","constant")})
    if training is not None:
        top=max([real(0)]+[((row["C_off"]-real(rho)*row["D"])/real(X)**real(gamma)).upper() for X,row in training.items()])
        assert real(B)+real(Q(1,10**30))>=2*top
        assert real(B)-2*top<real(Q(1,1024))+real(Q(1,10**30)) or B==Q(1,1024)
    return eta


def comparisons(c,observed):
    rho,gamma,B=map(Q,(c[k] for k in ("rho","gamma","constant")))
    return {X:status(r["C_off"],real(rho)*r["D"]+real(B)*real(X)**real(gamma)) for X,r in observed.items()}


def interpolation_calibration(ps,f,table):
    count=[Q(0)]
    for v in f[1:]:count.append(count[-1]+v)
    tested=0
    for beta in table:
        vals=table[beta][0]
        for n in (1,2,3,4,5,8,15,31,64,127):
            for u in (Q(1,113),Q(112,113)):
                t=n+u
                actual=real(0) if t<2 else real(t).li()-real(Q(beta)*count[n])
                assert abs(actual-interp(vals,t))<real(2+abs(Q(beta)));tested+=1
    return tested


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--run-dir",type=Path,required=True)
    directory=parser.parse_args().run_dir.resolve()
    spec,seal,arc,cases,final=(read(directory/n) for n in ("protocol.json","seal.json","archive.json","final_cases.json","final_evaluation.json"))
    for n,h in spec["code_sha256"].items():assert sha(BASE/n)==h
    source=Path(spec["source_run"])
    assert sha(source/"verification.json")==spec["source_verification_sha256"]
    assert sha(source/"candidate_batch.json")==spec["source_batch_sha256"] and read(source/"verification.json")["all_passed"]
    from prime_error_report import summary as parent_summary
    parent_summary(source)
    assert spec["input_programs"]==read(source/"candidate_batch.json")["programs"]
    assert not spec["input_programs_selected_by_prior_final_outcomes"] and not spec["imported_prime_distribution_estimate"]
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"] and not seal["final_cases_exist_at_seal"]
    for n,h in seal["files"].items():assert sha(directory/n)==h
    assert cases["created_after_selection_closed"] and cases["seal_sha256"]==final["seal_sha256"]==digest(seal)
    assert final["cases_sha256"]==digest(cases)
    assert all(arc["worker_access_denials"].values()) and not arc["final_data_used"] and not arc["RH_proved"]
    assert not arc["uniform_signed_correlation_premise_proved"]
    rng=random.Random(int(cases["evaluator_seed"]));rule=spec["final_cases"]
    exponents=sorted(rng.sample(range(rule["dyadic_exponents"][0],rule["dyadic_exponents"][1]+1),rule["dyadic_count"]))
    irregular=sorted(rng.sample(range(rule["irregular_range"][0],rule["irregular_range"][1]+1),rule["irregular_count"]))
    large=sorted(set([2**j for j in exponents]+irregular))
    assert cases["dyadic_exponents"]==exponents and cases["irregular"]==irregular and cases["large"]==large
    assert cases["scales"]==sorted(set(large+rule["boundary"]))
    replay=directory/"replay"
    if not replay.exists():
        replay.mkdir();(replay/"protocol.json").write_bytes((directory/"protocol.json").read_bytes())
        subprocess.run([sys.executable,str(BASE/"prime_discrepancy_search.py"),"discover","--run-dir",str(replay)],check=True,cwd=BASE)
    for n in ("discovery_data.json","candidate_batch.json","validation_data.json","archive.json","seal.json"):
        assert sha(directory/n)==sha(replay/n)
    batch=read(directory/"candidate_batch.json");development=read(directory/"discovery_data.json");validation=read(directory/"validation_data.json")
    assert batch["frozen_before_validation"] and batch["protocol_sha256"]==digest(spec)
    assert batch["discovery_sha256"]==sha(directory/"discovery_data.json")
    ps=batch["programs"];lookup={p["id"]:p for p in ps};assert ps==spec["input_programs"] and len(lookup)==len(ps)
    for p in ps:
        assert p["atoms"][0]==["1","1"] and all(Q(d)>=1 for d,c in p["atoms"])
        assert len({Q(d) for d,c in p["atoms"]})==len(p["atoms"])
        assert p["id"]==digest({k:p[k] for k in ("atoms","beta")})
    flint.ctx.prec=768
    zero,margin=zero_disk(spec["known_zero_dependency"])
    assert zero.real.contains(real(Q(1,2)))
    # zero_disk temporarily changes precision. Restore it for the independent
    # full-prefix and alternative special-function evaluations.
    flint.ctx.prec=768
    f=prime_coefficients(development["coefficient_cutoff"])
    assert development["coefficient_sha256"]==digest(list(map(str,f)))
    selected,carry_count,proved_count,period_count,prime_patch=check_carries(development,spec,f)
    betas=sorted({p["beta"] for p in ps},key=Q);table=tables(f,betas)
    coefficient_patch=check_coefficient_density(development,spec,selected,table)
    interpolation_cases=interpolation_calibration(ps,f,table)
    print("Independent all-scale prime/diagonal certificates checked",flush=True)
    training,cells,entries=moments(ps,table,spec["training_scales"],development["complete_moments"])
    coeff_count=len(f)-1
    N=validation["coefficient_cutoff"];f=prime_coefficients(N)
    assert N==2*max(spec["validation_scales"]) and validation["coefficient_sha256"]==digest(list(map(str,f)))
    val,more_cells,more_entries=moments(ps,tables(f,betas),spec["validation_scales"],validation["complete_moments"])
    cells+=more_cells;entries+=more_entries;coeff_count+=N
    assert len(validation["candidates"])==len(batch["candidates"])
    for c,original in zip(validation["candidates"],batch["candidates"]):
        assert all(c[k]==v for k,v in original.items())
        p=lookup[c["program_id"]]
        check_candidate(c,p,development["coefficient_densities"][p["beta"]]["selected"],training[p["id"]])
        states=comparisons(c,val[p["id"]])
        assert c["validation_failures"]==[X for X,v in states.items() if v=="fail"]
        assert c["validation_unresolved"]==[X for X,v in states.items() if v=="unresolved"]
    print("Independent training, validation and candidate bounds checked",flush=True)
    N=2*max(cases["scales"]);f=prime_coefficients(N)
    assert final["coefficient_cutoff"]==N and final["coefficient_sha256"]==digest(list(map(str,f)));coeff_count+=N
    used={c["program_id"] for c in arc["archive"]};chosen=[p for p in ps if p["id"] in used]
    assert set(final["actual_moments"])==used
    actual,c,e=moments(chosen,tables(f,betas),cases["scales"],final["actual_moments"])
    cells+=c;entries+=e
    print("Independent fresh actual-prime windows checked",flush=True)
    cut=spec["delayed_support_cutoff"];controls={};control_windows=0
    for name,coefs in (("positive_support",[Q(0),Q(0)]+[Q(1)]*(N-1)),("delayed_support",f[:cut+1]+[Q(1)]*(N-cut))):
        assert set(final["support_control_moments"][name])==used
        controls[name],c,e=moments(chosen,tables(coefs,betas),cases["large"],final["support_control_moments"][name])
        cells+=c;entries+=e;control_windows+=len(chosen)*len(cases["large"])
        print("Independent",name,"complete windows checked",flush=True)
    assert len(final["outcomes"])==len(arc["archive"])
    for candidate,outcome in zip(arc["archive"],final["outcomes"]):
        pid=candidate["program_id"];assert candidate["id"]==outcome["candidate_id"]
        states=comparisons(candidate,actual[pid])
        assert outcome["window_comparisons"]==states and outcome["finite_windows_passed"]==all(v=="pass" for v in states.values())
        assert outcome["support_control_comparisons"]=={name:comparisons(candidate,values[pid]) for name,values in controls.items()}
        assert not outcome["support_controls_are_actual_prime_density_inputs"] and not outcome["reselected"]
        assert not outcome["uniform_signed_correlation_premise_proved"] and not outcome["RH_proved"]
    assert not final["RH_proved"] and not final["uniform_RH_sufficient_signed_controls_verified"]
    checks={"frozen_parent_all_programs_and_sealed_fresh_case_provenance_checked":True,
        "discovery_isolation_and_deterministic_selection_replay_checked":True,
        "all_floor_proposals_and_full_period_universal_certificates_checked":True,
        "factorial_trace_and_elementary_dyadic_prime_density_certificates_checked":True,
        "complete_prime_density_finite_patch_and_monotone_tail_checked":True,
        "actual_prime_power_support_and_all_coefficient_square_certificates_checked":True,
        "complete_quadratic_window_energies_and_independent_ramp_Gram_diagonals_checked":True,
        "all_learned_constants_validation_and_final_comparisons_checked":True,
        "bounded_interpolation_error_and_logarithmic_ordinary_zero_bridge_checked":True,
        "rho_threshold_actual_zero_and_pole_logarithm_obstructions_checked":True,
        "support_controls_excluded_from_actual_prime_density_certificates_checked":True,
        "unsigned_all_scale_results_separated_from_unproved_signed_correlation_premises":True}
    result={"all_passed":all(checks.values()),"checks":checks,"protocol_sha256":digest(spec),
        "final_sha256":sha(directory/"final_evaluation.json"),"checker_sha256":sha(BASE/"check_prime_discrepancy.py"),
        "programs_checked":len(ps),"estimates_checked":len(batch["candidates"]),"carry_proposals_checked":carry_count,
        "universal_floor_certificates_checked":proved_count,"full_period_cells_checked":period_count,
        "prime_density_finite_patch_values_checked":prime_patch,"coefficient_density_finite_patch_values_checked":coefficient_patch,
        "exact_coefficients_checked":coeff_count,"complete_actual_windows_checked":len(ps)*(len(spec["training_scales"])+len(spec["validation_scales"]))+len(chosen)*len(cases["scales"]),
        "complete_support_control_windows_checked":control_windows,"polynomial_integration_cells_checked":cells,
        "independent_ramp_Gram_entries_checked":entries,"bounded_interpolation_cases":interpolation_cases,
        "actual_zero_Rouche_margin":margin,"imported_prime_distribution_estimate":False,
        "uniform_signed_correlation_premise_proved":False,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    (directory/"verification.json").write_text(json.dumps(result,indent=2)+"\n")
    print("Independent prime-density/signed-correlation audit",sum(checks.values()),"/",len(checks),flush=True)


if __name__=="__main__":main()

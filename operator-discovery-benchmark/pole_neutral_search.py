#!/usr/bin/env python3
"""Search actual signed fractional coefficient sums with pole-aware kernels."""
import argparse
from fractions import Fraction as Q
import math,os,random,subprocess,sys
from pathlib import Path
import flint
from stable_scale_search import read,write,sha,digest,verify_code,BASE
from fractional_moment_search import restrict
from signed_mellin_transfer import known_zero_rectangle
from pole_neutral_grammar import VERSION,real,coefficients,values,serialize,transfer,reciprocal_cost

CODE=["pole_neutral_grammar.py","pole_neutral_proof.txt","pole_neutral_search.py","check_pole_neutral.py","pole_neutral_report.py","exact_arithmetic.py"]


def root_grid(denominator,seed):
    rng=random.Random(seed);grid={Q(1,d) for d in range(1,denominator+1)}
    extra=[Q(p,d) for d in range(2,denominator+1) for p in range(2,d) if math.gcd(p,d)==1]
    rng.shuffle(extra)
    for a in extra:
        if len(grid)>=denominator+2:break
        grid.add(a)
    return sorted(grid)


def protocol(source,branch):
    from mellin_search_report import summary as source_summary
    from fractional_zeta_branch_audit import summary as branch_summary
    source=Path(source).resolve();branch=Path(branch).resolve();source_summary(source);branch_summary(branch)
    previous=read(source/"protocol.json");arc=read(source/"archive.json");hashes=dict(read(branch/"protocol.json")["code_sha256"])
    hashes.update(previous["code_sha256"])
    hashes.update({n:sha(BASE/n) for n in CODE});hashes["fractional_moment_search.py"]=sha(BASE/"fractional_moment_search.py")
    seed=2026100979;denominator=6
    return {"schema":1,"grammar_version":VERSION,"seed":seed,"precision":320,"code_sha256":hashes,
        "source_run":str(source),"source_archive_sha256":sha(source/"archive.json"),"source_verification_sha256":sha(source/"verification.json"),
        "branch_run":str(branch),"branch_audit_sha256":sha(branch/"branch_audit.json"),"branch_verification_sha256":sha(branch/"verification.json"),
        "known_zero_dependency":arc["known_zero_dependency"],"maximum_denominator":denominator,
        "coefficient_powers":[str(a) for a in root_grid(denominator,seed)],
        "kernel_powers":["0"]+[str(b) for b in root_grid(denominator,seed+1)],
        "shifts":[str(Q(k,2)) for k in range(-1,4)],
        "objective":"Find actual signed arithmetic bounds on coefficient roots and fractional logarithmic sums with an all-multiplicity ordinary-zeta bridge",
        "construction":"independent coefficient power, kernel power and rational shift grids; local divisor audit never assumes matching powers",
        "training_points":[1,2,3,5,8,12,16,24,32,48,64,96,128],"validation_points":[193,257,389,521],
        "data_scope":"complete arithmetic sum through every point; certified special-function values; no omitted coefficients or quadrature estimates",
        "offset_inference":"zero, median and mean of training responses at n>=16; quantize to 1/256; no predicted constant formula",
        "theta_inference":"OLS log absolute centered responses plus 0,1/8,1/4 margins on 1/32 grid, and generic quarter-power grid from zero to two",
        "constant_inference":"twice maximum training response/n^theta; upward 1/1024 rounding",
        "cost_line":"sigma=eta+1/8, height=16; charge full inverse power 1/a, shifted kernel, offset and real-interpolation bound",
        "archive_size":12,"selection":"original Mobius baseline; best matched fractional power per denominator; kernel-only smoothing; one failed pole-compensation and one introduced-shift control; fill by RH-compatible exponent and full reciprocal cost",
        "final_cases":{"large_count":4,"large_range":[2049,8191],"intermediate_count":3,"intermediate_range":[17,127],"boundary":[1,2,3,15]},
        "delayed_positive_cutoff":128,"maximum_final_cutoff":8191,
        "kernel_quadrature_calibration":{"count":2,"u_numerator_range":[1,63],"u_denominator":16},
        "native_Mellin_calibration":{"real_part":4,"heights":["0","7/3","19"],"tail_h":2},
        "coefficient_producer":"factor-free inverse plus exact normalized Dirichlet binomial powers","checker":"independent prime-power recursion, regularized incomplete gamma and auxiliary entire-integrand quadrature",
        "model_or_literature_calls":False,"historical_priority_is_acceptance_gate":False,"uniform_integer_signed_bound_proved":False,
        "remaining_assumptions":["fractional Dirichlet inverse and logarithmic integral construction language","small independent rational parameter grids","pure-power pointwise models","available local-divisor and Mellin proof methods"]}


def programs(spec):
    result=[]
    for a in map(Q,spec["coefficient_powers"]):
        for b in map(Q,spec["kernel_powers"]):
            for k in ([Q(0)] if b==0 else map(Q,spec["shifts"])):
                p={"a":str(a),"b":str(b),"kappa":str(k)}
                p["id"]=digest(p);result.append(p)
    return result


def observe(spec,ps,points):
    fs={a:coefficients(a,max(points)) for a in map(Q,spec["coefficient_powers"])}
    groups=sorted({(Q(p["b"]),Q(p["kappa"])) for p in ps});out={};hashes={str(a):digest(list(map(str,f))) for a,f in fs.items()}
    for i,(b,k) in enumerate(groups):
        measured=values(fs,b,k,points)
        for p in ps:
            if (Q(p["b"]),Q(p["kappa"]))==(b,k):out[p["id"]]={str(n):serialize(v) for n,v in measured[Q(p["a"])].items()}
        if i%8==0:print("Fractional arithmetic kernel group",i+1,"/",len(groups),flush=True)
    return out,hashes


def infer(p,response,spec):
    observations={int(n):flint.arb(v) for n,v in response.items()};tail=[v for n,v in sorted(observations.items()) if n>=16]
    ordered=sorted(tail,key=lambda v:float(v.mid()));unit=256
    proposals=[Q(0),Q(round(float(ordered[len(ordered)//2].mid())*unit),unit),Q(round(sum(float(v.mid()) for v in tail)*unit/len(tail)),unit)]
    results=[]
    for offset in sorted(set(proposals)):
        pairs=[(math.log(n),float(abs(v-real(offset)).mid().log())) for n,v in observations.items() if n>=16 and abs(v-real(offset))>0]
        growth=0.0
        if len(pairs)>=3:
            mx=sum(x for x,y in pairs)/len(pairs);my=sum(y for x,y in pairs)/len(pairs)
            growth=sum((x-mx)*(y-my) for x,y in pairs)/sum((x-mx)**2 for x,y in pairs)
        thetas={Q(j,4) for j in range(9)}|{max(Q(0),min(Q(2),Q(math.ceil(32*(growth+m)),32))) for m in (0,1/8,1/4)}
        for theta in sorted(thetas):
            top=max((abs(v-real(offset))/real(n)**real(theta)).upper() for n,v in observations.items())
            C=max(Q(1,1024),Q(int((top*2048).ceil().fmpz()),1024));cert=transfer(p["a"],p["b"],p["kappa"],theta,C,offset)
            eta=Q(cert["mellin_exponent"])
            if eta<Q(1,2):status="uniform_claim_ruled_out_by_actual_critical_zero"
            elif cert["local_divisor_obstructions"]:status="uniform_claim_ruled_out_by_local_pole_or_branch"
            elif cert["RH_sufficient_if_uniform"]:status="RH_sufficient_signed_obligation_missing_uniform_proof"
            else:status="signed_growth_obligation_above_RH_threshold"
            r={"program_id":p["id"],"offset":str(offset),"theta":str(theta),"constant":str(C),"observed_centered_growth_slope":growth,
                "transfer":cert,"analytic_status":status}
            if not cert["local_divisor_obstructions"] and eta>=Q(1,2):
                sigma=eta+Q(1,8);cost=reciprocal_cost(cert,sigma,16)
                r.update({"cost_sigma":str(sigma),"cost_height":"16","conditional_reciprocal_bound_ball":serialize(cost),"log_cost":float(cost.upper().log())})
            r["id"]=digest({k:r[k] for k in ("program_id","offset","theta","constant")});results.append(r)
    return results


def state(value,bound):
    if value<=bound:return "pass"
    if value>bound:return "fail"
    return "unresolved"


def choose(cs,ps,spec):
    lookup={p["id"]:p for p in ps};selected=[]
    def key(c):
        status=c["analytic_status"]
        rank=0 if status=="RH_sufficient_signed_obligation_missing_uniform_proof" else (1 if status=="signed_growth_obligation_above_RH_threshold" else 3)
        if c["validation_failures"] or c["validation_unresolved"]:rank=4
        return rank,Q(c["transfer"]["mellin_exponent"]),c.get("log_cost",1e100),c["id"]
    def add(pool):
        if pool:
            c=min(pool,key=key)
            if c not in selected:selected.append(c)
    add([c for c in cs if lookup[c["program_id"]]["a"]=="1" and lookup[c["program_id"]]["b"]=="0"])
    for d in range(2,spec["maximum_denominator"]+1):
        add([c for c in cs if Q(lookup[c["program_id"]]["a"])==Q(1,d) and lookup[c["program_id"]]["a"]==lookup[c["program_id"]]["b"] and lookup[c["program_id"]]["kappa"]=="1"])
    add([c for c in cs if lookup[c["program_id"]]["a"]=="1" and Q(lookup[c["program_id"]]["b"])>0 and Q(lookup[c["program_id"]]["kappa"])<=Q(1,2)])
    add([c for c in cs if c["analytic_status"]=="uniform_claim_ruled_out_by_local_pole_or_branch" and any(o["location"]=="1" for o in c["transfer"]["local_divisor_obstructions"])])
    add([c for c in cs if c["analytic_status"]=="uniform_claim_ruled_out_by_local_pole_or_branch" and any(o["kind"]=="introduced_kernel_branch_or_pole" for o in c["transfer"]["local_divisor_obstructions"])])
    for c in sorted(cs,key=key):
        if len(selected)>=spec["archive_size"]:break
        if c not in selected:selected.append(c)
    return selected


def discover(directory):
    spec=read(directory/"protocol.json");verify_code(spec);denied=restrict(directory,spec);flint.ctx.prec=spec["precision"]
    ps=programs(spec);zero,zero_audit=known_zero_rectangle(spec["known_zero_dependency"])
    observed,hashes=observe(spec,ps,spec["training_points"]);cs=[]
    for p in ps:cs.extend(infer(p,observed[p["id"]],spec))
    write(directory/"discovery_data.json",{"complete_values":observed,"coefficient_sha256":hashes})
    write(directory/"candidate_batch.json",{"programs":ps,"candidates":cs,"frozen_before_validation":True,"protocol_sha256":digest(spec),"discovery_sha256":sha(directory/"discovery_data.json")})
    validation,hashes=observe(spec,ps,spec["validation_points"])
    for c in cs:
        A,theta,C=map(Q,(c["offset"],c["theta"],c["constant"]))
        states={int(n):state(abs(flint.arb(v)-real(A)),real(C)*real(n)**real(theta)) for n,v in validation[c["program_id"]].items()}
        c["validation_failures"]=[n for n,v in states.items() if v=="fail"];c["validation_unresolved"]=[n for n,v in states.items() if v=="unresolved"]
    write(directory/"validation_data.json",{"complete_values":validation,"coefficient_sha256":hashes,"candidates":cs})
    write(directory/"archive.json",{"archive":choose(cs,ps,spec),"worker_access_denials":denied,"native_zero_audit":zero_audit,
        "final_data_used":False,"uniform_signed_bound_proved":False})
    write(directory/"seal.json",{"protocol_sha256":digest(spec),"selection_closed":True,"final_cases_exist_at_seal":False,
        "files":{n:sha(directory/n) for n in ("protocol.json","discovery_data.json","candidate_batch.json","validation_data.json","archive.json")}})
    print("Sealed fractional coefficient arithmetic",len(choose(cs,ps,spec)),"from",len(cs),"estimates",flush=True)


def final(directory):
    spec=read(directory/"protocol.json");verify_code(spec);seal=read(directory/"seal.json");flint.ctx.prec=spec["precision"]
    for n,h in seal["files"].items():assert sha(directory/n)==h
    arc=read(directory/"archive.json");path=directory/"final_cases.json"
    if path.exists():cases=read(path)
    else:
        seed=int.from_bytes(os.urandom(32),"big");rng=random.Random(seed);rule=spec["final_cases"]
        large=sorted(rng.sample(range(rule["large_range"][0],rule["large_range"][1]+1),rule["large_count"]))
        intermediate=sorted(rng.sample(range(rule["intermediate_range"][0],rule["intermediate_range"][1]+1),rule["intermediate_count"]))
        kr=spec["kernel_quadrature_calibration"]
        us=[str(Q(rng.randint(*kr["u_numerator_range"]),kr["u_denominator"])) for _ in range(kr["count"])]
        cases={"evaluator_seed":str(seed),"large":large,"intermediate":intermediate,"points":sorted(set(rule["boundary"]+intermediate+large)),
            "quadrature_u":us,"created_after_selection_closed":True,"seal_sha256":digest(seal)};write(path,cases)
    assert cases["seal_sha256"]==digest(seal)
    ps={p["id"]:p for p in read(directory/"candidate_batch.json")["programs"]};used={c["program_id"] for c in arc["archive"]}
    fs={a:coefficients(a,max(cases["points"])) for a in {Q(ps[p]["a"]) for p in used}};observed={};control={}
    N=max(cases["points"]);positive=[Q(0)]+[Q(1)]*N
    for i,pid in enumerate(sorted(used)):
        p=ps[pid];a=Q(p["a"]);f=fs[a];cut=spec["delayed_positive_cutoff"];delayed=f[:cut+1]+[Q(1)]*(N-cut)
        path=directory/("final_program_"+pid+".json");fingerprint={"seal_sha256":digest(seal),"cases_sha256":digest(cases),"code_sha256":spec["code_sha256"]}
        old=read(path) if path.exists() else {}
        if old.get("fingerprint")==fingerprint:actual,controls=old["actual"],old["controls"]
        else:
            actual={str(n):serialize(v) for n,v in values({a:f},p["b"],p["kappa"],cases["points"])[a].items()}
            measured=values({Q(1):positive,Q(2):delayed},p["b"],p["kappa"],cases["large"])
            controls={name:{str(n):serialize(v) for n,v in measured[key].items()} for name,key in (("positive",Q(1)),("delayed",Q(2)))}
            write(path,{"fingerprint":fingerprint,"actual":actual,"controls":controls})
        observed[pid]=actual;control[pid]=controls;print("Complete final fractional coefficient operator",i+1,p,flush=True)
    outcomes=[]
    for c in arc["archive"]:
        A,theta,C=map(Q,(c["offset"],c["theta"],c["constant"]))
        states={n:state(abs(flint.arb(v)-real(A)),real(C)*real(n)**real(theta)) for n,v in observed[c["program_id"]].items()}
        controls={name:{n:state(abs(flint.arb(v)-real(A)),real(C)*real(n)**real(theta)) for n,v in response.items()} for name,response in control[c["program_id"]].items()}
        outcomes.append({"candidate_id":c["id"],"point_comparisons":states,"finite_points_passed":all(v=="pass" for v in states.values()),"control_comparisons":controls,
            "positive_control_uniform_claims_ruled_out_by_pole":Q(c["transfer"]["mellin_exponent"])<1,"reselected":False,"uniform_signed_bound_proved":False})
    native=[];rule=spec["native_Mellin_calibration"]
    for pid in sorted(used):
        p=ps[pid];a,b,k=map(Q,(p["a"],p["b"],p["kappa"]));f=fs[a]
        checks=[]
        for height in rule["heights"]:
            s=flint.acb(rule["real_part"],real(height));mult=(-real(b)*(s-real(k)).log()).exp()/s
            value=(-real(a)*s.zeta().log()).exp()*mult
            partial=sum((real(f[n])*(-s*real(n).log()).exp() for n in range(1,len(f))),flint.acb(0))*mult
            tail=real(N)**real(-rule["tail_h"])*real(rule["real_part"]-rule["tail_h"]).zeta()**real(a)*abs(mult)
            assert abs(value-partial).upper()<tail.lower()
            checks.append({"height":height,"value":[serialize(value.real),serialize(value.imag)],"partial":[serialize(partial.real),serialize(partial.imag)],"tail":serialize(tail)})
        native.append({"program_id":pid,"checks":checks})
    write(directory/"final_evaluation.json",{"seal_sha256":digest(seal),"cases_sha256":digest(cases),"actual_values":observed,"control_values":control,
        "outcomes":outcomes,"coefficient_cutoff":N,"coefficient_sha256":{str(a):digest(list(map(str,f))) for a,f in fs.items()},
        "native_Mellin_checks":native,"uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False})


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("mode",choices=("run","discover","final"));parser.add_argument("--run-dir",type=Path,required=True)
    parser.add_argument("--source-run",type=Path);parser.add_argument("--branch-run",type=Path);args=parser.parse_args();directory=args.run_dir.resolve()
    if args.mode=="run":
        if directory.exists() or args.source_run is None or args.branch_run is None:raise ValueError("Fresh destination and verified source and branch runs required")
        directory.mkdir(parents=True);write(directory/"protocol.json",protocol(args.source_run,args.branch_run))
        for mode in ("discover","final"):subprocess.run([sys.executable,str(Path(__file__)),mode,"--run-dir",str(directory)],check=True,cwd=BASE)
        subprocess.run([sys.executable,str(BASE/"check_pole_neutral.py"),"--run-dir",str(directory)],check=True,cwd=BASE)
        from pole_neutral_report import publish
        publish(directory)
    elif args.mode=="discover":discover(directory)
    else:final(directory)

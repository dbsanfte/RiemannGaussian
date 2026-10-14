#!/usr/bin/env python3
"""Frozen data-driven scale operators for signed arithmetic control of zeta."""
import argparse
from fractions import Fraction as Q
import hashlib
from itertools import combinations
import json
import math
import os
from pathlib import Path
import random
import socket
import subprocess
import sys
import flint

from estimate_grammar import inverse_one_prefix
from signed_control_grammar import (atoms, critical_cost, real, prefix, residual,
    sampled_moments, complete_window_moments, positive_control_moment,
    operator_certificate, moment_transfer_certificate)

BASE = Path(__file__).resolve().parent
CODE = ["signed_control_search.py", "signed_control_grammar.py", "check_signed_control.py",
        "signed_control_report.py", "signed_control_proof.txt", "estimate_grammar.py"]


def read(path): return json.loads(Path(path).read_text())
def write(path, value): Path(path).write_text(json.dumps(value, indent=2) + "\n")
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def digest(value): return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()).hexdigest()


def protocol():
    return {"schema": 1, "objective": "signed arithmetic control of ordinary zeta across all scales, toward RH",
            "historical_priority_is_acceptance_gate": False,
            "code_sha256": {name: sha(BASE/name) for name in CODE}, "seed": 2026100731,
            "coefficient_source": "constant-one Dirichlet inverse by triangular divisor rows; no prime/factor oracle",
            "scale_dictionary": list(range(2, 17)), "orders": [2, 4, 6, 8],
            "training_scales": list(range(1, 16))+[16,24,32,48,64,96,128,192,256,384,512,768,1024,1536,2048,3072,4096],
            "validation_scales": [6144,8192,12289,16384,24577,32768,49157,65536],
            "moment_observations_in_development": "uniform sample of declared unit cells; exact within sampled cells, not a complete window integral",
            "sampled_cells_per_window": 24, "least_squares_weights": "1/X, on training integer cumulative responses",
            "coefficient_rounding_denominator": 512, "projection_denominator": 1024,
            "critical_inverse_cost_cap": "3/4", "fit_pair_budget": 80, "fit_triple_budget": 120,
            "random_program_budget": 80, "archive_size": 8,
            "growth_inference": "OLS log(moment) against log(X), add 1/8 then round upward to 1/16; fit constant from all training windows with factor 2",
            "growth_exponent_range": "0<=beta<=q+1; infer beta, do not require a predicted formula",
            "selection": "preserve baseline and one per construction family; then least certified-bridge pointwise exponent, retaining inverse and Lipschitz costs",
            "final_cases": {"fresh_large_windows": 6, "X_range": [131073,524287], "fresh_intermediate_windows": 3,
                            "intermediate_X_range": [17,8191], "fixed_boundary_windows": [1,2,3,15]},
            "maximum_final_coefficient_cutoff": 1048574, "precision": 320,
            "final_evaluation": "separate process after sealing; evaluator-owned OS entropy; exact complete window integrals; no reselection",
            "control_families": ["all-positive coefficients", "actual inverse through 4096 then all-positive"],
            "remaining_assumptions": ["finite integer-scale recurrence language", "at most three scale terms",
                                      "even moments through eight", "bounded moment and inverse certificate methods"],
            "finite_success_is_uniform_proof": False, "model_or_literature_calls_in_generator_selector": False}


def verify_code(spec):
    for name, expected in spec["code_sha256"].items():
        if sha(BASE/name) != expected: raise ValueError("frozen signed-control code changed: "+name)


def restrict_worker(directory):
    allowed = {str((directory/name).resolve()) for name in
               ("protocol.json","discovery_data.json","candidate_batch.json","validation_data.json","archive.json","seal.json")}
    allowed |= {str((BASE/name).resolve()) for name in CODE}
    allowed |= {str((BASE/name).resolve()) for name in
                ("shift-ratio-results/shift_ratio_analytic_verification.json","shift-ratio-results/shift_ratio_analytic.json")}
    def audit(event, args):
        if event == "open" and not isinstance(args[0], int):
            if str(Path(args[0]).resolve()) not in allowed: raise PermissionError("worker file access denied")
        if event.startswith("socket.") or event in ("subprocess.Popen","os.system","os.posix_spawn","os.posix_spawnp"):
            raise PermissionError("worker external access denied")
    sys.addaudithook(audit)
    denials = {}
    for name, action in (("private_final_file",lambda: open(directory/"final_evaluation.json")),
                         ("network",lambda: socket.socket()),
                         ("subprocess",lambda: subprocess.run([sys.executable,"-c","pass"]))):
        try: action()
        except PermissionError: denials[name] = True
        else: raise AssertionError("discovery access restriction failed")
    return denials


def solve(matrix, vector):
    size = len(vector)
    augmented = [list(row)+[v] for row,v in zip(matrix,vector)]
    for j in range(size):
        pivot = next((i for i in range(j,size) if augmented[i][j]),None)
        if pivot is None: return None
        augmented[j],augmented[pivot] = augmented[pivot],augmented[j]
        z = augmented[j][j]; augmented[j] = [x/z for x in augmented[j]]
        for i in range(size):
            if i != j:
                z = augmented[i][j]
                augmented[i] = [a-z*b for a,b in zip(augmented[i],augmented[j])]
    return [row[-1] for row in augmented]


def project(rows, spec):
    rows = atoms([(d,Q(round(max(Q(-8),min(Q(8),a))*spec["coefficient_rounding_denominator"]),
                       spec["coefficient_rounding_denominator"])) for d,a in rows])
    cost = critical_cost(rows)
    cap = Q(spec["critical_inverse_cost_cap"])
    if rows and not cost < real(cap):
        unit = spec["projection_denominator"]
        floor = (real(cap-Q(1,unit))/cost*unit).floor()
        factor = Q(int(floor.fmpz()),unit)
        rows = atoms([(d,a*factor) for d,a in rows])
    assert critical_cost(rows) < real(cap)
    return [[d,str(a)] for d,a in rows]


def generate(mu,M,spec):
    rng = random.Random(spec["seed"])
    divisors = spec["scale_dictionary"]
    scales = [X for X in spec["training_scales"] if X>=16]
    columns = {d:[residual(mu,M,[[d,"-1"]],X)-Q(M[X]) for X in scales] for d in divisors}
    gram = {(d,e):sum((a*b/X for a,b,X in zip(columns[d],columns[e],scales)),Q(0)) for d in divisors for e in divisors}
    rhs = {d:sum((a*M[X]/X for a,X in zip(columns[d],scales)),Q(0)) for d in divisors}
    proposals = [("baseline",[],"unfiltered signed cumulative sum")]
    rejected = []
    for size,budget in ((1,len(divisors)),(2,spec["fit_pair_budget"]),(3,spec["fit_triple_budget"])):
        supports = list(combinations(divisors,size))
        supports = sorted(rng.sample(supports,min(budget,len(supports))))
        for support in supports:
            coefficients = solve([[gram[d,e] for e in support] for d in support],[rhs[d] for d in support])
            if coefficients is None:
                rejected.append({"support":list(support),"reason":"singular training feature matrix"}); continue
            proposals.append((f"fit_{size}_scales",project(list(zip(support,coefficients)),spec),"exact weighted least squares, quantization and critical-cost projection"))
    for _ in range(spec["random_program_budget"]):
        support = sorted(rng.sample(divisors,rng.randint(1,3)))
        rows = project([(d,Q(rng.randint(-8,8),8)) for d in support],spec)
        proposals.append(("random_signed",rows,"seeded signed rational exploration"))
    programs = []; seen = set()
    for family,rows,method in proposals:
        key = digest(rows)
        if key in seen:
            rejected.append({"atoms":rows,"reason":"exact duplicate after projection"}); continue
        seen.add(key)
        programs.append({"id":key,"family":family,"atoms":rows,"fit_method":method,
                         "operator_certificate":operator_certificate(rows)})
    return programs,rejected


def cell_cases(scales, count, seed):
    rng = random.Random(seed)
    return {str(X):sorted(rng.sample(range(X,2*X),min(count,X))) for X in scales}


def fit_growth(observations, order):
    points = [(math.log(X),math.log(float(value))) for X,value in observations.items() if X>=16 and value>0]
    center_x = sum(x for x,y in points)/len(points); center_y = sum(y for x,y in points)/len(points)
    slope = sum((x-center_x)*(y-center_y) for x,y in points)/sum((x-center_x)**2 for x,y in points)
    beta = min(Q(order+1),max(Q(0),Q(math.ceil(16*(slope+0.125)),16)))
    maximum = max((real(value)/real(X)**real(beta)).upper() for X,value in observations.items())*2*1024
    C = Q(int(maximum.ceil().fmpz()),1024)
    return {"order":order,"beta":str(beta),"constant":str(C),"observed_loglog_slope":slope,
            "constant_source":"training only; factor two margin and upward 1/1024 rounding",
            "uniform_premise_proved":False}


def known_zero_dependency():
    path = BASE/"shift-ratio-results/shift_ratio_analytic_verification.json"
    source = BASE/"shift-ratio-results/shift_ratio_analytic.json"
    checked = read(path)
    assert checked["all_passed"] and checked["source_artifact_sha256"] == sha(source)
    row = checked["actual_zero_and_corridor_audit"]["records"][0]
    return {"verification_sha256":sha(path),"source_sha256":sha(source),"centre":row["disk_centre"],
            "radius":row["fresh_nested_Rouche_radius"],"scope":"previously certified simple critical-line zero; reflection and uniqueness"}


def discover(directory):
    spec = read(directory/"protocol.json"); verify_code(spec)
    denials = restrict_worker(directory)
    flint.ctx.prec = spec["precision"]
    scales = spec["training_scales"]+spec["validation_scales"]
    mu = inverse_one_prefix(2*max(scales)); M = prefix(mu)
    train_cells = cell_cases(spec["training_scales"],spec["sampled_cells_per_window"],spec["seed"]+1)
    write(directory/"discovery_data.json",{"protocol_sha256":digest(spec),"cells":train_cells,
          "coefficient_cutoff":len(mu)-1,"inverse_coefficient_sha256":digest(mu),"fit_responses":{str(X):M[X] for X in spec["training_scales"]}})
    programs,rejected = generate(mu,M,spec)
    batch = {"protocol_sha256":digest(spec),"discovery_sha256":sha(directory/"discovery_data.json"),
             "programs":programs,"rejected":rejected,"frozen_before_validation":True}
    write(directory/"candidate_batch.json",batch)
    validation_cells = cell_cases(spec["validation_scales"],spec["sampled_cells_per_window"],spec["seed"]+2)
    records = []; zero = known_zero_dependency()
    for index,program in enumerate(programs):
        training = sampled_moments(mu,M,program["atoms"],spec["training_scales"],spec["orders"],train_cells)
        validation = sampled_moments(mu,M,program["atoms"],spec["validation_scales"],spec["orders"],validation_cells)
        estimates = []
        for order in spec["orders"]:
            estimate = fit_growth({X:r[order] for X,r in training.items()},order)
            beta,C = Q(estimate["beta"]),Q(estimate["constant"])
            failures = [X for X,r in validation.items() if not real(r[order])<=real(C)*real(X)**real(beta)]
            transfer = moment_transfer_certificate(program["atoms"],order,beta)
            impossible = Q(transfer["pointwise_exponent"])<Q(1,2)
            estimate.update({"validation_sample_failures":failures,"known_zero_rules_out_uniform_claim":impossible,
                             "status":"ruled_out_by_ordinary_zeta_zero" if impossible else
                                      ("falsified_on_sampled_validation" if failures else "numerical_lead_missing_uniform_signed_moment_proof"),
                             "moment_to_signed_pointwise_transfer":transfer})
            estimates.append(estimate)
        eligible = [r for r in estimates if r["status"]=="numerical_lead_missing_uniform_signed_moment_proof"]
        score = min((Q(r["moment_to_signed_pointwise_transfer"]["pointwise_exponent"]) for r in eligible),default=Q(2))
        record = {"program":program,"sampled_training_moments":{str(X):{str(q):str(v) for q,v in r.items()} for X,r in training.items()},
                  "sampled_validation_moments":{str(X):{str(q):str(v) for q,v in r.items()} for X,r in validation.items()},
                  "estimates":estimates,"selection_pointwise_exponent":str(score),
                  "selection_inverse_cost_ball":program["operator_certificate"]["critical_inverse_cost_ball"]}
        records.append(record)
        if index%50==0: print("Signed operator development",index,"/",len(programs),flush=True)
    write(directory/"validation_data.json",{"cells":validation_cells,"records":records,"observations_are_sampled_window_estimates":True})
    def key(r):
        return Q(r["selection_pointwise_exponent"]),len(r["program"]["atoms"]),r["program"]["id"]
    chosen = []; families = ["baseline","fit_1_scales","fit_2_scales","fit_3_scales","random_signed"]
    for family in families:
        rows = [r for r in records if r["program"]["family"]==family]
        if rows: chosen.append(min(rows,key=key))
    for row in sorted(records,key=key):
        if len(chosen)>=spec["archive_size"]: break
        if row not in chosen: chosen.append(row)
    archive = {"protocol_sha256":digest(spec),"batch_sha256":digest(batch),"archive":chosen,
               "known_zero_dependency":zero,"worker_access_denials":denials,
               "final_data_used":False,"historical_priority_used":False,
               "uniform_sublinear_signed_control_proved":False}
    write(directory/"archive.json",archive)
    write(directory/"seal.json",{"protocol_sha256":digest(spec),"files":{name:sha(directory/name) for name in
          ("protocol.json","discovery_data.json","candidate_batch.json","validation_data.json","archive.json")},
          "selection_closed":True,"final_cases_exist_at_seal":False})
    print("Sealed signed-control archive",len(chosen),"from",len(programs),"programs",flush=True)


def verify_seal(directory):
    spec,seal = read(directory/"protocol.json"),read(directory/"seal.json")
    verify_code(spec)
    assert seal["protocol_sha256"]==digest(spec) and seal["selection_closed"]
    for name,expected in seal["files"].items():
        assert sha(directory/name)==expected,"sealed data changed: "+name
    return spec,seal


def final_evaluation(directory):
    spec,seal = verify_seal(directory); archive = read(directory/"archive.json")
    flint.ctx.prec = spec["precision"]
    cases_path = directory/"final_cases.json"
    if cases_path.exists(): cases = read(cases_path)
    else:
        seed = int.from_bytes(os.urandom(32),"big"); rng = random.Random(seed); rule = spec["final_cases"]
        large = sorted(rng.sample(range(rule["X_range"][0],rule["X_range"][1]+1),rule["fresh_large_windows"]))
        intermediate = sorted(rng.sample(range(rule["intermediate_X_range"][0],rule["intermediate_X_range"][1]+1),rule["fresh_intermediate_windows"]))
        cases = {"seal_sha256":digest(seal),"evaluator_seed":str(seed),"large":large,
                 "scales":sorted(set(rule["fixed_boundary_windows"]+intermediate+large)),"created_after_selection_closed":True}
        write(cases_path,cases)
    assert cases["seal_sha256"]==digest(seal) and cases["created_after_selection_closed"]
    mu = inverse_one_prefix(2*max(cases["scales"])); M = prefix(mu)
    assert len(mu)-1<=spec["maximum_final_coefficient_cutoff"]
    records = []
    for index,row in enumerate(archive["archive"]):
        program = row["program"]; component = directory/("final_program_"+program["id"]+".json")
        fp = {"archive_sha256":digest(archive),"final_cases_sha256":digest(cases),"code_sha256":spec["code_sha256"]}
        previous = read(component) if component.exists() else {}
        if previous.get("fingerprint")==fp:
            records.append(previous["record"]); print("Reused signed final operator",index,flush=True); continue
        exact = complete_window_moments(mu,M,program["atoms"],cases["scales"],spec["orders"])
        outcomes = []
        for estimate in row["estimates"]:
            q,beta,C = estimate["order"],Q(estimate["beta"]),Q(estimate["constant"])
            failures = [X for X,r in exact.items() if not real(r[q])<=real(C)*real(X)**real(beta)]
            controls = []
            for name,offset in (("all_positive",0),("finite_inverse_then_positive",M[4096]-4096)):
                values = {X:positive_control_moment(program["atoms"],X,q,offset) for X in cases["large"]}
                rejected = [X for X,v in values.items() if not real(v)<=real(C)*real(X)**real(beta)]
                controls.append({"name":name,"moments":{str(X):str(v) for X,v in values.items()},
                                 "finite_failure_windows":rejected,"uniform_sublinear_claim_false":beta<q+1})
            outcomes.append({"order":q,"beta":str(beta),"constant":str(C),"complete_final_failure_windows":failures,
                             "finite_validation_passed":not failures,"controls":controls,
                             "uniform_moment_bound_proved":False,"operator_or_archive_reselected":False})
        record = {"program_id":program["id"],"exact_window_moments":{str(X):{str(q):str(v) for q,v in r.items()} for X,r in exact.items()},
                  "estimate_outcomes":outcomes,"every_unit_interval_included":True}
        write(component,{"fingerprint":fp,"record":record}); records.append(record)
        print("Complete signed final operator",index,program["family"],flush=True)
    output = {"seal_sha256":digest(seal),"final_cases_sha256":digest(cases),"records":records,
              "coefficient_cutoff":len(mu)-1,"inverse_coefficient_sha256":digest(mu),
              "selection_closed_before_final_data":True,"finite_success_is_all_scale_proof":False,
              "uniform_sublinear_signed_controls_verified":[],"RH_proved":False}
    write(directory/"final_evaluation.json",output)
    print("Final signed-control evaluation complete",len(records),flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode",choices=("run","discover","final"))
    parser.add_argument("--run-dir",type=Path,required=True)
    args = parser.parse_args(); directory = args.run_dir.resolve()
    if args.mode=="run":
        if directory.exists(): raise ValueError("A new run requires a fresh destination")
        directory.mkdir(parents=True); write(directory/"protocol.json",protocol())
        for mode in ("discover","final"):
            subprocess.run([sys.executable,str(Path(__file__)),mode,"--run-dir",str(directory)],check=True,cwd=BASE)
        subprocess.run([sys.executable,str(BASE/"check_signed_control.py"),"--run-dir",str(directory)],check=True,cwd=BASE)
        from signed_control_report import publish
        publish(directory)
    elif args.mode=="discover": discover(directory)
    else: final_evaluation(directory)


if __name__=="__main__": main()

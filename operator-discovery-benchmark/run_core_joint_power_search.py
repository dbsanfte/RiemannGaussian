"""One immutable joint source-control search, with independent proof replay."""
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time
from flint import arb, ctx
from prime_bank_candidates import Meter
import core_joint_power_search as P
import check_core_joint_power_search as C
import check_core_prefix_proof_search as PREFIX_CHECK
import run_core_prefix_proof_search as PRIOR


ROOT = Path(__file__).resolve().parent
INPUT = 'candidate10_prefix_proof_obligation.json'
PARENT = ROOT/'core-prefix-proof-results/pilot-001'
OUT = ROOT/'core-joint-power-results/pilot-001'
TESTS = ['test_core_joint_power_search','test_check_core_joint_power_search']
RECEIPTS = ['core_joint_power_search_development.json','core_joint_power_checker_development.json']
FILES = ['core_joint_power_search.py','check_core_joint_power_search.py','run_core_joint_power_search.py',
         'core_joint_power_search_protocol.txt','check_core_prefix_proof_search.py',
         'prime_bank_candidates.py','potential_candidate_language.py',INPUT]+[t+'.py' for t in TESTS]+RECEIPTS
CAP = 200000000


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def verify():
    PRIOR.verify()
    for name in read(OUT/'source_files.json'):
        if (ROOT/name).read_bytes() != (OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen source '+name)
    for name in read(OUT/'parent_proof_files.json'):
        if (PARENT/name).read_bytes() != (OUT/'parent_proof_snapshot'/name).read_bytes():
            raise ValueError('changed inherited proof artifact '+name)


def main():
    start = time.monotonic()
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4*1024**3, hard))
    ctx.prec = 192
    PRIOR.verify()
    if read(PARENT/'report.json')['status'] != 'SIGNED_PREFIX_PROOF_SEARCH_VERIFIED_WITH_OPEN_JOINED_GOALS':
        raise ValueError('completed previous source-bound proof search')
    if (ROOT/INPUT).read_bytes() != (PARENT/'publication-001/next_search_input.json').read_bytes():
        raise ValueError('current published source obligation')
    prior = read(ROOT/INPUT)
    if prior['whole_signed_bound_proved'] or prior['RH_proved']:
        raise ValueError('unresolved signed goal required')
    rows = prior['parent_obligation']['source_geometries']
    parents = prior['generated_prefix_bound_obligations']
    constructions = {o['id']: o['construction'] for o in
        prior['parent_obligation']['parent_obligation']['generated_bound_program_obligations']}
    expected = {(row['id'], ident) for row in rows for ident in constructions}
    actual = [(p['geometry_id'],p['parent_obligation_id']) for p in parents]
    if len(set(actual)) != len(actual) or set(actual) != expected:
        raise ValueError('complete current geometry and source bindings')
    development = [read(ROOT/name) for name in RECEIPTS]
    if any(d['runs'][-1]['returncode'] or d['operations'] != sum(r['operations'] for r in d['runs']) for d in development):
        raise ValueError('passed complete owned development receipts')
    if OUT.exists():
        raise FileExistsError('one immutable study, preserve terminal outcomes')
    OUT.mkdir(parents=True)
    (OUT/'source_snapshot').mkdir()
    (OUT/'parent_proof_snapshot').mkdir()
    for name in FILES:
        (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    parent_files = ['geometry-'+str(row['id'])+'.json' for row in rows]+['source_scalar.json']
    for name in parent_files:
        (OUT/'parent_proof_snapshot'/name).write_bytes((PARENT/name).read_bytes())
    write(OUT/'source_files.json', FILES)
    write(OUT/'parent_proof_files.json', parent_files)
    write(OUT/'protocol.json', dict(schema='joint-power-source-control-run-v1', input=INPUT,
        geometry_ids=[r['id'] for r in rows], parent_bindings=len(parents),
        theta_grammar=list(P.THETAS), subset_search='every subset of finite-factor source pieces including no change',
        selection='certified eligible-subsum N power, log degree, unpaid component count, introduced remainders, mask',
        analyst_supplied=['integral power remainder theorem', 'finite moment multiplicativity',
                         'finite norm bounds', 'Abel and norm recovery inequalities', 'grammar and ranking policy'],
        detector_generated=['compatible power increment', 'exact signed moment coefficients', 'joint drift polynomials',
                            'centering subset', 'uniformly controlled remainders', 'remaining whole signed expression'],
        prior_proof_check='fast independent rule replay and full selected recovery; no old optimization rerun',
        numerical_source_evaluations=0, model_calls_in_search=0, source_values_used_for_selection=False,
        memory_limit_bytes=4*1024**3, runtime_limit_seconds=900, inclusive_operation_cap=CAP,
        hashes=False, whole_signed_bound_proved=False, RH_proved=False))
    meter = Meter(CAP, 900)
    meter.charge(1000000)
    test_start = time.monotonic()
    tests = subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,
                           capture_output=True,text=True,timeout=300)
    test_ops = sum(map(int,re.findall(r'operations=(\d+)',tests.stdout)))
    write(OUT/'frozen_tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr,
        operations=test_ops,elapsed_seconds=time.monotonic()-test_start))
    if tests.returncode:
        raise RuntimeError('frozen independent suites failed')
    scalar = read(OUT/'parent_proof_snapshot/source_scalar.json')
    if scalar['absolute_R_u_bound'] != '5' or scalar['beta'] != '9/2' or not abs(arb(scalar['R_u'])) < 5:
        raise ValueError('inherited complete source scalar envelope')
    results, checks, summaries = {}, [], []
    for row in rows:
        PREFIX_CHECK._source_terms(row, meter)
        prefix = read(OUT/'parent_proof_snapshot'/('geometry-'+str(row['id'])+'.json'))
        bound_parents = [p for p in parents if p['geometry_id'] == row['id']]
        refs = bound_parents[0]['remaining_signed_pieces']
        if any(p['remaining_signed_pieces'] != refs for p in bound_parents):
            raise ValueError('common exact source representation across bound channels')
        result = P.search(row, prefix, refs, meter)
        checked = C.verify_search(row, prefix, refs, result, meter)
        if not checked['verified']:
            raise ArithmeticError('independent source-control proof replay')
        results[row['id']] = result
        checks.append(checked)
        write(OUT/('geometry-'+str(row['id'])+'.json'),result)
        selected = result['alternatives'][result['selected_mask']]
        baseline = result['alternatives'][0]
        summary = dict(geometry_id=row['id'],alpha=row['alpha'],gamma=row['gamma'],
            selected_mask=result['selected_mask'],baseline_subsum_score=baseline['score'],
            selected_subsum_score=selected['score'],statistics=result['statistics'],
            selected_remainders=selected['remainders'],joint_drifts=selected['joint_drifts'])
        summaries.append(summary)
        print(json.dumps(dict(geometry=row['id'],verified=True,baseline_score=baseline['score'],
            selected_score=selected['score'],**result['statistics'])),flush=True)
    reductions, reduction_checks = [], []
    for parent in parents:
        result = results[parent['geometry_id']]
        construction = constructions[parent['parent_obligation_id']]
        reduction = P.reduction(parent,construction,result)
        reductions.append(reduction)
        reduction_checks.append(C.verify_reduction(parent,construction,result,reduction,meter))
    write(OUT/'verification.json',dict(search_checks=checks,reduction_checks=reduction_checks))
    write(OUT/'reductions.json',reductions)
    next_input = dict(schema='joint-power-control-feedback-v1',status='open',parent_obligation=prior,
        generated_joint_power_obligations=reductions,search_results=summaries,
        current_joint_moment_variables=['m_theta(A)','m_theta(B)','c_U','R_u'],
        next_priority='Search control of the exact joint drift together with all remaining inverse residual terms; no separately bounded drift or discarded drift cross may stand in for the whole signed inequality',
        detector_generates_joint_controls=True, detector_has_general_analytic_prover=False,
        supplied_rules_recorded=True, new_source_observations=0,
        original_target_and_all_corrections_retained=True,
        whole_signed_bound_proved=False,all_scale_signed_control_proved=False,RH_proved=False)
    write(OUT/'next_search_input.json',next_input)
    total = meter.operations+test_ops+sum(d['operations'] for d in development)
    if total > CAP:
        raise OverflowError('inclusive operation cap')
    verify()
    report = dict(status='JOINT_POWER_CONTROLS_VERIFIED_WITH_OPEN_SIGNED_DRIFT',source_geometries=len(rows),
        subsets=sum(r['statistics']['subsets'] for r in results.values()),
        profile_trials=sum(r['statistics']['profile_trials'] for r in results.values()),
        selected_paid_remainders=sum(r['statistics']['selected_paid_remainders'] for r in results.values()),
        reduction_bindings=len(reductions),geometry_summary=summaries,
        whole_signed_bounds_proved=0, numerical_source_evaluations=0,model_calls_in_search=0,
        main_operations=meter.operations,inclusive_operations=total,
        elapsed_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        whole_signed_bound_proved=False,RH_proved=False)
    write(OUT/'report.json',report)
    print(json.dumps({k:v for k,v in report.items() if k!='geometry_summary'}),flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        if OUT.exists() and not (OUT/'report.json').exists() and not (OUT/'terminal_failure.json').exists():
            write(OUT/'terminal_failure.json',dict(status='incomplete',error_type=type(error).__name__,error=str(error),
                whole_signed_bound_proved=False,RH_proved=False))
        raise

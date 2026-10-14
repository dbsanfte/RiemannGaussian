"""Freeze and evaluate analytic short-repair recipes on saved062 bases."""
import os
for _native_thread_variable in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[_native_thread_variable]='1'

from fractions import Fraction as Q
import json
import multiprocessing as mp
import resource
import time

import mobius_prefix_repair_063 as SEARCH
import check_mobius_prefix_repair_063 as REPAIR
import check_mobius_prefix_completion_062 as WHOLE
import run_mobius_prefix_completion_062 as PRIOR
from run_fractional_prime_kernel_051 import write,emit,check_receipt

ROOT=PRIOR.ROOT
OUT=PRIOR.OUT/'analytic_repair_followup_001'
FILES=['mobius_prefix_repair_063.py','test_mobius_prefix_repair_063.py',
       'mobius_prefix_repair_search_063_development.json',
       'check_mobius_prefix_repair_063.py','test_check_mobius_prefix_repair_063.py',
       'mobius_prefix_repair_checker_063_development.json','MOBIUS_PREFIX_REPAIR_CHECK_SCOPE_063.txt',
       'MOBIUS_PREFIX_REPAIR_REVIEW_063.txt','run_mobius_prefix_repair_063.py','mobius_prefix_repair_protocol_063.txt']
SPEC={'recipes':list(SEARCH.RULES),'bases':'all36 saved062 generic_indicator_inverse certificates',
      'new_LP_or_arithmetic_source_prefix_values':False,
      'quadratic_lift':'each fixed-case winner; f and G are mu-free and fills are linear',
      'cutoff_dependency_ranking':'minimize max(eta,1-eta); selects1/2 independently of finite budgets',
      'workers':3,'native_threads_per_worker':1,'maximum_aggregate_bytes':16*1024**3,
      'module_seconds':7200,'work_cap_per_meter':300_000_000_000,
      'uniform_budget_growth_claim':False}


def validate_parent():
    counts=PRIOR.validate_parent();directory=PRIOR.OUT/'source_snapshot'
    if sorted(p.name for p in directory.iterdir())!=sorted(PRIOR.FILES):raise ValueError('complete062 snapshot')
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(directory/name).read_bytes():raise ValueError('preserve062 '+name)
    report=json.loads((PRIOR.OUT/'report.json').read_text())
    if report['exact_certificates_independently_verified']!=108 or report['uniform_budget_growth_proved'] or report['RH_proved']:
        raise ValueError('062 finite prefix proof and open uniform budget binding')
    return counts+[len(PRIOR.FILES)]


def evaluate_task(name):
    started=time.monotonic();saved=json.loads((PRIOR.OUT/name).read_text())
    baseline=next(c for c in saved['candidates'] if c['kind']=='generic_indicator_inverse')
    if not baseline['admitted'] or not baseline['verification']['finite_prefix_bound_proved']:
        raise ValueError('saved generic completion proof')
    base=baseline['certificate'];meter=SEARCH.Meter(cap=SPEC['work_cap_per_meter'],seconds=7200)
    rm=REPAIR.Meter(cap=SPEC['work_cap_per_meter'],seconds=7200)
    wm=WHOLE.Meter(cap=SPEC['work_cap_per_meter'],seconds=7200)
    result=SEARCH.discover(base,meter)
    for candidate in result['candidates']:
        candidate['repair_verification']=REPAIR.verify_repair(candidate['repair'],rm)
        candidate['whole_verification']=WHOLE.verify_completion(candidate['completion'],wm)
        if any(Q(e['short_residual_l1']) for e in candidate['whole_verification']['endpoint_costs']):
            raise ValueError('every actual short source row must be repaired')
    chosen=next(c for c in result['candidates'] if c['rule']==result['selected_rule'])
    result['selected_quadratic_lift']=SEARCH.quadratic_lift(base,chosen['rule'],chosen['repair'],meter)
    result.update({'source_base_file':name,'theta':saved['theta'],
        'old062_selected_budget':saved['selected_budget'],'old062_selected_kind':saved['selected_kind'],
        'producer_operations':meter.operations,'repair_checker_operations':rm.operations,
        'whole_checker_operations':wm.operations,'elapsed_seconds':time.monotonic()-started,
        'prospective_algorithm_bytes':meter.peak_bytes_estimate,
        'worker_peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss})
    return result


def feedback(params,parent):
    return {'schema':'mobius-analytic-repair-feedback-v1','source_parameters':params,
        'previous_goal_turn':'062 substantive: automatic finite prefix completion bounds; uniform growth open',
        'current_goal_turn':'063 substantive: exact analytic repair recipes, arithmetic dependency audit, and factored quadratic cancellation target',
        'parent_target':parent['target'],'conditional_core_recovery':parent['conditional_core_recovery'],
        'repair_identity':{'formula':'A_j=sum_(m<=H/j)mu(m)*g_(j*m); c_j=A_j-A_(j+1)',
            'exact_conclusion':'sum_(j<=H)c_j*floor(j/d)=g_d at every positive integer d',
            'g':'linear fill P of the exact short residual, unchanged at every coprime d',
            'norm':'sum_j|A_j-A_(j+1)|, joint in r=p/q through1',
            'full_row_inverse_unique':True,'coprime_row_inverse_unique':False},
        'generic_long_identification':'062 generic long coefficients are exactly the j>H block of the unique full-row source inverse, with every truncated threshold retained',
        'current_scale_information_guard':{'indicator':'c_j=M(floor(T/j))-M(floor(T/(j+1))); c1 is a current-scale interval',
            'mask':'free fills change the repair but leave its masked signed convolution invariant',
            'no_short_support_implies_small_cost':True},
        'quadratic_target':{'formula':'c=Delta D(u) P(f-G*u), u_m=ordinary mu(m), SAME u in both factors',
            'source_free_factors':'f, G and each fill matrix P are built from floors, cutoffs, registered primes and rational weights without mu values',
            'degree_at_most':2,'arithmetic_radius':'B=max(H,floor(y/(H+1)))<=max(H,floor(D/(H+1)))',
            'general_eta':'H=floor(N^eta) gives B=O(N^max(eta,1-eta))',
            'smallest_query_exponent':'1/2, at eta=1/2; this does not assert budget growth',
            'required_estimate':'uniform joint total variation of Delta D(u)P(f-G*u) bounded by O_kappa(N^(1/2+kappa)) for every prefix and kappa>0',
            'paid_long_component':'generic long L1 is O(N/H*log(4N/H)); eta1/2 pays it',
            'source_only_general_derivation_reviewed':True,'new_quadratic_schema_machine_admission':False,
            'finite_factor_replays_match_independently_verified_whole_completions':True,
            'uniform_quadratic_variation_bound_proved':False},
        'next_search_input':{'target':'the signed quadratic variation, retaining shared u and its multiplicative constraints',
            'constructions':['structured factorizations and pairings of the two-index arithmetic kernel',
                'telescoping identities across repair index j with a paid absolute-variation bound',
                'gcd-aware interactions using mu(a)*mu(b)=mu(ab) only when gcd(a,b)=1; overlap squares retained'],
            'forbidden_shortcut':'smaller arithmetic query radius is not a contraction of the quadratic norm',
            'no_uncontrolled_current_scale_boundary':True,'no_Mertens_or_RH_provider_assumed':True},
        'uniform_repair_growth_proved':False,'uniform_core_bound_proved':False,
        'uniform_RH_strength_bound_proved':False,'RH_proved':False,'RH_refuted':False}


def main():
    if OUT.exists():raise FileExistsError('preserve every063 attempt')
    started=time.monotonic();counts=validate_parent()
    parent=json.loads((PRIOR.OUT/'mechanism_feedback.json').read_text());params=parent['source_parameters']
    frozen={name:(ROOT/name).read_bytes() for name in FILES}
    development=sum(check_receipt(json.loads(data)) for name,data in frozen.items() if name.endswith('_development.json'))
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name,data in frozen.items():(OUT/'source_snapshot'/name).write_bytes(data)
    results=[]
    try:
        write(OUT/'spec.json',{'spec':SPEC,'parameters':params,'prior_frozen_counts':counts,
            'new_frozen_files':len(FILES),'frozen_before_new_repair_search':True,'hashes_used':False})
        names=sorted(p.name for p in PRIOR.OUT.glob('completion_*.json'))
        if len(names)!=36:raise ValueError('all36 saved source-bound generic bases')
        emit('analytic_repair_started',cases=len(names),recipes=len(SEARCH.RULES),workers=SPEC['workers'])
        with mp.get_context('fork').Pool(SPEC['workers']) as pool:
            for result in pool.imap_unordered(evaluate_task,names,chunksize=1):
                name='repair_'+result['source_base_file'].removeprefix('completion_')
                write(OUT/name,result);results.append(result)
                emit('analytic_repair_checked',N=result['N'],y=result['y'],H=result['H'],
                    rule=result['selected_rule'],budget=result['selected_budget'],
                    arithmetic_radius=result['selected_quadratic_lift']['arithmetic_radius'],
                    completed=len(results),total=len(names))
        results.sort(key=lambda r:(r['N'],r['y'],Q(r['theta'])))
        rows=[]
        for result in results:
            for candidate in result['candidates']:
                rows.append({'N':result['N'],'y':result['y'],'H':result['H'],'theta':result['theta'],
                    'rule':candidate['rule'],'new_budget':candidate['new_budget'],
                    'repair_endpoint_l1':candidate['repair']['coefficient_l1'],
                    'base_budget':result['base_budget'],'old062_selected_budget':result['old062_selected_budget']})
        write(OUT/'summary.json',{'rows':rows,'finite_recipe_comparison_only':True,'uniform_budget_growth_proved':False})
        write(OUT/'mechanism_feedback.json',feedback(params,parent))
        validate_parent()
        if any((ROOT/name).read_bytes()!=data for name,data in frozen.items()):raise ValueError('preserve frozen063 sources')
        report={'status':'EXACT_ANALYTIC_REPAIR_AND_QUADRATIC_LIFT_UNIFORM_VARIATION_OPEN',
            'fixed_N_y_H_cases':len(results),'analytic_recipes':len(SEARCH.RULES),
            'exact_repair_certificates_verified':len(rows),'new_whole_prefix_certificates_verified':len(rows),
            'selected_factored_quadratic_replays':len(results),
            'cases_improving_generic_budget':sum(Q(r['selected_budget'])<Q(r['base_budget']) for r in results),
            'cases_matching_or_improving_old_LP':sum(Q(r['selected_budget'])<=Q(r['old062_selected_budget']) for r in results),
            'new_synthetic_tests':28,'development_operations':development,
            'producer_operations':sum(r['producer_operations'] for r in results),
            'repair_checker_operations':sum(r['repair_checker_operations'] for r in results),
            'whole_checker_operations':sum(r['whole_checker_operations'] for r in results),
            'elapsed_seconds':time.monotonic()-started,
            'parent_peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'largest_worker_peak_rss_kib':max(r['worker_peak_rss_kib'] for r in results),
            'largest_prospective_algorithm_bytes':max(r['prospective_algorithm_bytes'] for r in results),
            'workers':SPEC['workers'],'native_threads_per_worker':1,'prior_frozen_counts':counts,
            'new_frozen_source_count':len(FILES),'hashes_used':False,'old_suites_or_studies_replayed':False,
            'new_LP_used':False,'original_source_prefix_sums_or_integrals_evaluated':False,
            'new_short_inverse_arithmetic_evaluated':True,'query_radius_reduction_has_reviewed_general_proof':True,
            'quadratic_schema_independently_machine_admitted':False,
            'uniform_quadratic_variation_bound_proved':False,'uniform_core_bound_proved':False,
            'uniform_RH_strength_bound_proved':False,'RH_proved':False,'RH_refuted':False}
        write(OUT/'report.json',report);emit('analytic_repair_complete',status=report['status'],elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json',{'type':type(exc).__name__,'message':str(exc),'completed_cases':len(results),
            'elapsed_seconds':time.monotonic()-started,'uniform_core_bound_proved':False,'RH_proved':False})
        raise


if __name__=='__main__':main()

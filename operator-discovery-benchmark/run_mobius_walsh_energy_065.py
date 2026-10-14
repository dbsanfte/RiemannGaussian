"""Freeze and synthesize joint energy bounds on the admitted064 parents."""
import os
for _native_thread_variable in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[_native_thread_variable]='1'

from fractions import Fraction as Q
from math import isqrt
import json
import multiprocessing as mp
import resource
import time

import mobius_walsh_energy_065 as SEARCH
import check_mobius_walsh_energy_065 as CHECK
import run_mobius_quadratic_contraction_064 as PRIOR
from run_fractional_prime_kernel_051 import write,emit,check_receipt

ROOT=PRIOR.ROOT
OUT=PRIOR.OUT/'walsh_energy_followup_001'
FILES=['mobius_walsh_energy_065.py','test_mobius_walsh_energy_065.py','mobius_walsh_energy_search_065_development.json',
       'check_mobius_walsh_energy_065.py','test_check_mobius_walsh_energy_065.py',
       'mobius_walsh_energy_checker_065_development.json','MOBIUS_WALSH_ENERGY_CHECK_SCOPE_065.txt',
       'MOBIUS_GROWING_CONDITIONING_REVIEW_065.txt','run_mobius_walsh_energy_065.py','mobius_walsh_energy_protocol_065.txt']
SPEC={'parents':'all36 saved064 certificates whose labels include prefix_1/2',
      'new_prime_conditioning':False,'weight_powers':list(SEARCH.WEIGHT_POWERS),
      'rational_orders_are_not_whitelisted':True,'weight_binary_significand_bits':4,
      'weight_formula':'upward binary rounding of each nonzero row coefficient L1 to the requested rational power; empty rows have zero weight',
      'rounding_reason':'bounded significands avoid unrelated large odd divisors in every energy weight',
      'cycle_search':'GF(2) dependencies, descending remaining coefficient capacity, then degree/key; consume minimum capacity and rebuild basis',
      'maximum_cycles_per_endpoint':64,'variation_bound_rounding_denominator':4096,
      'source_binding':'reuse064 source and contraction admissions of SAME literal parent; independently verify every new energy and cycle',
      'selection':'lowest complete endpointwise long-plus-short budget; inherited064 bound remains available as fallback',
      'new_LP_source_prefix_or_integral_evaluation':False,
      'workers':3,'native_threads_per_worker':1,'maximum_aggregate_bytes':16*1024**3,
      'module_seconds':7200,'work_cap_per_meter':300_000_000_000,'uniform_growth_claim':False}


def validate_parent():
    counts=PRIOR.validate_parent();directory=PRIOR.OUT/'source_snapshot'
    if sorted(p.name for p in directory.iterdir())!=sorted(PRIOR.FILES):raise ValueError('complete064 snapshot')
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(directory/name).read_bytes():raise ValueError('preserve064 '+name)
    report=json.loads((PRIOR.OUT/'report.json').read_text())
    if report['exact_contraction_certificates_verified']!=301 or report['independent_quadratic_source_admissions']!=36:
        raise ValueError('complete064 bound archive')
    if not report['quadratic_schema_independently_machine_admitted'] or report['uniform_core_bound_proved'] or report['RH_proved']:
        raise ValueError('064 source admission and open global growth binding')
    return counts+[len(PRIOR.FILES)]


def bind_parent(saved,meter):
    candidates=[c for c in saved['candidates'] if 'prefix_1/2' in c['labels']]
    if len(candidates)!=1:raise ValueError('one deduplicated sqrtB conditioning parent')
    chosen=candidates[0];parent=chosen['certificate'];proof=chosen['verification'];source=saved['independent_quadratic_source_verification']
    if not source['verified'] or not source['quadratic_source_factorization_proved'] or not source['linked_repair_identity_proved']:
        raise ValueError('saved independent quadratic source admission')
    for k in ('N','y','H','K'):
        if parent[k]!=saved[k] or proof[k]!=parent[k] or source[k]!=parent[k]:raise ValueError('same source-bound parent scale and horizons')
    B=max(parent['H'],parent['K']);C=isqrt(B)
    conditioned=[p for p in range(2,C+1) if all(p%d for d in range(2,isqrt(p)+1))]
    if parent['conditioned_primes']!=conditioned or proof['conditioned_primes']!=conditioned:
        raise ValueError('exact sqrtB actual-prime conditioning')
    if chosen['fully_conditioned'] or proof['all_radius_primes_conditioned']:
        raise ValueError('study requires free large-prime variables')
    if not chosen['all_small_primes_through_sqrtB_conditioned'] or not proof['verified'] or not proof['finite_variation_bound_proved'] or not proof['endpoint_convexity_proved']:
        raise ValueError('saved complete conditional variation admission')
    if proof['budget']!=parent['budget'] or proof['endpoint_l1']!=[e['l1'] for e in parent['endpoints']] or proof['endpoint_ratios']!=[e['ratio'] for e in parent['endpoints']]:
        raise ValueError('same parent endpoint prices and ratios')
    p,q=source['parameters']['p'],source['parameters']['q']
    if proof['endpoint_ratios']!=[str(Q(p,q)),'1']:raise ValueError('source ratio endpoints')
    if source['coefficient_l1']!=saved['actual_repair_endpoint_l1'] or not saved['saved_whole_proof_reused_with_exact_merge_binding']:
        raise ValueError('saved actual repair and whole prefix ancestry')
    actual=list(map(Q,saved['actual_repair_endpoint_l1']));long=list(map(Q,saved['long_endpoint_l1']))
    if str(max(a+b for a,b in zip(actual,long)))!=saved['actual_selected_whole_budget']:
        raise ValueError('same actual long-plus-short budget')
    if str(max(a+Q(e['l1']) for a,e in zip(long,parent['endpoints'])))!=chosen['whole_prefix_budget']:
        raise ValueError('same conditioned parent whole budget')
    meter.charge(128*B)
    return chosen,parent,long,actual


def evaluate_task(name):
    started=time.monotonic();saved=json.loads((PRIOR.OUT/name).read_text())
    meter=SEARCH.Meter(cap=SPEC['work_cap_per_meter'],seconds=SPEC['module_seconds'])
    cm=CHECK.Meter(cap=SPEC['work_cap_per_meter'],seconds=SPEC['module_seconds'])
    old,parent,long,actual=bind_parent(saved,meter)
    result=SEARCH.discover(parent,meter,powers=SPEC['weight_powers'],precision=SPEC['weight_binary_significand_bits'],max_cycles=SPEC['maximum_cycles_per_endpoint'])
    for candidate in result['candidates']:
        certificate=candidate['certificate'];verdict=CHECK.verify_energy(parent,certificate,cm)
        endpoint_bounds=[];uncycled=[]
        for e,endpoint in enumerate(verdict['endpoints']):
            budget=Q(endpoint['variation_bound']);endpoint_bounds.append(long[e]+budget)
            if budget<actual[e] or budget<Q(endpoint['all_free_plus_l1']):raise ValueError('new envelope cannot evade common-sign witnesses')
            old_diag=old['diagnostics']['endpoints'][e]
            if endpoint['all_free_minus_l1']!=str(actual[e]) or endpoint['all_free_plus_l1']!=old_diag['all_free_plus_one_l1']:
                raise ValueError('same actual and formal witness interpretation')
            raw=Q(candidate['uncycled_endpoint_variation_bounds'][e]);uncycled.append(long[e]+raw)
            if raw*raw<Q(endpoint['weight_mass'])*Q(endpoint['energy_l1']):raise ValueError('raw energy Cauchy price')
        candidate.update({'verification':verdict,'whole_prefix_endpoint_budgets':list(map(str,endpoint_bounds)),
            'whole_prefix_budget':str(max(endpoint_bounds)),'uncycled_whole_prefix_budget':str(max(uncycled)),
            'source_bound_by_same_admitted_064_parent':True,'uniform_N_growth_proved':False})
    selected=min(range(len(result['candidates'])),key=lambda i:(Q(result['candidates'][i]['whole_prefix_budget']),i))
    best=result['candidates'][selected];old_budget=Q(old['whole_prefix_budget']);new_budget=Q(best['whole_prefix_budget'])
    result.update({'source_contraction_file':name,'source_parent_certificate':parent,
        'reused_064_source_verification':saved['independent_quadratic_source_verification'],
        'reused_064_contraction_verification':old['verification'],
        'theta':saved['theta'],'rule':saved['rule'],'arithmetic_radius':saved['arithmetic_radius'],
        'remaining_prime_count':old['remaining_prime_count'],
        'selected_energy_index':selected,'selected_energy_weight_powers':best['weight_powers'],
        'best_energy_whole_budget':str(new_budget),'previous_conditioned_whole_budget':str(old_budget),
        'selected_whole_budget':str(min(new_budget,old_budget)),
        'selected_kind':'walsh_energy' if new_budget<old_budget else 'inherited_coefficient_l1',
        'actual_repair_endpoint_l1':list(map(str,actual)),'long_endpoint_l1':list(map(str,long)),
        'actual_selected_whole_budget':saved['actual_selected_whole_budget'],
        'producer_operations':meter.operations,'independent_checker_operations':cm.operations,
        'prospective_algorithm_bytes':meter.peak_bytes_estimate,
        'worker_peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'elapsed_seconds':time.monotonic()-started})
    return result


def feedback(params,parent,results):
    return {'schema':'mobius-walsh-energy-feedback-v1','source_parameters':params,
        'previous_goal_turn':'064 substantive: exact prime-conditioned envelopes and relaxation lower guards',
        'current_goal_turn':'065 substantive: automatically synthesized cross-row energies and frustrated parity-cycle inequalities',
        'parent_target':parent['parent_target'],'conditional_core_recovery':parent['conditional_core_recovery'],
        'new_bound_program':{'energy':'E(x)=sum_j q_j(x)^2/w_j, same remaining prime assignment in all rows',
            'weights':'positive rational binary approximations of row coefficient L1 to arbitrary rational powers, zero only on empty rows',
            'algebra':'character products reduce by symmetric difference; every cross and diagonal is retained; rows coalesce before absolute values',
            'cycles':'GF(2) dependency with negative product of preferred coefficient signs; coefficient capacities pay overlapping cycles',
            'bound':'sum_j |q_j(x)| <=sqrt[(sum_j w_j)*(energy_l1-2*sum_cycle_mass)]',
            'source_binding':'new independent energy proof composed with SAME saved064 source/contraction proof',
            'all_remaining_sign_assignments':True,'fixed_N_y_parameter_continuum':True},
        'observed_feedback':{'cases':len(results),'cases_with_stronger_complete_bound':sum(r['selected_kind']=='walsh_energy' for r in results),
            'cases_with_synthesized_frustrated_cycles':sum(any(any(c['cycle_counts']) for c in r['candidates']) for r in results),
            'finite_comparison_not_a_growth_estimate':True},
        'unpaid_leaf':{'formula':'(sum_j w_j)*(A_1+sum_(F!=empty)|A_F|-2*sum_cycle_mass)',
            'required_growth':'<=C_kappa^2*N^(1+2*kappa), every kappa>0, both endpoints, every N and required y',
            'program_family':'declared source fill/cutoff/conditioning and finite weight/cycle algorithms may depend on N,y as specified',
            'no_uniform_N_growth_proved':True},
        'source_only_audit':{'formal_inverse_defect':'F_H Delta D(chi)E(d)=sum_(n<=H/d)(chi*One)(n)E(dn)',
            'at_sqrt_conditioning_all_free_plus':'defect beyond E(d) is exactly 2*sum_(free primes P<=H/d)E(dP)',
            'actual_mu_defect':'zero, because ordinary mu*One=delta_1',
            'core_inverse_profile':'P(1/d)=1/d; G_chi=M_chi/d-R_chi with exact joined, truncated fractional remainder',
            'paid_source_linear_part':'||Delta D(chi)Pf||_1<=4H(1+log H)',
            'remaining_joint_term':'Delta D(chi)[P R_chi-M_chi/d]',
            'reviewed_general_finite_identities':True,'new_machine_admission_of_defect_schema':False,
            'growing_conditioning_obstruction_proved':False,
            'leading_term_guard':'an unsigned O(N) error cannot support an N/log(N)^2 lower witness'},
        'next_search_input':{'target':'uniform energy-product control or an arithmetic-constrained construction for the exact inverse defect/residual',
            'retain':['common prime signs','both source channels','cross-row energy coefficients','units','floor/truncation boundaries'],
            'do_not_repeat':'additional fixed-scale weight tuning cannot discharge the uniform leaf',
            'free_sign_domain_still_stronger_than_actual_mu':True},
        'uniform_quadratic_variation_bound_proved':False,'uniform_core_bound_proved':False,
        'uniform_RH_strength_bound_proved':False,'RH_proved':False,'RH_refuted':False}


def main():
    if OUT.exists():raise FileExistsError('preserve every065 attempt')
    started=time.monotonic();counts=validate_parent()
    parent=json.loads((PRIOR.OUT/'mechanism_feedback.json').read_text());params=parent['source_parameters']
    frozen={name:(ROOT/name).read_bytes() for name in FILES}
    receipts=[json.loads(data) for name,data in frozen.items() if name.endswith('_development.json')]
    development=sum(check_receipt(r) for r in receipts)
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name,data in frozen.items():(OUT/'source_snapshot'/name).write_bytes(data)
    results=[]
    try:
        write(OUT/'spec.json',{'spec':SPEC,'parameters':params,'prior_frozen_counts':counts,
            'new_frozen_files':len(FILES),'frozen_before_new_energy_scores_or_cycles':True,'hashes_used':False,
            'pre_freeze_source_read':'existing064 certificate pair counts only for resource planning; no new energy or weight evaluation',
            'prospective_largest_pair_count':87598})
        names=sorted(p.name for p in PRIOR.OUT.glob('contraction_*.json'))
        if len(names)!=36:raise ValueError('all36 admitted064 parents')
        emit('walsh_energy_started',cases=len(names),weight_orders=len(SPEC['weight_powers']),workers=SPEC['workers'])
        with mp.get_context('fork').Pool(SPEC['workers']) as pool:
            for result in pool.imap_unordered(evaluate_task,names,chunksize=1):
                name='energy_'+result['source_contraction_file'].removeprefix('contraction_')
                write(OUT/name,result);results.append(result)
                emit('walsh_energy_checked',N=result['N'],y=result['y'],H=result['H'],
                    selected=result['selected_kind'],weight_powers=result['selected_energy_weight_powers'],
                    completed=len(results),total=len(names))
        results.sort(key=lambda r:(r['N'],r['y'],Q(r['theta'])))
        rows=[]
        for result in results:
            for i,candidate in enumerate(result['candidates']):
                rows.append({**{k:result[k] for k in ('N','y','H','K','theta','rule','remaining_prime_count')},
                    'candidate_index':i,**{k:candidate[k] for k in ('weight_powers','cycle_counts','whole_prefix_budget','uncycled_whole_prefix_budget')},
                    'endpoint_energy_data':candidate['verification']['endpoints'],
                    'previous_conditioned_whole_budget':result['previous_conditioned_whole_budget'],
                    'actual_selected_whole_budget':result['actual_selected_whole_budget']})
        write(OUT/'summary.json',{'rows':rows,'finite_bound_search_only':True,'uniform_growth_proved':False})
        write(OUT/'mechanism_feedback.json',feedback(params,parent,results))
        validate_parent()
        if any((ROOT/name).read_bytes()!=data for name,data in frozen.items()):raise ValueError('preserve frozen065 sources')
        peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss;worker=max(r['worker_peak_rss_kib'] for r in results)
        peak_sum=1024*(peak+SPEC['workers']*worker)
        if peak_sum>SPEC['maximum_aggregate_bytes']:raise MemoryError('conservative sum of process peaks exceeds16GiB')
        report={'status':'AUTOMATIC_SHARED_SIGN_ENERGY_AND_CYCLE_BOUNDS_UNIFORM_RATE_OPEN',
            'fixed_N_y_H_cases':len(results),'exact_energy_certificates_independently_verified':len(rows),
            'cases_improving_complete_conditioned_bound':sum(r['selected_kind']=='walsh_energy' for r in results),
            'cases_with_synthesized_cycles':sum(any(any(c['cycle_counts']) for c in r['candidates']) for r in results),
            'total_synthesized_cycles':sum(sum(c['cycle_counts']) for r in results for c in r['candidates']),
            'candidates_with_strict_cycle_gain':sum(Q(c['whole_prefix_budget'])<Q(c['uncycled_whole_prefix_budget']) for r in results for c in r['candidates']),
            'parent_calibration_witnesses_preserved':True,
            'new_synthetic_tests':sum(r['unique_new_synthetic_tests'] for r in receipts),
            'test_invocations':sum(sum(t['tests'] for t in r['runs']) for r in receipts),
            'development_operations':development,'producer_operations':sum(r['producer_operations'] for r in results),
            'independent_checker_operations':sum(r['independent_checker_operations'] for r in results),
            'square_expansion_pairs_reused_across_policies':sum(r['expanded_square_pairs_reused_across_policies'] for r in results),
            'elapsed_seconds':time.monotonic()-started,'parent_peak_rss_kib':peak,'largest_worker_peak_rss_kib':worker,
            'conservative_sum_of_process_peaks_bytes':peak_sum,
            'largest_prospective_algorithm_bytes':max(r['prospective_algorithm_bytes'] for r in results),
            'largest_checker_prospective_bytes':max(c['verification']['prospective_peak_storage_bytes'] for r in results for c in r['candidates']),
            'workers':SPEC['workers'],'native_threads_per_worker':1,'prior_frozen_counts':counts,'new_frozen_source_count':len(FILES),
            'hashes_used':False,'old_scientific_studies_or_suites_replayed':False,
            'new_source_prefix_sums_LP_or_integrals_evaluated':False,'new_prime_conditioning':False,
            'same_064_parent_admissions_reused':True,'new_energy_certificates_checked_independently':True,
            'general_divisor_inverse_defect_reviewed':True,'general_growing_conditioning_obstruction_proved':False,
            'uniform_energy_product_bound_proved':False,'uniform_core_bound_proved':False,
            'all_y_bound_proved':False,'uniform_RH_strength_bound_proved':False,'RH_proved':False,'RH_refuted':False}
        write(OUT/'report.json',report);emit('walsh_energy_complete',status=report['status'],elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json',{'type':type(exc).__name__,'message':str(exc),'completed_cases':len(results),
            'elapsed_seconds':time.monotonic()-started,'uniform_core_bound_proved':False,'RH_proved':False})
        raise


if __name__=='__main__':main()

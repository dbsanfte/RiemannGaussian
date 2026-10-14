"""Frozen adaptive divisor-identity correction study on admitted069 inputs."""
import os
for _thread_variable in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[_thread_variable]='1'

from fractions import Fraction as Q
from pathlib import Path
import json
import multiprocessing as mp
import resource
import time
import mobius_divisor_correction_070 as SEARCH
import check_mobius_divisor_correction_070 as CHECK
import run_mobius_convolution_scale_069 as PRIOR
from run_fractional_prime_kernel_051 import write,emit,check_receipt

ROOT=PRIOR.ROOT
OUT=PRIOR.OUT/'divisor_correction_followup_001'
FILES=['mobius_divisor_correction_070.py','test_mobius_divisor_correction_070.py',
       'mobius_divisor_correction_search_070_development.json','check_mobius_divisor_correction_070.py',
       'test_check_mobius_divisor_correction_070.py','mobius_divisor_correction_checker_070_development.json',
       'MOBIUS_DIVISOR_CORRECTION_CHECK_SCOPE_070.txt','MOBIUS_DIVISOR_CORRECTION_REVIEW_070.txt',
       'run_mobius_divisor_correction_070.py','mobius_divisor_correction_protocol_070.txt']
SPEC=dict(source='all12 admitted069 groups, all14436 models and all36 H cuts',
    options=SEARCH.DEFAULT_OPTIONS, price_exponents=SEARCH.DEFAULT_SIGMAS,
    arithmetic_domain='T=U, the declared smaller prefix radius of each069 polynomial',
    supplied_rule='G_n=sum_(d|n)(M_d-M_(d-1))-delta_n1=0',
    adaptive_grammar='constant multipliers, current monomial quotients, adjacent indices and rank-spread constraint indices',
    promotion='dual-defect ranked candidate columns persist through up to3 adaptive LP rounds',
    objective='unconditional coefficient L1 with weights product(indices), using abs(M(s))<=s',
    proposal='boxed float LP, exact rational replay and robust box dual with full stationarity penalty',
    selection='unconditional upper, nonzero correction coefficients, stable model order',
    sign_values_or_target_values_given_to_learner=False,
    source_cases_are_reused_development_evidence=True, fresh_holdout_claim=False,
    workers=3,native_threads_per_worker=1,maximum_aggregate_bytes=16*1024**3,
    module_seconds=7200,work_cap_per_case_meter=300_000_000_000,
    uniform_head_bound_claim=False,hashes_used=False)


def validate_parent():
    counts=PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve069 '+name)
    report=json.loads((PRIOR.OUT/'report.json').read_text())
    if (report['independent_convolution_certificates']!=12 or report['distinct_models']!=14436
            or report['source_cases']!=36 or report['RH_proved'] or report['uniform_head_bound_proved']):
        raise ValueError('all completed069 polynomials and open signed cost')
    return counts+[len(PRIOR.FILES)]


def upper(cert):
    i=cert['selected_round']
    return Q(cert['baseline_unconditional_bound']) if i==-1 else Q(cert['rounds'][i]['primal_upper'])


def half_price(cert):
    return sum(map(Q,cert['selected_conditional_prices'][0]['coefficients']))


def multiplier_count(cert):
    return 0 if cert['selected_round']==-1 else sum(v!=0 for v in cert['rounds'][cert['selected_round']]['lambda_numerators'])


def bind_parent(saved):
    cert=saved['certificate']; verdict=saved['verification']
    if (not saved['original_source_binding_proved'] or not verdict['verified']
            or saved['RH_proved'] or saved['uniform_head_bound_proved']
            or cert['uniform_head_bound_proved'] or cert['conditional_prefix_bounds_paid']):
        raise ValueError('same admitted source; uniform arithmetic premise open')
    for key in ('N','y','max_j'):
        if saved[key]!=cert[key] or verdict[key]!=cert[key]: raise ValueError('same source geometry')
    if cert['parameters']!=verdict['parameters']: raise ValueError('same registered source')
    return cert,verdict


def summarize(saved,endpoints,meter):
    cert=saved['certificate']; result=[]
    for oldcase in saved['source_cases']:
        H=oldcase['H']; stop=(H+1)//2-1
        if (any(oldcase[k]!=cert[k] for k in ('N','y'))
                or H!=PRIOR.SEARCH.power(cert['N'],oldcase['theta'],meter)):
            raise ValueError('same source case and exact H power')
        eps=[]
        for old,endpoint,oldendpoint in zip(oldcase['endpoints'],endpoints,cert['endpoints']):
            if old['ratio']!=endpoint['ratio'] or endpoint['ratio']!=oldendpoint['ratio']:
                raise ValueError('same ratio endpoint')
            rows=endpoint['rows'][:stop]
            chosen=[r['models'][r['selected_model']]['certificate'] for r in rows]
            actual=Q(old['actual_head_variation'])
            total=sum((upper(c) for c in chosen),Q(0))
            if total<actual: raise ArithmeticError('new unconditional bound on admitted raw head')
            plans=[]
            for i,exponents in enumerate(cert['requests']):
                models=[r['models'][oldrow['plans'][i]['model_index']]['certificate']
                        for r,oldrow in zip(rows,oldendpoint['rows'][:stop])]
                plans.append(dict(exponents=exponents,
                    unconditional_head_upper=str(sum((upper(c) for c in models),Q(0))),
                    conditional_C1_half_head_price=str(sum((half_price(c) for c in models),Q(0))),
                    maximum_arithmetic_argument=max((c['constraint_radius'] for c in models),default=1),
                    nonzero_corrections=sum(multiplier_count(c) for c in models),
                    constant_only_rows=sum(c['constant_only_selected'] for c in models),
                    full_divisor_system_rows=sum(c['full_divisor_system_used'] for c in models)))
            partial=[]
            for row in rows:
                available=[m['certificate'] for m in row['models']
                           if not m['certificate']['constant_only_selected'] and not m['certificate']['full_divisor_system_used']]
                partial.append(min((upper(c) for c in available),default=None))
            eps.append(dict(ratio=endpoint['ratio'],head_stop=stop,actual_head_variation=str(actual),
                prior068_certified_head_upper=old['prior068_certified_head_upper'],
                prior069_selected_conditional_half_price=old['selected_conditional_C1_head_prices'][0],
                best_before_correction_unconditional_upper=str(sum((min(Q(m['certificate']['baseline_unconditional_bound']) for m in r['models']) for r in rows),Q(0))),
                selected_unconditional_head_upper=str(total),
                selected_conditional_C1_half_head_price=str(sum((half_price(c) for c in chosen),Q(0))),
                selected_maximum_arithmetic_argument=max((c['constraint_radius'] for c in chosen),default=1),
                selected_nonzero_corrections=sum(multiplier_count(c) for c in chosen),
                selected_constant_only_rows=sum(c['constant_only_selected'] for c in chosen),
                selected_full_divisor_system_rows=sum(c['full_divisor_system_used'] for c in chosen),
                every_row_has_nonconstant_incomplete_model=all(v is not None for v in partial),
                incomplete_nonconstant_head_upper=str(sum(partial,Q(0))) if all(v is not None for v in partial) else None,
                all_plans=plans,uniform_head_bound_proved=False))
        result.append(dict(N=cert['N'],y=cert['y'],H=H,theta=oldcase['theta'],endpoints=eps))
    return result


def evaluate_task(name):
    started=time.monotonic(); saved=json.loads((PRIOR.OUT/name).read_text())
    original,checked=bind_parent(saved)
    meter=SEARCH.Meter(cap=SPEC['work_cap_per_case_meter'],seconds=SPEC['module_seconds'])
    cm=CHECK.Meter(limit=SPEC['work_cap_per_case_meter'],seconds=SPEC['module_seconds'])
    algebra=SEARCH.Algebra(meter); cache={}; endpoints=[]
    unique_calls=0
    for ep,oldverdict in zip(original['endpoints'],checked['endpoints']):
        rows=[]
        if ep['ratio']!=oldverdict['ratio']: raise ValueError('same endpoint order')
        for row,priorrow in zip(ep['rows'],oldverdict['rows']):
            models=[]
            for i,parentmodel in enumerate(row['models']):
                source=SEARCH.input_from_model(parentmodel,ep['denominator'])
                key=(source['degree'],source['U'],source['denominator'],
                     tuple((tuple(t['indices']),t['numerator']) for t in source['polynomial']))
                if key not in cache:
                    cert=SEARCH.construct(source,options=SPEC['options'],price_exponents=SPEC['price_exponents'],meter=meter,algebra=algebra)
                    verdict=CHECK.verify_correction(cert,cm); unique_calls+=1
                    cache[key]=(cert,verdict)
                cert,verdict=cache[key]
                if cert['input']!=source or cert['constraint_radius']!=parentmodel['mu_query_radius']:
                    raise ValueError('same full admitted polynomial and declared arithmetic domain')
                if (not verdict['verified'] or verdict['source_actual_value']!=priorrow['actual_coefficient']
                        or verdict['selected_actual_value']!=priorrow['actual_coefficient']):
                    raise ValueError('every corrected model binds to original raw row')
                if row['R']>1 and cert['constraint_radius']>=row['R']:
                    raise ValueError('strict smaller arithmetic domain for original nonunit row')
                models.append(dict(parent_model_index=i,certificate=cert,verification=verdict))
            best=min(range(len(models)),key=lambda i:(upper(models[i]['certificate']),multiplier_count(models[i]['certificate']),i))
            rows.append(dict(j=row['j'],R=row['R'],models=models,selected_model=best))
        endpoints.append(dict(ratio=ep['ratio'],rows=rows))
    cases=summarize(saved,endpoints,meter)
    return dict(source_convolution_file=name,N=original['N'],y=original['y'],max_j=original['max_j'],
        endpoints=endpoints,source_cases=cases,unique_search_and_checker_calls=unique_calls,
        original_source_binding_proved=True,producer_operations=meter.operations,checker_operations=cm.operations,
        prospective_algorithm_bytes=meter.peak_bytes_estimate,worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        elapsed_seconds=time.monotonic()-started,uniform_head_bound_proved=False,RH_proved=False)


def feedback(results):
    return dict(schema='mobius-divisor-correction-feedback-v1',
        previous_goal_turn='069 progress: exact signed scale reduction, verified poor finite prices and proved scalar-domain obstruction',
        current_goal_turn='070 automatic adaptive ideal-multiplier synthesis and exact unconditional finite prices',
        detector_generated=['constraint and monomial choices from dual defects','signed polynomial multipliers',
            'complete corrected polynomial','unconditional finite upper and robust boxed optimum lower'],
        supplied_mathematics=['local complete divisor identities','polynomial ideal multiplication','weighted coefficient L1 bound','box dual penalty'],
        admission='each polynomial is exactly matched to an admitted069 source; independent actual evaluation agrees with its saved raw row',
        arithmetic_domain='current science T=U; API larger T is an explicit new dependency requiring a rank/cost audit',
        target='uniform Oepsilon(N^(1/2+epsilon)) of the signed raw head for every N,y and both endpoint ratios',
        full_ideal_warning='complete divisor ideal fixes the unique actual prefix point; optimal finite correction can just encode the target',
        main_unpaid_leaf='uniform cost law for the selected complete corrected polynomial or a reusable arithmetic energy/scale invariant',
        candidate_status='finite bound certificates, not proved uniform growth mechanisms',
        analytical_review='MOBIUS_DIVISOR_CORRECTION_REVIEW_070.txt; supplied proved lemmas and their conditional dependencies stay distinct from detector discoveries',
        next_obligation='extract a reusable source/scale multiplier rule and prove its full cost; treat target-valued constants and conditional prefix premises as unpaid leaves',
        observed_groups=len(results),conditional_prefix_bounds_paid=False,uniform_head_bound_proved=False,
        uniform_far_correlation_bound_proved=False,uniform_core_bound_proved=False,RH_proved=False,research_goal_complete=False)


def main():
    if OUT.exists(): raise FileExistsError('preserve every070 attempt')
    start=time.monotonic(); counts=validate_parent(); frozen={n:(ROOT/n).read_bytes() for n in FILES}
    receipts=[json.loads(v) for n,v in frozen.items() if n.endswith('_development.json')]
    development=sum(check_receipt(r) for r in receipts)
    if any(r['final_status']!='PASS' for r in receipts): raise ValueError('new synthetic verification gates passed')
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for name,data in frozen.items():(OUT/'source_snapshot'/name).write_bytes(data)
    results=[]; sampled_peak=0
    try:
        write(OUT/'spec.json',dict(spec=SPEC,prior_frozen_counts=counts,new_frozen_files=len(FILES),frozen_before_scientific_correction_search=True))
        names=sorted(p.name for p in PRIOR.OUT.glob('convolution_*.json'))
        if len(names)!=12:raise ValueError('all12 source groups')
        emit('divisor_correction_started',groups=len(names),workers=SPEC['workers'])
        with mp.get_context('spawn').Pool(SPEC['workers']) as pool:
            iterator=pool.imap_unordered(evaluate_task,names,chunksize=1)
            while len(results)<len(names):
                if time.monotonic()-start>SPEC['module_seconds']:raise TimeoutError('whole070 module deadline')
                rss=PRIOR.PRIOR.aggregate_rss([os.getpid()]+[p.pid for p in pool._pool]);sampled_peak=max(sampled_peak,rss)
                if rss>SPEC['maximum_aggregate_bytes']:raise MemoryError('aggregate070 worker RSS')
                try:result=iterator.next(timeout=1)
                except mp.TimeoutError:continue
                write(OUT/result['source_convolution_file'].replace('convolution_','correction_',1),result);results.append(result)
                emit('divisor_correction_checked',N=result['N'],y=result['y'],completed=len(results),total=len(names),unique_models=result['unique_search_and_checker_calls'])
        results.sort(key=lambda r:(r['N'],r['y']));cases=[c for r in results for c in r['source_cases']]
        write(OUT/'summary.json',dict(cases=cases,uniform_head_bound_proved=False))
        write(OUT/'mechanism_feedback.json',feedback(results))
        for name,data in frozen.items():
            if (ROOT/name).read_bytes()!=data:raise ValueError('preserve070 '+name)
        if validate_parent()!=counts:raise ValueError('preserve inherited source chain')
        rows=[row for r in results for e in r['endpoints'] for row in e['rows']]
        models=[m['certificate'] for row in rows for m in row['models']]
        rounds=[rd for c in models for rd in c['rounds']]
        selected=[row['models'][row['selected_model']]['certificate'] for row in rows]
        parent_peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        worker_peak=max(r['worker_peak_rss_kib'] for r in results);peak_sum=1024*(parent_peak+SPEC['workers']*worker_peak)
        if peak_sum>SPEC['maximum_aggregate_bytes']:raise MemoryError('conservative process peaks070')
        report=dict(status='EXACT_ARITHMETIC_CORRECTIONS_AND_UNCONDITIONAL_FINITE_BOUNDS_VERIFIED_UNIFORM_COST_OPEN',
            source_cases=len(cases),independent_correction_groups=len(results),distinct_endpoint_rows=len(rows),
            source_models=len(models),unique_search_and_checker_calls=sum(r['unique_search_and_checker_calls'] for r in results),
            model_round_records=len(rounds),strict_model_bound_improvements=sum(upper(c)<Q(c['baseline_unconditional_bound']) for c in models),
            selected_corrected_models=sum(c['selected_round']!=-1 for c in selected),
            selected_constant_only_models=sum(c['constant_only_selected'] for c in selected),
            selected_full_divisor_system_models=sum(c['full_divisor_system_used'] for c in selected),
            all_models_with_nonlinear_corrections=sum(c['selected_round']!=-1 and any(col['multiplier_indices'] and v for col,v in zip(c['rounds'][c['selected_round']]['columns'],c['rounds'][c['selected_round']]['lambda_numerators'])) for c in models),
            excluded_scalar_fake_models=sum(bool(c['scalar_fake']['violated_used_constraints']) for c in models),
            failed_solver_round_records=sum(r['solver']['status']=='failed_zero_fallback' for r in rounds),
            new_synthetic_tests=sum(r['unique_new_synthetic_tests'] for r in receipts),
            test_invocations=sum(sum(t['tests'] for t in r['runs']) for r in receipts),development_operations=development,
            producer_operations=sum(r['producer_operations'] for r in results),independent_checker_operations=sum(r['checker_operations'] for r in results),
            elapsed_seconds=time.monotonic()-start,parent_peak_rss_kib=parent_peak,largest_worker_peak_rss_kib=worker_peak,
            sampled_aggregate_rss_peak_bytes=sampled_peak,conservative_sum_of_process_peaks_bytes=peak_sum,
            largest_prospective_algorithm_bytes=max(r['prospective_algorithm_bytes'] for r in results),workers=SPEC['workers'],native_threads_per_worker=1,
            prior_frozen_counts=counts,new_frozen_source_count=len(FILES),learner_mobius_signs_accessed=False,
            exact_ideal_identity_and_box_dual_verified=True,finite_bounds_unconditional=True,
            old_scientific_studies_or_suites_replayed=False,hashes_used=False,fresh_holdout_claim=False,
            conditional_prefix_bounds_paid=False,uniform_head_bound_proved=False,uniform_far_correlation_bound_proved=False,
            uniform_core_bound_proved=False,RH_proved=False,RH_refuted=False)
        write(OUT/'report.json',report);emit('divisor_correction_complete',status=report['status'],elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json',dict(type=type(exc).__name__,message=str(exc),completed_groups=len(results),RH_proved=False))
        raise


if __name__=='__main__':main()

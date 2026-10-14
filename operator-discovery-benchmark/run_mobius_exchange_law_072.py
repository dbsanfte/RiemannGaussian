"""Frozen all-scale exchange-law search on a necessary original source slice."""
import os
for _var in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[_var]='1'
from fractions import Fraction as Q
import json
import multiprocessing as mp
import resource
import time

import mobius_exchange_law_072 as SEARCH
import check_mobius_exchange_law_072 as CHECK
import run_mobius_moment_scale_071 as PRIOR
from run_fractional_prime_kernel_051 import write,emit,check_receipt

ROOT=PRIOR.ROOT
OUT=PRIOR.OUT/'exchange_law_followup_001'
FILES=['mobius_exchange_law_072.py','test_mobius_exchange_law_072.py',
       'test_mobius_exchange_law_integration_072.py','mobius_exchange_law_search_072_development.json',
       'check_mobius_exchange_law_072.py','test_check_mobius_exchange_law_072.py',
       'mobius_exchange_law_checker_072_development.json','MOBIUS_EXCHANGE_LAW_CHECK_SCOPE_072.txt',
       'MOBIUS_EXCHANGE_LAW_SCHEMA_072.txt','MOBIUS_PRIME_ORBIT_REVIEW_072.txt',
       'run_mobius_exchange_law_072.py','mobius_exchange_law_protocol_072.txt']
CAPS=[2,3,5,7,11,13,17,19,23]
SCALES=[1,2,3,5,11,17,31,64,101,211,257,512,769,1024]
SPEC=dict(profile=SEARCH.SOURCE_PROFILE,multiplier_caps=CAPS,finite_check_scales=SCALES,
    source='same original joined source at N=15k,y=16k,p3,q5,r1,j1;necessary slice,not fullhead',
    objective='minimize exact rational leading coefficient of a proved all-scale price',
    arithmetic_input='small multiplier factorizations through cap and symbolic divisibility states only',
    learner_actual_source_mobius_values=False,actual_values_used_for_selection=False,
    proof='complete geometric/divisibility capacities plus supplied squarefree-coprime count theorem',
    automatic_rejection='positive certified lower leading coefficient rules out a sublinear price in this packing language',
    shared_prime_composite_signs=True,workers=3,native_threads_per_worker=1,
    maximum_aggregate_bytes=16*1024**3,module_seconds=7200,work_cap_per_meter=300_000_000_000,
    old_scientific_studies_or_suites_replayed=False,hashes_used=False,fresh_predictive_holdout_claim=False,
    uniform_head_bound_proved=False,RH_proved=False)


def validate_parent():
    counts=PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'source_snapshot'/name).read_bytes():raise ValueError('preserve071 '+name)
    report=json.loads((PRIOR.OUT/'report.json').read_text())
    if report['exact_optimal_programs']!=50 or report['distinct_rows']!=1032 or report['RH_proved']:
        raise ValueError('completed071 conditional programs and open joint remainder')
    return counts+[len(PRIOR.FILES)]


def original_slice(k,meter):
    """Independent source admission, bypassing the assumed step-profile formula."""
    N,y,D=15*k,16*k,20*k
    # Divisor inversion, independent of the checker's prime sieve.
    mu=[0]*(D+1);mu[1]=1
    # Exact divisor inverse gives a separate ordinary-mu construction.
    for n in range(1,D+1):
        value=mu[n]
        for m in range(2*n,D+1,n):mu[m]-=value
        meter.charge(4*(D//n+1))
    def g(d):
        if d<=y or d>D:return 0
        wp=4*N//(3*d)-3*(2*N//(3*d))+2*(N//(3*d))
        wq=4*N//(5*d)-3*(2*N//(5*d))+2*(N//(5*d))
        return -wp+wq
    direct=sum(sign*a for b,sign in ((3,1),(5,-1)) for v,a in ((4,1),(2,-3),(1,2)) if v*N//b==1)
    original=direct
    for n in range(1,D+1):
        coefficient=g(n)-g(2*n)
        expected=int(8*k<n<=10*k)-int(16*k<n<=20*k)
        if coefficient!=expected:raise ValueError('same full joined raw source profile')
        original+=mu[n]*coefficient;meter.charge(32)
    if direct!=0:raise ValueError('source-family direct atom')
    return dict(k=k,N=N,y=y,p=3,q=5,ratio='1',j=1,actual_signed_target=str(original),
                complete_pointwise_source_binding_proved=True)


def law_task(cap):
    start=time.monotonic();pm=SEARCH.Meter(cap=SPEC['work_cap_per_meter']);cm=CHECK.Meter(limit=SPEC['work_cap_per_meter'])
    cert=SEARCH.construct(SPEC['profile'],cap,pm);v=CHECK.verify_law(cert,cm)
    result=dict(cap=cap,certificate=cert,verification=v,producer_operations=pm.operations,
        checker_operations=cm.ops,prospective_algorithm_bytes=pm.peak_bytes_estimate,
        elapsed_seconds=time.monotonic()-start,worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    write(OUT/('law_'+str(cap)+'.json'),result)
    return dict(cap=cap,leading_upper=cert['leading_upper'],leading_lower=cert['leading_lower'],
        sqrt_error_upper=cert['sqrt_error_upper'],selected_families=len(cert['selected_family_indices']),
        family_count=len(cert['candidates']),capacity_row_count=len(cert['capacity_rows']),
        robust_dual_gap=str(Q(cert['objective_upper'])-Q(cert['objective_gain'])),
        sublinear_profile_bound_proved=cert['sublinear_profile_bound_proved'],
        sublinear_price_excluded_in_language=Q(cert['leading_lower'])>0,
        failed_solver=cert['solver']['status']=='failed_zero_fallback',
        producer_operations=pm.operations,checker_operations=cm.ops,
        prospective_algorithm_bytes=pm.peak_bytes_estimate,worker_peak_rss_kib=result['worker_peak_rss_kib'],
        elapsed_seconds=result['elapsed_seconds'])


def finite_task(cap):
    start=time.monotonic();cm=CHECK.Meter(limit=SPEC['work_cap_per_meter'])
    cert=json.loads((OUT/('law_'+str(cap)+'.json')).read_text())['certificate']
    values=[CHECK.evaluate_law(cert,k,cm) for k in SCALES]
    result=dict(cap=cap,values=values,checker_operations=cm.ops,
        elapsed_seconds=time.monotonic()-start,worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    write(OUT/('finite_'+str(cap)+'.json'),result)
    return result


def collect(pool,function,args,start,event):
    results=[];peak=0;iterator=pool.imap_unordered(function,args,chunksize=1)
    while len(results)<len(args):
        if time.monotonic()-start>SPEC['module_seconds']:raise TimeoutError('whole072 module deadline')
        rss=PRIOR.PRIOR.PRIOR.PRIOR.aggregate_rss([os.getpid()]+[p.pid for p in pool._pool]);peak=max(peak,rss)
        if rss>SPEC['maximum_aggregate_bytes']:raise MemoryError('aggregate072 memory')
        try:item=iterator.next(timeout=1)
        except mp.TimeoutError:continue
        results.append(item);emit(event,cap=item['cap'],completed=len(results),total=len(args))
    return sorted(results,key=lambda x:x['cap']),peak


def main():
    if OUT.exists():raise FileExistsError('preserve every072 attempt')
    start=time.monotonic();counts=validate_parent();frozen={n:(ROOT/n).read_bytes() for n in FILES}
    receipts=[json.loads(b) for n,b in frozen.items() if n.endswith('_development.json')]
    development=sum(check_receipt(r) for r in receipts)
    if any(r['final_status']!='PASS' for r in receipts):raise ValueError('new synthetic gates passed')
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for n,b in frozen.items():(OUT/'source_snapshot'/n).write_bytes(b)
    try:
        write(OUT/'spec.json',dict(spec=SPEC,prior_frozen_counts=counts,new_frozen_files=len(FILES),
            frozen_before_symbolic_scores_and_finite_evaluation=True))
        with mp.get_context('spawn').Pool(SPEC['workers']) as pool:
            laws,peak1=collect(pool,law_task,CAPS,start,'uniform_exchange_law_checked')
            # All symbolic programs are fixed before any finite arithmetic query.
            write(OUT/'symbolic_summary.json',dict(laws=laws,all_laws_fixed_before_finite_mu=True))
            finite,peak2=collect(pool,finite_task,CAPS,start,'uniform_exchange_finite_checked')
        bm=SEARCH.Meter(cap=SPEC['work_cap_per_meter']);binding=[original_slice(k,bm) for k in SCALES]
        for group in finite:
            for value,original in zip(group['values'],binding):
                if value['k']!=original['k'] or value['actual_signed_target']!=original['actual_signed_target']:
                    raise ValueError('independent original-source admission')
        write(OUT/'original_source_binding.json',dict(values=binding,operations=bm.operations,
            universal_family_derivation='N15k,y16k: g=-1_(16k,20k],h=g(n)-g(2n),direct0;review072'))
        pareto=[]
        for a in laws:
            qa=(Q(a['leading_upper']),Q(a['sqrt_error_upper']),a['cap'])
            if not any(all(x<=y for x,y in zip((Q(b['leading_upper']),Q(b['sqrt_error_upper']),b['cap']),qa))
                       and any(x<y for x,y in zip((Q(b['leading_upper']),Q(b['sqrt_error_upper']),b['cap']),qa))
                       for b in laws):pareto.append(a['cap'])
        feedback=dict(schema='uniform-exchange-law-feedback-v1',
            prior_goal_turn='071 progress: exact conditional exponent programs; joined remainder open',
            current_goal_turn='072 uniform signed exchange laws and proof-price obstruction synthesis',
            detector_generated=['all admissible multiplier/cell families','fractional global capacity allocations',
                'all-scale leading/error price','robust dual limit','automatic sublinear-price rejection'],
            supplied_rules=['multiplicativity on coprime squarefree factors','fractional pairing triangle inequality',
                'squarefree-coprime count with explicit square-root error'],
            source_scope='actual original row family for every k>=1; necessary slice, not all N,y,rows',
            pareto_uniform_envelope_caps=pareto,
            rejected_as_sublinear_price_caps=[r['cap'] for r in laws if r['sublinear_price_excluded_in_language']],
            sublinear_profile_candidate_caps=[r['cap'] for r in laws if r['sublinear_profile_bound_proved']],
            theorem='abs(Z(k)) <= (6/pi^2)*leading_upper*k+sqrt_error_upper*sqrt(k), every integer k>=1',
            exact_J_link='J1=Z(k)-2k H_mu(u)H_mu(v); full071 conditional moment cost retained',
            next_priority='signed interaction between distinct rough components, not more unsigned exchange transport within a fixed dictionary',
            extra_growing_scope_cost='leading and square-root error coefficients both depend on dictionary; a scale-dependent cap needs both priced',
            actual_prime_leaf='top-band primes above every dictionary multiplier are isolated; their signs may only be aggregated via an explicit additional rule',
            main_open_leaf='complete joint signed remainder bound or coupled energy with all cross-component terms',
            uniform_head_bound_proved=False,uniform_core_bound_proved=False,RH_proved=False,research_goal_complete=False)
        write(OUT/'mechanism_feedback.json',feedback)
        write(OUT/'next_search_input.json',dict(schema='signed-rough-component-obligation-v1',
            original_obstruction='../joint_obstruction.json',retained_family='N15k,y16k,p3,q5,r1,j1',
            profile=SPEC['profile'],uniform_bound_laws=['law_'+str(c)+'.json' for c in CAPS],
            exact_component_form='Z(k)=sum_C mu(anchor_C) V_C(k), V_C=sum_(n in C)relative_sign(n)*w(n/k)',
            target='abs(sum_C mu(anchor_C)V_C(k))=Oepsilon(k^(1/2+epsilon));preserve broader whole-head target',
            proved_limit='positive robust-dual leading lower for flagged caps; fixed-scope exchange transport also has rough survivor obstruction',
            unresolved=['signed cancellation between components','uniform growing-dictionary cost if used','full original head/core/RH transfer'],
            forbidden_claim='sum_C abs(V_C) or exact finite target reconstruction is a paid square-root bound',
            uniform_head_bound_proved=False,RH_proved=False))
        for n,b in frozen.items():
            if (ROOT/n).read_bytes()!=b:raise ValueError('preserve072 '+n)
        if validate_parent()!=counts:raise ValueError('preserve inherited source chain')
        parent_peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        worker_peak=max(r['worker_peak_rss_kib'] for r in laws+finite)
        peak_sum=1024*(parent_peak+SPEC['workers']*worker_peak)
        if peak_sum>SPEC['maximum_aggregate_bytes']:raise MemoryError('conservative072 process peak sum')
        report=dict(status='UNIFORM_SIGNED_EXCHANGE_LAWS_VERIFIED_COMPLETE_RH_CONTROL_OPEN',
            uniform_profile_laws=len(laws),finite_law_checks=sum(len(r['values']) for r in finite),
            new_original_source_scales=len(binding),source_family_valid_every_integer_scale=True,
            total_families=sum(r['family_count'] for r in laws),total_capacity_rows=sum(r['capacity_row_count'] for r in laws),
            total_selected_families=sum(r['selected_families'] for r in laws),
            sublinear_profile_candidates=sum(r['sublinear_profile_bound_proved'] for r in laws),
            exact_sublinear_price_rejections=sum(r['sublinear_price_excluded_in_language'] for r in laws),
            failed_solver_calls=sum(r['failed_solver'] for r in laws),pareto_caps=pareto,
            producer_operations=sum(r['producer_operations'] for r in laws),
            symbolic_checker_operations=sum(r['checker_operations'] for r in laws),
            finite_checker_operations=sum(r['checker_operations'] for r in finite),source_binding_operations=bm.operations,
            development_operations=development,new_synthetic_tests=sum(r['unique_new_synthetic_tests'] for r in receipts),
            test_invocations=sum(sum(v['tests'] for v in r['runs']) for r in receipts),
            elapsed_seconds=time.monotonic()-start,parent_peak_rss_kib=parent_peak,largest_worker_peak_rss_kib=worker_peak,
            sampled_aggregate_rss_peak_bytes=max(peak1,peak2),conservative_sum_of_process_peaks_bytes=peak_sum,
            largest_prospective_algorithm_bytes=max(r['prospective_algorithm_bytes'] for r in laws),
            workers=SPEC['workers'],native_threads_per_worker=1,prior_frozen_counts=counts,new_frozen_source_count=len(FILES),
            learner_source_scale_mobius_accessed=False,all_symbolic_laws_fixed_before_arithmetic_evaluation=True,
            all_original_source_bindings_proved=True,old_scientific_studies_or_suites_replayed=False,hashes_used=False,
            fresh_predictive_holdout_claim=False,uniform_head_bound_proved=False,uniform_core_bound_proved=False,
            RH_proved=False,RH_refuted=False)
        write(OUT/'report.json',report);emit('uniform_exchange_law_complete',status=report['status'],elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json',dict(type=type(exc).__name__,message=str(exc),RH_proved=False));raise


if __name__=='__main__':main()

"""Frozen symbolic proof search and same-source joined residual compilation071."""
import os
for _name in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[_name]='1'

from fractions import Fraction as Q
from pathlib import Path
import json
import multiprocessing as mp
import resource
import time
import mobius_moment_scale_071 as SEARCH
import check_mobius_moment_scale_071 as CHECK
import run_mobius_divisor_correction_070 as PRIOR
from run_fractional_prime_kernel_051 import write,emit,check_receipt

ROOT=PRIOR.ROOT
OUT=PRIOR.OUT/'moment_scale_followup_001'
FILES=['mobius_moment_scale_071.py','test_mobius_moment_scale_071.py',
       'test_mobius_moment_scale_integration_071.py','mobius_moment_scale_search_071_development.json',
       'check_mobius_moment_scale_071.py','test_check_mobius_moment_scale_071.py',
       'mobius_moment_scale_checker_071_development.json','MOBIUS_MOMENT_SCALE_CHECK_SCOPE_071.txt',
       'MOBIUS_MOMENT_SCALE_SCHEMA_071.txt','MOBIUS_MOMENT_SCALE_REVIEW_071.txt',
       'run_mobius_moment_scale_071.py','mobius_moment_scale_protocol_071.txt']
SIGMAS=['1/257','2/7','1/2','5/9','2/3','6/7']
RHOS=['3/7','1/2','2/3','3/4','4/5','7/8','256/257']
REQUESTS=[dict(sigma=s,rho=r,fixed_theta=None) for s in SIGMAS for r in RHOS]+[
    dict(sigma=s,rho=r,fixed_theta=t) for s in ('1/2','5/9') for r in ('3/4','256/257')
    for t in ('1/257','1/17','1/9','2/7','3/7')]
SPEC=dict(requests=REQUESTS,source='all12 admitted069 groups and all36 head cuts; same070 source',
    grammar='generic rational affine cost/rank constraints with exact optimum and Farkas certificates',
    objectives=['minimum conditional separable exponent','minimum auxiliary exposure at that exponent','minimum disjoint-short exponent'],
    supplied_rules=['finite reciprocal moment lemma070','complete degree2 support identity069',
        'quotient-counted source moment071','disjoint short-interval pricing071'],
    actual_mu_given_to_learner=False, measured_scores_used_for_proof_search=False,
    fractional_exponents='arbitrary canonical rational API,4096 input bits,100000 intermediate power bits',
    selected_diagnostics='sigma1/2 free rho3/4 plus fixed1/9 and1/257 rho256/257; chosen before evaluation',
    workers=3,native_threads_per_worker=1,maximum_aggregate_bytes=16*1024**3,
    module_seconds=7200,work_cap_per_case_meter=300_000_000_000,
    fresh_holdout_claim=False,hashes_used=False,uniform_head_bound_proved=False)


def validate_parent():
    counts=PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve070 '+name)
    report=json.loads((PRIOR.OUT/'report.json').read_text())
    if (report['distinct_endpoint_rows']!=1032 or report['source_models']!=14436
            or report['selected_constant_only_models']!=1032 or report['RH_proved']):
        raise ValueError('completed070 finite constant encoding, uniform bound open')
    return counts+[len(PRIOR.FILES)]


def diagnostics(programs):
    chosen=[]
    for i,p in enumerate(programs):
        if (p['sigma']=='1/2' and ((p['rho']=='3/4' and p['fixed_theta'] is None)
                or (p['rho']=='256/257' and p['fixed_theta'] in ('1/9','1/257')))):
            if p['derivation'] is None: raise ValueError('predeclared diagnostic program not certified')
            chosen.append(i)
    if len(chosen)!=3: raise ValueError('three predeclared diagnostics')
    return chosen


def summarize(saved,cert,verdict):
    cases=[]; chosen=diagnostics(cert['programs'])
    for oldcase in saved['source_cases']:
        H=oldcase['H']; stop=(H+1)//2-1; endpoints=[]
        for old,ep,check in zip(oldcase['endpoints'],cert['endpoints'],verdict['endpoints']):
            if old['ratio']!=ep['ratio'] or ep['ratio']!=check['ratio']: raise ValueError('same ordered source endpoint')
            rows=ep['rows'][:stop]; evaluated=check['rows'][:stop]
            actual=sum((abs(Q(r['actual_coefficient'])) for r in evaluated),Q(0))
            if actual!=Q(old['actual_head_variation']): raise ValueError('same actual original head')
            scopes=[]
            for i,p in enumerate(cert['programs']):
                if p['derivation'] is None: continue
                plans=[next(plan for plan in r['plans'] if plan['program_index']==i) for r in rows]
                scopes.append(dict(program_index=i,maximum_auxiliary_argument=max((max(v['T_u'],v['T_v']) for v in plans),default=1),
                    maximum_cut_argument=max((max(v['u'],v['v']) for v in plans),default=1),
                    strict_rank_rows=sum(v['strict_rank'] for v in plans),
                    universal_base_gate_rows=sum(v['universal_base_gate'] for v in plans),
                    short_zero_support_rows=sum(v['short_zero_support'] for v in plans)))
            measured=[]
            for i in chosen:
                ev=[]
                for r,c in zip(rows,evaluated):
                    plan=next(v for v in r['plans'] if v['program_index']==i)
                    ev.append(next(v for v in c['evaluations'] if (v['u'],v['v'])==(plan['u'],plan['v'])))
                measured.append(dict(program_index=i,
                    actual_separable_variation=CHECK.qtext(sum((abs(Q(v['separable'])) for v in ev),Q(0))),
                    actual_joint_remainder_variation=CHECK.qtext(sum((abs(Q(v['J'])) for v in ev),Q(0))),
                    actual_floor_remainder_variation=CHECK.qtext(sum((abs(Q(v['E'])) for v in ev),Q(0))),
                    actual_joined_short_variation=CHECK.qtext(sum((abs(Q(v['L_u'])+Q(v['L_v'])) for v in ev),Q(0))),
                    actual_separately_priced_short_variation=CHECK.qtext(sum((abs(Q(v['L_u']))+abs(Q(v['L_v'])) for v in ev),Q(0))),
                    actual_direct_variation=CHECK.qtext(sum((abs(Q(v['direct'])) for v in ev),Q(0)))))
            endpoints.append(dict(ratio=ep['ratio'],head_stop=stop,actual_head_variation=str(actual),
                M1=str(Q(ep['M1_scaled'],ep['denominator'])),program_scopes=scopes,diagnostics=measured,
                conditional_prefix_bounds_paid=False,uniform_head_bound_proved=False))
        cases.append(dict(N=cert['N'],y=cert['y'],H=H,theta=oldcase['theta'],endpoints=endpoints))
    return cases


def evaluate_task(task):
    name,programs=task; start=time.monotonic()
    saved=json.loads((PRIOR.PRIOR.OUT/name).read_text()); original,oldcheck=PRIOR.bind_parent(saved)
    pm=SEARCH.Meter(cap=SPEC['work_cap_per_case_meter'],seconds=SPEC['module_seconds'])
    cm=CHECK.Meter(limit=SPEC['work_cap_per_case_meter'],seconds=SPEC['module_seconds'])
    cert=SEARCH.construct_source(original['N'],original['y'],original['max_j'],original['parameters'],programs,pm)
    verdict=CHECK.verify_source(cert,cm)
    for ep,old in zip(verdict['endpoints'],oldcheck['endpoints']):
        if ep['ratio']!=old['ratio'] or len(ep['rows'])!=len(old['rows']):raise ValueError('same complete admitted row family')
        for row,priorrow in zip(ep['rows'],old['rows']):
            if any(row[k]!=priorrow[k] for k in ('j','R','actual_coefficient')):raise ValueError('literal original source row binding')
    cases=summarize(saved,cert,verdict)
    rows=[r for ep in cert['endpoints'] for r in ep['rows']]
    plans=[v for r in rows for v in r['plans']]
    filename=name.replace('convolution_','moment_',1)
    result=dict(source_convolution_file=name,N=cert['N'],y=cert['y'],max_j=cert['max_j'],
        certificate=cert,verification=verdict,source_cases=cases,original_source_binding_proved=True,**SEARCH.FLAGS)
    write(OUT/filename,result)
    return dict(file=filename,N=cert['N'],y=cert['y'],source_cases=cases,
        distinct_rows=len(rows),plan_instances=len(plans),strict_rank_instances=sum(v['strict_rank'] for v in plans),
        universal_base_gate_instances=sum(v['universal_base_gate'] for v in plans),
        short_zero_support_instances=sum(v['short_zero_support'] for v in plans),
        distinct_residual_evaluations=sum(len(r['evaluations']) for e in verdict['endpoints'] for r in e['rows']),
        producer_operations=pm.operations,checker_operations=cm.operations,prospective_algorithm_bytes=pm.peak_bytes_estimate,
        elapsed_seconds=time.monotonic()-start,worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def feedback(programs):
    return dict(schema='mobius-moment-scale-feedback-v1',
        previous_obstruction='070 finite exact correction becomes target-valued constants; their growth is unpaid',
        detector_generated=['rational cut/exposure exponents','conditional separable exponent',
            'exact optimum/failure separating combinations','minimal exposure at optimum','short split and fractional moment exponent'],
        supplied_mathematics=SPEC['supplied_rules'],
        proof_scope='uniform conditional laws for specified components; exact optimality within affine language',
        unresolved_signed_target='sum_(j in head) |J_j|, J_j=L_j(u)+L_j(v)-sum mu(a)mu(b)e_j(ab)',
        exact_original_binding='c_j=d_j-b_j H_mu(u)H_mu(v)+J_j',
        current_rank_warning='J_j=sum_A h_(j,A)M(A)+b_j H_mu(u)H_mu(v); endpoints may reach R_j',
        active_obligations=['uniform joined signed J control or stronger coupled control',
            'uniform Mertens premise through every auxiliary T','explicit complete base-row price',
            'common-rank invariant and full C-polynomial closure','filled-core and ordinary-zeta/RH transfer'],
        next_search_input='the literal signed J expression, source steps and current-rank endpoints; do not substitute a smaller-rank prefix premise',
        practical_next_grammar=['signed floor-state scale recurrences','coupled energies with cross terms',
            'arithmetic pairings or correlation reductions with exact residual obligations'],
        target='uniform Oepsilon(N^(1/2+epsilon)) for original head, uniformly over required parameters',
        proof_search_is_automated=True, analytic_rules_were_supplied=True,
        no_new_unconditional_cancellation_theorem=True,uniform_core_bound_proved=False,
        uniform_far_correlation_bound_proved=False,research_goal_complete=False,**SEARCH.FLAGS)


def main():
    if OUT.exists():raise FileExistsError('preserve every071 attempt')
    start=time.monotonic();counts=validate_parent();frozen={n:(ROOT/n).read_bytes() for n in FILES}
    receipts=[json.loads(data) for name,data in frozen.items() if name.endswith('_development.json')]
    development=sum(check_receipt(r) for r in receipts)
    if any(r['final_status']!='PASS' for r in receipts):raise ValueError('new synthetic gates passed before freeze')
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name,data in frozen.items():(OUT/'source_snapshot'/name).write_bytes(data)
    results=[];sampled_peak=0
    try:
        write(OUT/'spec.json',dict(spec=SPEC,prior_frozen_counts=counts,new_frozen_files=len(FILES),frozen_before_scientific_search=True))
        pm=SEARCH.Meter(cap=SPEC['work_cap_per_case_meter']);cm=CHECK.Meter();cache={}
        programs=[SEARCH.construct_program(**r,meter=pm,short_cache=cache) for r in REQUESTS]
        checks=[CHECK.verify_program(p,cm) for p in programs]
        write(OUT/'programs.json',dict(programs=programs,verification=checks,producer_operations=pm.operations,checker_operations=cm.operations))
        emit('moment_programs_certified',programs=len(programs),optimal=sum(p['derivation'] is not None for p in programs),
             infeasible=sum(p['primary']['result']['status']=='infeasible' for p in programs))
        names=sorted(p.name for p in PRIOR.PRIOR.OUT.glob('convolution_*.json'))
        if len(names)!=12:raise ValueError('all12 inherited source groups')
        with mp.get_context('spawn').Pool(SPEC['workers']) as pool:
            iterator=pool.imap_unordered(evaluate_task,[(name,programs) for name in names],chunksize=1)
            while len(results)<len(names):
                if time.monotonic()-start>SPEC['module_seconds']:raise TimeoutError('whole071 deadline')
                rss=PRIOR.PRIOR.PRIOR.aggregate_rss([os.getpid()]+[p.pid for p in pool._pool]);sampled_peak=max(sampled_peak,rss)
                if rss>SPEC['maximum_aggregate_bytes']:raise MemoryError('aggregate071 memory')
                try:result=iterator.next(timeout=1)
                except mp.TimeoutError:continue
                results.append(result);emit('moment_source_checked',N=result['N'],y=result['y'],completed=len(results),total=len(names))
        results.sort(key=lambda r:(r['N'],r['y']));cases=[c for r in results for c in r['source_cases']]
        write(OUT/'summary.json',dict(cases=cases,**SEARCH.FLAGS))
        write(OUT/'group_resources.json',results)
        fb=feedback(programs);write(OUT/'mechanism_feedback.json',fb)
        write(OUT/'next_search_input.json',dict(schema='joined-signed-floor-obligation-v1',
            expression=fb['unresolved_signed_target'],identity=fb['exact_original_binding'],
            current_rank_warning=fb['current_rank_warning'],dependencies=fb['active_obligations'],
            source_certificates=[r['file'] for r in results],supplied_conditional_rules='programs.json',
            next_grammar=fb['practical_next_grammar'],circular_use_of_current_rank_prefix_bound_allowed=False,**SEARCH.FLAGS))
        for name,data in frozen.items():
            if (ROOT/name).read_bytes()!=data:raise ValueError('preserve071 '+name)
        if validate_parent()!=counts:raise ValueError('preserve inherited sources')
        peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        worker=max(r['worker_peak_rss_kib'] for r in results);peak_sum=1024*(peak+SPEC['workers']*worker)
        if peak_sum>SPEC['maximum_aggregate_bytes']:raise MemoryError('conservative process peak sum071')
        report=dict(status='EXACT_UNIFORM_CONDITIONAL_COST_PROGRAMS_AND_JOINED_RESIDUALS_VERIFIED_FULL_CONTROL_OPEN',
            programs=len(programs),exact_optimal_programs=sum(p['derivation'] is not None for p in programs),
            exact_infeasible_programs=sum(p['primary']['result']['status']=='infeasible' for p in programs),
            unresolved_programs=sum(p['derivation'] is None and p['primary']['result']['status']!='infeasible' for p in programs),
            primary_solver_calls=len(programs),secondary_solver_calls=sum(p['secondary'] is not None for p in programs),
            short_solver_calls=len(cache),farkas_solver_calls=sum('farkas_iterations' in p['primary']['result']['solver'] for p in programs),
            source_cases=len(cases),independent_source_groups=len(results),
            new_synthetic_tests=sum(r['unique_new_synthetic_tests'] for r in receipts),
            test_invocations=sum(sum(t['tests'] for t in r['runs']) for r in receipts),development_operations=development,
            symbolic_producer_operations=pm.operations,symbolic_checker_operations=cm.operations,
            elapsed_seconds=time.monotonic()-start,parent_peak_rss_kib=peak,largest_worker_peak_rss_kib=worker,
            sampled_aggregate_rss_peak_bytes=sampled_peak,conservative_sum_of_process_peaks_bytes=peak_sum,
            largest_prospective_algorithm_bytes=max(r['prospective_algorithm_bytes'] for r in results),
            workers=SPEC['workers'],native_threads_per_worker=1,prior_frozen_counts=counts,new_frozen_source_count=len(FILES),
            original_source_binding_proved=True,learner_mobius_signs_accessed=False,
            old_scientific_studies_or_suites_replayed=False,hashes_used=False,fresh_holdout_claim=False,
            supplied_analytic_rules_not_detector_discoveries=True,uniform_core_bound_proved=False,
            uniform_far_correlation_bound_proved=False,RH_refuted=False,**SEARCH.FLAGS)
        for k in ('distinct_rows','plan_instances','strict_rank_instances','universal_base_gate_instances',
                  'short_zero_support_instances','distinct_residual_evaluations','producer_operations','checker_operations'):
            report[k]=sum(r[k] for r in results)
        write(OUT/'report.json',report);emit('moment_scale_complete',status=report['status'],elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json',dict(type=type(exc).__name__,message=str(exc),completed_groups=len(results),RH_proved=False))
        raise


if __name__=='__main__':main()

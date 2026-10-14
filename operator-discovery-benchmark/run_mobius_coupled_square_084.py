"""Prospective joint operator/square search and new-geometry auxiliary checks."""
import os
for key in ('OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','OMP_NUM_THREADS'):os.environ[key]='1'
import json
import random
import resource
import time
import traceback
from copy import deepcopy
from fractions import Fraction as Q
import mobius_coupled_square_084 as SEARCH
import check_mobius_coupled_square_084 as CHECK
import mobius_rh_target_084 as TARGET
import run_mobius_coupled_completion_083 as PRIOR
from run_fractional_prime_kernel_051 import write,emit

ROOT=PRIOR.ROOT;OUT=PRIOR.OUT/'square_completion_followup_001'
FILES=['mobius_coupled_square_084.py','test_mobius_coupled_square_084.py','mobius_coupled_square_search_084_development.json',
       'check_mobius_coupled_square_084.py','test_check_mobius_coupled_square_084.py','mobius_coupled_square_checker_084_development.json',
       'MOBIUS_COUPLED_SQUARE_CHECK_SCOPE_084.txt','mobius_rh_target_084.py','test_mobius_rh_target_084.py',
       'mobius_rh_target_084_development.json','MOBIUS_RH_TARGET_AUDIT_084.txt','MOBIUS_SQUARE_BOUND_REVIEW_084.txt',
       'mobius_coupled_square_protocol_084.txt','run_mobius_coupled_square_084.py']
SPEC=dict(schema='coupled-square-search-protocol-v1',source_ids=['q1_p16','q1_p04'],
          families=['inherited','cofactor','reciprocal','fractional'],calibration_parent=1024,
          seed=20261011084,validation_bands=[[1408,1791],[2304,2815]],fresh_parents_per_band=2,
          diagnostic_exponent_parameters=[1,3,7,15,31],workers=3,native_threads=1,
          module_seconds=7200,max_aggregate_bytes=16*1024**3,discovery_solver_seconds=180,validation_solver_seconds=90,
          square_factor_bits=24,max_effective_dimension=512,theta_box=['-16','16'],
          selection='retain every independently admitted family; freeze theta before all new geometries',
          validation='fixed operator; synthesize new auxiliary factor at each new geometry; this is new certificate search',
          unknown_composite_signs_used=False,observed_full_source_values_used=False,
          known_unit_and_all_prime_signs_used=True,uniform_remaining_bound_proved=False,RH_proved=False,hashes_used=False)


def validate_parent():
    counts=PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'source_snapshot'/name).read_bytes():raise ValueError('preserve083 '+name)
    publication=json.loads((PRIOR.OUT/'publication_integrity.json').read_text())
    for name in publication['postrun_files']:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'postrun_snapshot'/name).read_bytes():raise ValueError('preserve083 postrun '+name)
    return counts+[len(PRIOR.FILES),len(publication['postrun_files'])]


def transfer(source):
    return dict(schema='two-dilation-source-inverse-v1',base_divisor=4,ratios=['1/2','4/5'],
                extra=dict(coefficient='3547/8192',divisor=3)if source=='q1_p04'else None)


def make_program(parent,family):
    p=deepcopy(parent);weights=[]
    for arithmetic in ['all','prime','composite']:
        weights += [dict(kind='source',i=1,arithmetic=arithmetic),dict(kind='product',i=1,j=1,arithmetic=arithmetic),
                    dict(kind='product',i=0,j=1,arithmetic=arithmetic),dict(kind='band',left='1/10',right='1/8',arithmetic=arithmetic)]
    descriptors={'inherited':[],
                 'cofactor':[('1/2','1','0'),('3/2','1','0'),('3','1','0')],
                 'reciprocal':[('1/4','-1','1'),('1/8','-1','1'),('1/12','-1','1')],
                 'fractional':[('1/2','2/5','3/5'),('1/3','5/7','2/7'),('1','11/9','-2/9')]}
    for scale,eta,beta in descriptors[family]:
        for complement in [False,True]:
            cut=dict(scale=scale,n_exponent=eta,u_exponent=beta,complement=complement,unit_balance=True)
            for w in weights:p['coupled_terms'].append(dict(cut=deepcopy(cut),weight=deepcopy(w),theta='0'))
    SEARCH.B.parse_program(p)
    if SEARCH.O.synthesize(p)['status']!='PROPOSED_UNIFORM_WHOLE_OUTER_CONTROL':raise ValueError('initial valid outer family')
    return p


def require(row,status):
    if row.get('status')!=status:raise ValueError('independent084 admission '+str(row))
    return row


def growth_constants(price,u):
    result=[]
    for j in SPEC['diagnostic_exponent_parameters']:
        lo=0;hi=max(1,(Q(price).numerator+Q(price).denominator-1)//Q(price).denominator)
        while lo<hi:
            mid=(lo+hi)//2
            if TARGET.exact_power_comparison(price,u,j,str(mid)):hi=mid
            else:lo=mid+1
        result.append(dict(j=j,energy_exponent=str(TARGET.exponent(j)),constant=str(lo),scope='finite residual-price growth hypothesis only; full drift adds Astar*u'))
    return result


def discovery_task(task):
    started=time.monotonic();row={};u=SPEC['calibration_parent']
    try:
        row=SEARCH.solve(task['program'],u,time_limit=SPEC['discovery_solver_seconds'])
        if row['status']=='EXACT_SQUARE_PROPOSAL':
            if 'dual'not in row:raise ValueError('complete exact SDP grammar dual required')
            row['upper_admission']=require(CHECK.verify_certificate(row['program'],u,row['outer_certificate'],row['certificate']),
                                           'VERIFIED_FINITE_COUPLED_SQUARE_BOUND')
            row['dual_admission']=require(CHECK.verify_dual(row['program'],u,row['outer_certificate'],row['dual']),
                                          'VERIFIED_FINITE_COUPLED_SQUARE_GRAMMAR_LOWER_BOUND')
            row['conditional_target']=TARGET.compile_target(row['program'],transfer(task['source_id']))
            row['calibrated_growth_hypotheses']=growth_constants(row['certificate']['price'],u)
            row['price_over_u']=str(Q(row['certificate']['price'])/u)
            row['price_over_u2']=str(Q(row['certificate']['price'])/(u*u))
    except Exception as exc:
        row.update(status='RESOURCE_REJECTED'if isinstance(exc,(SEARCH.B.ResourceLimit,MemoryError))else'TASK_FAILED',error=str(exc),traceback=traceback.format_exc())
    row.update(id=task['id'],source_id=task['source_id'],family_id=task['family_id'],u=u,
               total_elapsed_seconds=time.monotonic()-started,worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    write(OUT/('search_'+task['id']+'.json'),row)
    return {k:row[k]for k in ('id','source_id','family_id','status','total_elapsed_seconds','worker_peak_rss_kib')}


def validation_task(task):
    candidate,us=task;started=time.monotonic();rows=[]
    for u in us:
        row={}
        try:
            row=SEARCH.solve(candidate['program'],u,optimize_operator=False,time_limit=SPEC['validation_solver_seconds'])
            if row['status']=='EXACT_SQUARE_PROPOSAL':
                if row['program']!=candidate['program']:raise ValueError('frozen operator coefficients changed')
                if row['outer_certificate']!=candidate['outer_certificate']:raise ValueError('frozen complete outer proof changed')
                row['admission']=require(CHECK.verify_certificate(row['program'],u,row['outer_certificate'],row['certificate']),
                                         'VERIFIED_FINITE_COUPLED_SQUARE_BOUND')
                row['calibrated_growth_tests']=[dict(**h,passes=TARGET.exact_power_comparison(row['certificate']['price'],u,h['j'],h['constant']))
                                                for h in candidate['calibrated_growth_hypotheses']]
                row['price_over_u']=str(Q(row['certificate']['price'])/u)
                row['price_over_u2']=str(Q(row['certificate']['price'])/(u*u))
                row.pop('program');row.pop('outer_certificate')
        except Exception as exc:row.update(status='VALIDATION_FAILED',error=str(exc),traceback=traceback.format_exc())
        row['u']=u;rows.append(row)
    report=dict(id=candidate['id'],program=candidate['program'],outer_certificate=candidate['outer_certificate'],rows=rows,
                elapsed_seconds=time.monotonic()-started,worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                operator_coefficients_frozen=True,new_auxiliary_factor_searches=True,new_unknown_sign_data=False,
                uniform_remaining_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False)
    write(OUT/('validation_'+candidate['id']+'.json'),report)
    return {k:report[k]for k in ('id','elapsed_seconds','worker_peak_rss_kib')}


def inventory():
    known=set(PRIOR.inventory()['parents'])
    for u in json.loads((PRIOR.OUT/'validation_draw.json').read_text())['parents']:
        known.update(u//2**i for i in range(4))
    known.update([1,5,15,23,29,47,91,131,137,211,401,1024])
    return dict(parents=sorted(known),registered083_and_delays=True,development_geometry_included=True)


def main():
    started=time.monotonic();counts=validate_parent();PRIOR.stage_check(started,[os.getpid()])
    for k in ['workers','module_seconds','max_aggregate_bytes']:
        if SPEC[k]!=PRIOR.SPEC[k]:raise ValueError('shared pool guard mismatch '+k)
    if OUT.exists():raise FileExistsError('preserve084 run directory')
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name in FILES:(OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(OUT/'protocol.json',dict(**SPEC,source_files=FILES,prior_byte_preserved_files=sum(counts),previous_goal_turn='PROGRESS'))
    parents=[c for c in json.loads((PRIOR.OUT/'frozen_candidates.json').read_text())['candidates']if 'outer_certificate'in c]
    tasks=[]
    for source in SPEC['source_ids']:
        parent=next(c for c in parents if c['source_id']==source)
        for family in SPEC['families']:
            tasks.append(dict(id=source+'_'+family,source_id=source,family_id=family,parent_id=parent['id'],program=make_program(parent['program'],family)))
    write(OUT/'frozen_task_roster.json',dict(tasks=tasks,registered_before_calibration=True))
    known=inventory();write(OUT/'prior_parent_inventory.json',known)
    discovery=PRIOR.pool_tasks(discovery_task,tasks,started,'joint_operator_square_discovery')
    rows=[json.loads((OUT/('search_'+t['id']+'.json')).read_text())for t in tasks]
    admitted=[r for r in rows if r['status']=='EXACT_SQUARE_PROPOSAL']
    selected=[{k:r[k]for k in ('id','source_id','family_id','program','outer_certificate','certificate','dual','calibrated_growth_hypotheses')}for r in admitted]
    write(OUT/'frozen_candidates.json',dict(candidates=selected,all_admitted_families_retained=True,operator_frozen_before_draw=True,
                                          validation_will_synthesize_new_auxiliary_factors=True))
    rng=random.Random(SPEC['seed']);excluded=set(known['parents']);us=[];draws=[]
    for lo,hi in SPEC['validation_bands']:
        accepted=0
        while accepted<SPEC['fresh_parents_per_band']:
            u=rng.randint(lo,hi);ok=u not in excluded
            draws.append(dict(u=u,band=[lo,hi],status='ACCEPTED'if ok else'REJECTED_PREVIOUS_OR_DUPLICATE'))
            if ok:us.append(u);excluded.add(u);accepted+=1
    us.sort();write(OUT/'validation_draw.json',dict(seed=SPEC['seed'],parents=us,draws=draws,drawn_after_operator_freeze=True))
    validation=PRIOR.pool_tasks(validation_task,[(c,us)for c in selected],started,'fixed_operator_new_auxiliary_factors')
    checks=[json.loads((OUT/('validation_'+v['id']+'.json')).read_text())for v in validation]
    vrows=[r for v in checks for r in v['rows']];good=[r for r in vrows if r['status']=='EXACT_SQUARE_PROPOSAL']
    for name in FILES:
        if (ROOT/name).read_bytes()!=(OUT/'source_snapshot'/name).read_bytes():raise ValueError('084 frozen source changed '+name)
    if validate_parent()!=counts:raise ValueError('prior preservation changed')
    report=dict(status='COMPLETE_COUPLED_SQUARE_SEARCH',tasks=len(tasks),admitted_proposals=len(admitted),frozen_operators=len(selected),
                new_geometry_parents=us,new_auxiliary_rows=len(vrows),independently_admitted_auxiliary_rows=len(good),
                discovery=discovery,validation=validation,elapsed_seconds=time.monotonic()-started,
                sampled_aggregate_peak_rss_bytes=PRIOR._PEAK,
                conservative_process_peak_sum_bytes=1024*(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss+
                    SPEC['workers']*max([r['worker_peak_rss_kib']for r in discovery+validation]+[0])),
                constructor_operations=sum(r.get('ops',0)for r in rows)+sum(r.get('ops',0)for r in good),
                independent_discovery_operations=sum(r['upper_admission']['ops']+r['dual_admission']['ops']for r in admitted),
                independent_validation_operations=sum(r['admission']['ops']for r in good),
                operation_accounting_scope='Instrumented matrix and factor work; excludes solver instructions, symbolic outer setup, conditional target compilation and exact growth comparisons',
                growth_hypotheses_by_j=[dict(j=j,passes=sum(t['passes']for r in good for t in r['calibrated_growth_tests']if t['j']==j),
                                             tested=sum(t['j']==j for r in good for t in r['calibrated_growth_tests']))for j in SPEC['diagnostic_exponent_parameters']],
                operator_coefficients_frozen_at_validation=True,new_auxiliary_factor_searches_at_validation=True,
                prior_frozen_files=sum(counts),source_bytes_preserved=True,known_unit_and_all_prime_signs_used=True,
                unknown_composite_signs_used=False,observed_full_source_values_used=False,
                uniform_remaining_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False,hashes_used=False)
    write(OUT/'report.json',report);PRIOR.stage_check(started,[os.getpid()])
    emit({k:v for k,v in report.items()if k not in ['discovery','validation']})


if __name__=='__main__':main()

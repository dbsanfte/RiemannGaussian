"""Prospective witness-driven identity discovery on the complete signed residual."""
import os
for key in ('OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','OMP_NUM_THREADS'):os.environ[key]='1'
import gc
import json
import random
import resource
import time
import traceback
from fractions import Fraction as Q
import mobius_annihilator_085 as SEARCH
import mobius_annihilator_bank_085 as BANK
import check_mobius_annihilator_085 as CHECK
import run_mobius_coupled_square_084 as PRIOR
from run_fractional_prime_kernel_051 import write,emit

ROOT=PRIOR.ROOT;OUT=PRIOR.OUT/'annihilator_followup_001';POOL=PRIOR.PRIOR
FILES=['mobius_annihilator_085.py','mobius_annihilator_bank_085.py',
       'test_mobius_annihilator_085.py','mobius_annihilator_search_085_development.json',
       'check_mobius_annihilator_085.py','test_check_mobius_annihilator_085.py',
       'mobius_annihilator_checker_085_development.json','MOBIUS_ANNIHILATOR_CHECK_SCOPE_085.txt',
       'MOBIUS_ANNIHILATOR_REVIEW_085.txt','mobius_annihilator_protocol_085.txt',
       'run_mobius_annihilator_085.py']
SPEC=dict(schema='adaptive-annihilator-search-protocol-v1',training_parents=[1603,1738,2651,2766],
          calibration_parent=1024,scale_height=12,exponent_height=8,bank_size=8,
          modes=['adaptive','grammar_order'],seed=20261011085,
          validation_bands=[[1872,2279],[3008,3503]],fresh_parents_per_band=1,
          diagnostic_exponent_parameters=[1,3,7,15,31],workers=3,native_threads=1,
          solver_seconds=90,module_seconds=7200,max_aggregate_bytes=16*1024**3,
          fixed_operators='all eight independently admitted084 programs; no operator retuning',
          bank_selection='greedy exact normalized witness violation; diminishing coverage; grammar-order ties',
          baseline='first eight nonzero forms in the same grammar order; calibration only',
          prospective_draw_values_seen_in_preflight=True,
          no_scientific_validation_outcomes_seen_before_freeze=True,
          validation='retain every adaptive bank, including calibration failures; new S and L per geometry',
          growth_constants='retain084 hypotheses without refitting',
          known_unit_and_all_prime_signs_used=True,unknown_composite_signs_used=False,
          observed_full_source_values_used=False,uniform_remaining_bound_proved=False,RH_proved=False,hashes_used=False)


def read(path):return json.loads(path.read_text())


def validate_parent():
    counts=PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'source_snapshot'/name).read_bytes():raise ValueError('preserve084 '+name)
    publication=read(PRIOR.OUT/'publication_integrity.json')
    for name in publication['postrun_files']:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'postrun_snapshot'/name).read_bytes():raise ValueError('preserve084 postrun '+name)
    return counts+[len(PRIOR.FILES),len(publication['postrun_files'])]


def inventory():
    known=set(PRIOR.inventory()['parents'])
    for u in read(PRIOR.OUT/'validation_draw.json')['parents']+[SPEC['calibration_parent']]:
        known.update(u//2**i for i in range(4))
    return dict(parents=sorted(known),registered084_and_delays=True,development_geometry_included=True)


def learn_bank(candidate):
    started=time.monotonic();parents=SPEC['training_parents'];witnesses={};bindings=[]
    for u in parents:
        name='witness_'+candidate['id']+'_'+str(u)+'.json';row=read(PRIOR.OUT/name)
        if row['candidate_id']!=candidate['id']or row['u']!=u or row['admission']['status']!='VERIFIED_FINITE_FIXED_OPERATOR_SQUARE_LOWER_BOUND':
            raise ValueError('exact prior artificial witness binding')
        witnesses[u]=row['certificate']['signs'];bindings.append(dict(u=u,file=name,certificate=row['certificate']))
    data=BANK.catalog(candidate['program'],parents,SPEC['scale_height'],SPEC['exponent_height'])
    choices={mode:BANK.select(data,witnesses,SPEC['bank_size'],adaptive=mode=='adaptive')for mode in SPEC['modes']}
    result=dict(id=candidate['id'],witness_bindings=bindings,generated=data['generated'],
                representatives=[{k:v for k,v in row.items()if k!='column_keys'}for row in data['representatives']],
                training_only_duplicates=data['training_only_duplicates'],choices=choices,
                prospective_catalog_bytes=data['prospective_catalog_bytes'],
                ops=sum(m['meter'].ops for m in data['models'].values())+sum(c['scalar_operations']for c in choices.values()),
                elapsed_seconds=time.monotonic()-started,training_only=True,
                unknown_composite_signs_used=False,uniform_remaining_bound_proved=False)
    write(OUT/('bank_'+candidate['id']+'.json'),result)
    return choices,dict(id=candidate['id'],generated=len(data['generated']),representatives=len(data['representatives']),
                        prospective_catalog_bytes=data['prospective_catalog_bytes'],ops=result['ops'],elapsed_seconds=result['elapsed_seconds'])


def solve_task(task):
    started=time.monotonic();row={};u=task['u'];candidate=task['candidate']
    try:
        row=SEARCH.solve(candidate['program'],task['bank'],u,time_limit=SPEC['solver_seconds'])
        if row['status']=='EXACT_ANNIHILATOR_SQUARE_PROPOSAL':
            row['admission']=CHECK.verify_certificate(candidate['program'],u,candidate['outer_certificate'],task['bank'],row['certificate'])
            if row['admission']['status']!='VERIFIED_FINITE_ANNIHILATOR_SQUARE_BOUND':raise ValueError('independent085 admission '+str(row['admission']))
            row['frozen_growth_tests']=[dict(**h,passes=PRIOR.TARGET.exact_power_comparison(row['certificate']['price'],u,h['j'],h['constant']))
                                      for h in candidate['calibrated_growth_hypotheses']]
            row['price_over_u2']=str(Q(row['certificate']['price'])/(u*u))
            if task['stage']=='calibration':
                old=read(PRIOR.OUT/('search_'+candidate['id']+'.json'))
                row['saved084_comparison']=dict(price=old['certificate']['price'],
                    exact_reduction=str(Q(old['certificate']['price'])-Q(row['certificate']['price'])),
                    same_operator=True,same_geometry=True,old_solver_seconds=old['solver_seconds'],
                    scope='saved084 certificate comparison, unequal numerical solve budgets; no old rerun')
    except Exception as exc:
        row.update(status='RESOURCE_REJECTED'if isinstance(exc,(SEARCH.B.ResourceLimit,MemoryError))else'TASK_FAILED',
                   error=str(exc),traceback=traceback.format_exc())
    row.update(id=task['id'],candidate_id=candidate['id'],source_id=candidate['source_id'],family_id=candidate['family_id'],
               mode=task['mode'],stage=task['stage'],u=u,bank=task['bank'],
               total_elapsed_seconds=time.monotonic()-started,
               worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    write(OUT/('bound_'+task['id']+'.json'),row)
    return {k:row[k]for k in ('id','candidate_id','stage','mode','u','status','total_elapsed_seconds','worker_peak_rss_kib')}


def make_task(candidate,mode,u,stage):
    return dict(id=candidate['id']+'_'+mode+'_'+str(u),candidate=candidate,
                bank=candidate['banks'][mode],mode=mode,u=u,stage=stage)


def main():
    started=time.monotonic();counts=validate_parent();POOL.stage_check(started,[os.getpid()])
    for key in ['workers','module_seconds','max_aggregate_bytes']:
        if SPEC[key]!=POOL.SPEC[key]:raise ValueError('shared pool guard mismatch '+key)
    if OUT.exists():raise FileExistsError('preserve085 run directory')
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name in FILES:(OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(OUT/'protocol.json',dict(**SPEC,source_files=FILES,prior_byte_preserved_files=sum(counts)))
    candidates=read(PRIOR.OUT/'frozen_candidates.json')['candidates']
    if len(candidates)!=8:raise ValueError('retain all eight prior operators')
    if SPEC['training_parents']!=read(PRIOR.OUT/'validation_draw.json')['parents']:raise ValueError('registered084 training geometry')
    write(OUT/'frozen_operator_roster.json',dict(candidates=candidates,frozen_before_identity_selection=True))
    known=inventory();write(OUT/'prior_parent_inventory.json',known);summaries=[];selected=[]
    for candidate in candidates:
        choices,summary=learn_bank(candidate);summaries.append(summary)
        selected.append(dict(**candidate,banks={mode:choices[mode]['bank']for mode in SPEC['modes']},
                             selected_descriptor_ids={mode:choices[mode]['selected_ids']for mode in SPEC['modes']}))
        gc.collect();POOL.stage_check(started,[os.getpid()]);emit(dict(stage='adaptive_identity_selection',**summary))
    write(OUT/'frozen_candidates.json',dict(candidates=selected,all_prior_operators_retained=True,
          banks_frozen_before_calibration_and_draw=True,new_auxiliary_coefficients_at_each_geometry=True))
    tasks=[make_task(c,mode,SPEC['calibration_parent'],'calibration')for c in selected for mode in SPEC['modes']]
    write(OUT/'calibration_roster.json',dict(tasks=tasks))
    calibration=POOL.pool_tasks(solve_task,tasks,started,'annihilator_calibration_and_ablation')
    rng=random.Random(SPEC['seed']);excluded=set(known['parents']);us=[];draws=[]
    for lo,hi in SPEC['validation_bands']:
        accepted=0
        while accepted<SPEC['fresh_parents_per_band']:
            u=rng.randint(lo,hi);ok=u not in excluded
            draws.append(dict(u=u,band=[lo,hi],status='ACCEPTED'if ok else'REJECTED_PREVIOUS_OR_DUPLICATE'))
            if ok:us.append(u);excluded.add(u);accepted+=1
    us.sort();write(OUT/'validation_draw.json',dict(seed=SPEC['seed'],parents=us,draws=draws,drawn_after_bank_freeze=True,
         prospective_draw_values_seen_in_preflight=True,no_validation_outcomes_seen_before_freeze=True))
    tasks=[make_task(c,'adaptive',u,'validation')for c in selected for u in us]
    write(OUT/'validation_roster.json',dict(tasks=tasks,includes_all_adaptive_banks_even_if_calibration_failed=True))
    validation=POOL.pool_tasks(solve_task,tasks,started,'fixed_banks_new_signed_controls')
    outcomes=calibration+validation;rows=[read(OUT/('bound_'+r['id']+'.json'))for r in outcomes]
    good=[r for r in rows if r['status']=='EXACT_ANNIHILATOR_SQUARE_PROPOSAL']
    fresh=[r for r in good if r['stage']=='validation']
    for name in FILES:
        if (ROOT/name).read_bytes()!=(OUT/'source_snapshot'/name).read_bytes():raise ValueError('085 frozen source changed '+name)
    if validate_parent()!=counts:raise ValueError('prior preservation changed')
    report=dict(status='COMPLETE_ADAPTIVE_ANNIHILATOR_SEARCH',operators=len(selected),bank_selection=summaries,
        calibration_rows=len(calibration),calibration_admitted=sum(r['stage']=='calibration'for r in good),
        new_geometry_parents=us,new_auxiliary_rows=len(validation),new_auxiliary_admitted=len(fresh),outcomes=outcomes,
        elapsed_seconds=time.monotonic()-started,sampled_aggregate_peak_rss_bytes=POOL._PEAK,
        conservative_process_peak_sum_bytes=1024*(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss+
            SPEC['workers']*max([r['worker_peak_rss_kib']for r in outcomes]+[0])),
        bank_selection_operations=sum(r['ops']for r in summaries),
        constructor_operations=sum(r.get('ops',0)for r in rows),independent_operations=sum(r['admission']['ops']for r in good),
        operation_accounting_scope='instrumented geometry, exact identity and matrix work, bounded exact scalar scoring; excludes solver instructions and symbolic growth comparisons',
        growth_hypotheses_by_j=[dict(j=j,passes=sum(t['passes']for r in fresh for t in r['frozen_growth_tests']if t['j']==j),
             tested=sum(t['j']==j for r in fresh for t in r['frozen_growth_tests']))for j in SPEC['diagnostic_exponent_parameters']],
        baseline_scope='calibration only; no fresh-baseline comparison',
        fixed_operators_and_banks=True,new_auxiliary_coefficient_searches=True,
        prior_frozen_files=sum(counts),source_bytes_preserved=True,known_unit_and_all_prime_signs_used=True,
        unknown_composite_signs_used=False,observed_full_source_values_used=False,
        uniform_remaining_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False,hashes_used=False)
    write(OUT/'report.json',report);POOL.stage_check(started,[os.getpid()])
    emit({k:v for k,v in report.items()if k not in ['outcomes','bank_selection']})


if __name__=='__main__':main()

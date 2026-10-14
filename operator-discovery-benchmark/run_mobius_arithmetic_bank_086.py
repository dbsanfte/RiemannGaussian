"""Counterexample-guided arithmetic information discovery on the full remainder."""
import os
for key in ('OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','OMP_NUM_THREADS'):os.environ[key]='1'
import copy
import gc
import json
import random
import resource
import time
import traceback
from fractions import Fraction as Q
import mobius_arithmetic_bank_086 as BANK
import mobius_mixed_zero_086 as UPPER
import mobius_bank_witness_086 as LOWER
import check_mobius_arithmetic_bank_086 as CHECK
import run_mobius_annihilator_085 as PRIOR
from run_fractional_prime_kernel_051 import write,emit

ROOT=PRIOR.ROOT;OUT=PRIOR.OUT/'arithmetic_bank_followup_001';POOL=PRIOR.POOL
FILES=['mobius_arithmetic_bank_086.py','mobius_mixed_zero_086.py','mobius_bank_witness_086.py',
       'check_mobius_arithmetic_bank_086.py','test_mobius_arithmetic_bank_086.py',
       'test_mobius_mixed_zero_086.py','test_mobius_bank_witness_086.py','test_check_mobius_arithmetic_bank_086.py',
       'mobius_arithmetic_bank_checker_086_development.json','mobius_mixed_zero_development_attempts_086.json',
       'mobius_bank_witness_086_development.json','MOBIUS_MIXED_ZERO_DEVELOPMENT_086.txt',
       'MOBIUS_BANK_WITNESS_DEVELOPMENT_086.txt',
       'MOBIUS_ARITHMETIC_BANK_CHECK_SCOPE_086.txt','MOBIUS_ARITHMETIC_BANK_REVIEW_086.txt',
       'mobius_arithmetic_bank_protocol_086.txt','run_mobius_arithmetic_bank_086.py']
SPEC=dict(schema='counterexample-guided-arithmetic-bank-protocol-v1',training_parent=3475,
          initial_bank='all eight adaptive085 divisor descriptors for each of all eight frozen084 operators',
          modes=['divisor','union'],maximum_additions=4,maximum_bank_size=12,
          divisor_scale_height=12,prime_scale_height=8,exponent_height=8,
          witness_attempts=4,witness_seconds_per_attempt=10,witness_seed=20261011086,
          shared_initial_witness=True,trigger_j=31,trigger_constant='1',
          trigger='strict exact lower_bound > C*u^(1+1/j) for the frozen residual target',
          selection='maximum exact squared violation / complete column norm; stable grammar order ties',
          validation_seed=20261012086,validation_bands=[[3600,4095]],fresh_parents_per_band=1,
          upper_solver_seconds=90,upper_work_limit=100_000_000_000_000,
          upper_work_scope='estimated conservative SCS dense-cone work charged prospectively; not an instruction bound;085 excluded solver instructions',
          workers=3,native_threads=1,module_seconds=7200,max_aggregate_bytes=16*1024**3,
          fresh_bounds='both learned banks at new geometry, with new W and L; fixed operators and symbolic banks',
          diagnostic_exponent_parameters=[1,3,7,15,31],
          training_final_upper_retains_initial=True,selection_uses_upper_results=False,
          no_scientific_validation_outcomes_seen_before_bank_freeze=True,
          prospective_draw_values_seen_in_preflight=False,
          known_unit_and_all_prime_signs_used=True,unknown_composite_signs_used=False,
          observed_full_source_values_used=False,uniform_remaining_bound_proved=False,RH_proved=False,hashes_used=False)


def read(path):return json.loads(path.read_text())


def validate_parent():
    counts=PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'source_snapshot'/name).read_bytes():raise ValueError('preserve085 '+name)
    publication=read(PRIOR.OUT/'publication_integrity.json')
    for name in publication['postrun_files']:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'postrun_snapshot'/name).read_bytes():raise ValueError('preserve085 postrun '+name)
    return counts+[len(PRIOR.FILES),len(publication['postrun_files'])]


def inventory():
    known=set(PRIOR.inventory()['parents'])
    for u in read(PRIOR.OUT/'validation_draw.json')['parents']+[PRIOR.SPEC['calibration_parent'],SPEC['training_parent']]:
        known.update(u//2**i for i in range(4))
    known.update(range(1,257))
    return dict(parents=sorted(known),registered085_and_delays=True,tiny_development_geometry_included=True)


def target_excluded(value,u,j=None,constant=None):
    j=SPEC['trigger_j']if j is None else j;constant=SPEC['trigger_constant']if constant is None else constant
    if type(j)is not int or j<1 or type(u)is not int or u<1 or Q(constant)<=0:raise ValueError('positive exact trigger domain')
    q=Q(value)
    if q<=0:return False
    c=Q(constant)
    if max(j*(abs(q.numerator).bit_length()+c.denominator.bit_length()),
           j*(q.denominator.bit_length()+abs(c.numerator).bit_length())+(j+1)*u.bit_length())>100000:raise BANK.B.ResourceLimit('prospective exact target comparison bit gate')
    return not PRIOR.PRIOR.TARGET.exact_power_comparison(str(q),u,j,constant)


def lower_search(candidate,bank,u,label,seed):
    started=time.monotonic();result={}
    try:
        model=UPPER.build_model(candidate['program'],u)
        result=LOWER.solve_model(model,bank,time_limit=SPEC['witness_seconds_per_attempt'],
                                 attempts=SPEC['witness_attempts'],seed=seed)
        if result['status']=='EXACT_BOOLEAN_BANK_INFEASIBLE':
            result.update(status='ARITHMETIC_IDENTITY_IMPLEMENTATION_INCONSISTENCY',
                          reason='The actual anchored Mobius vector proves feasibility of every correctly constructed bank.')
        if result.get('certificate')is not None:
            result['admission']=CHECK.verify_lower(candidate['program'],u,candidate['outer_certificate'],bank,result['certificate'])
            if result['admission']['status']!='VERIFIED_FINITE_ARITHMETIC_BANK_LOWER_BOUND':raise ValueError('independent lower admission '+str(result['admission']))
            result['excludes_frozen_target']=target_excluded(result['certificate']['lower_bound'],u)
            result['lower_bound_over_u']=str(Q(result['certificate']['lower_bound'])/u)
    except Exception as exc:
        result.update(status='RESOURCE_REJECTED'if isinstance(exc,(BANK.B.ResourceLimit,MemoryError))else'TASK_FAILED',
                      error=str(exc),traceback=traceback.format_exc())
        # A certificate retained after a failed independent check is evidence
        # of that failure only; it cannot trigger any extension.
    result.update(id=label,candidate_id=candidate['id'],u=u,bank=bank,seed=seed,
                  total_elapsed_seconds=time.monotonic()-started,
                  worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    write(OUT/('witness_'+label+'.json'),result)
    return result


def admitted_lower(row):
    return row.get('status')=='EXACT_COMPATIBLE_BANK_WITNESS_PROPOSAL'and row.get('admission',{}).get('status')=='VERIFIED_FINITE_ARITHMETIC_BANK_LOWER_BOUND'


def learn_task(task):
    started=time.monotonic();c=task['candidate'];u=SPEC['training_parent'];initial=c['initial_bank'];result={}
    try:
        model=UPPER.build_model(c['program'],u)
        generated=BANK.grammar(model['program']['memory'],SPEC['divisor_scale_height'],SPEC['prime_scale_height'],SPEC['exponent_height'])
        catalog=BANK.catalog(model,generated)
        write(OUT/('catalog_'+c['id']+'.json'),{k:v for k,v in catalog.items()if k!='columns'})
        base_seed=SPEC['witness_seed']+1000*task['operator_index']
        shared=lower_search(c,initial,u,c['id']+'_initial_'+str(u),base_seed)
        arms={}
        for mode in SPEC['modes']:
            bank=copy.deepcopy(initial);current=shared;steps=[];stop='ADDITION_BUDGET_EXHAUSTED'
            for iteration in range(SPEC['maximum_additions']):
                if current.get('status')=='ARITHMETIC_IDENTITY_IMPLEMENTATION_INCONSISTENCY':raise ArithmeticError('exact Boolean bank contradiction; retain witness artifact and investigate implementation')
                if not admitted_lower(current):stop='NO_ADMITTED_COMPATIBLE_WITNESS';break
                if not current['excludes_frozen_target']:stop='CURRENT_WITNESS_DOES_NOT_EXCLUDE_TARGET';break
                choice=BANK.choose_extension(catalog,current['certificate']['signs'],allow_prime_pairs=mode=='union')
                step=dict(iteration=iteration,old_bank=copy.deepcopy(bank),witness_file='witness_'+current['id']+'.json',
                          choice=choice,trigger_j=SPEC['trigger_j'],trigger_constant=SPEC['trigger_constant'])
                if choice['selected']is None:
                    step['status']='NO_VIOLATING_IDENTITY_IN_GRAMMAR';steps.append(step);stop=step['status'];break
                added=choice['selected']['descriptor']
                admission=CHECK.verify_extension(c['program'],u,c['outer_certificate'],bank,current['certificate'],added)
                step['extension_admission']=admission
                if admission['status']!='VERIFIED_FINITE_ARITHMETIC_BANK_INFORMATION_GAIN':
                    step['status']='EXTENSION_ADMISSION_FAILED';steps.append(step);stop=step['status'];break
                bank.append(copy.deepcopy(added));step.update(status='EXACT_INFORMATION_GAIN',new_bank=copy.deepcopy(bank))
                steps.append(step)
                label=c['id']+'_'+mode+'_round'+str(iteration+1)+'_'+str(u)
                write(OUT/('extension_'+label+'.json'),step)
                current=lower_search(c,bank,u,label,base_seed+iteration+1)
                if current.get('status')=='ARITHMETIC_IDENTITY_IMPLEMENTATION_INCONSISTENCY':raise ArithmeticError('exact Boolean bank contradiction after extension; retain artifacts and investigate implementation')
                emit(dict(stage='arithmetic_enrichment',id=c['id'],mode=mode,addition=iteration+1,
                          kind=added['kind'],witness_status=current['status']))
            arms[mode]=dict(bank=bank,steps=steps,stop_reason=stop,
                            final_witness_file='witness_'+current['id']+'.json',
                            added_count=len(bank)-len(initial),final_witness_admitted=admitted_lower(current),
                            final_target_excluded=current.get('excludes_frozen_target')if admitted_lower(current)else None)
        result.update(status='COMPLETE_ARITHMETIC_ENRICHMENT',initial_bank=initial,arms=arms,
                      generated=len(generated),representatives=len(catalog['representatives']),
                      prospective_catalog_bytes=catalog['prospective_catalog_bytes'],catalog_operations=model['meter'].ops,
                      shared_initial_witness_file='witness_'+shared['id']+'.json')
    except Exception as exc:
        result.update(status='RESOURCE_REJECTED'if isinstance(exc,(BANK.B.ResourceLimit,MemoryError))else'TASK_FAILED',
                      error=str(exc),traceback=traceback.format_exc())
    result.update(id=c['id'],candidate_id=c['id'],training_u=u,total_elapsed_seconds=time.monotonic()-started,
                  worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                  uniform_remaining_bound_proved=False,unknown_composite_signs_used=False)
    write(OUT/('bank_'+c['id']+'.json'),result)
    return {k:result[k]for k in ('id','status','total_elapsed_seconds','worker_peak_rss_kib')}


def embedded_incumbent(candidate,bank,u,path):
    old=read(OUT/path)
    if old['candidate_id']!=candidate['id']or old['u']!=u:raise ValueError('bound incumbent binding')
    if old['status']!='EXACT_MIXED_ZERO_SQUARE_PROPOSAL':
        return dict(status='NO_ADMITTED_INITIAL_INCUMBENT',source_file=path,source_status=old['status'])
    old_bank=old['bank']
    if bank[:len(old_bank)]!=old_bank:raise ValueError('bound incumbent bank must be a prefix')
    cert=copy.deepcopy(old['certificate']);cert['partner_matrix']=[r+['0']*(len(bank)-len(old_bank))for r in cert['partner_matrix']]
    admission=CHECK.verify_upper(candidate['program'],u,candidate['outer_certificate'],bank,cert)
    if admission['status']!='VERIFIED_FINITE_ARITHMETIC_BANK_MIXED_UPPER_BOUND':raise ValueError('embedded incumbent exact admission')
    return dict(status='EXACT_EMBEDDED_INCUMBENT',source_file=path,certificate=cert,admission=admission,exact_zero_partner_embedding=True)


def upper_task(task):
    started=time.monotonic();c=task['candidate'];u=task['u'];bank=task['bank'];row={}
    try:
        model=UPPER.build_model(c['program'],u,meter=UPPER.B.Meter(SPEC['upper_work_limit']))
        V,identity_metadata=BANK.vectors(model,bank)
        row=UPPER.solve_model(model,V,time_limit=SPEC['upper_solver_seconds'])
        row['identity_metadata']=identity_metadata
    except Exception as exc:
        row.update(status='RESOURCE_REJECTED'if isinstance(exc,(BANK.B.ResourceLimit,MemoryError))else'TASK_FAILED',
                   error=str(exc),traceback=traceback.format_exc())
    # Independent incumbent admission also runs after a failed new search.
    # A failure remains recorded even when this fallback supplies the bound.
    path=task.get('incumbent_file')
    if path:
        try:
            inherited=embedded_incumbent(c,bank,u,path);row['inherited_incumbent']=inherited
            successful=row.get('status')=='EXACT_MIXED_ZERO_SQUARE_PROPOSAL'
            if inherited['status']=='EXACT_EMBEDDED_INCUMBENT'and(not successful or Q(inherited['certificate']['price'])<Q(row['certificate']['price'])):
                if successful:
                    row['search_certificate']=row['certificate'];row['search_selected_attempt']=row['selected_attempt']
                else:
                    row['search_failure']={k:row[k]for k in ('status','error','traceback')if k in row}
                    row.pop('error',None);row.pop('traceback',None)
                row['certificate']=inherited['certificate'];row['selected_attempt']='EMBEDDED_INITIAL_BANK_INCUMBENT'
                row['status']='EXACT_MIXED_ZERO_SQUARE_PROPOSAL'
                row['diagnostics_scope']='new mixed search before optional initial-incumbent embedding; selected exact traces are in admission'
        except Exception as exc:
            row['incumbent_failure']=dict(error=str(exc),traceback=traceback.format_exc())
    if row.get('status')=='EXACT_MIXED_ZERO_SQUARE_PROPOSAL':
        try:
            row['admission']=CHECK.verify_upper(c['program'],u,c['outer_certificate'],bank,row['certificate'])
            if row['admission']['status']!='VERIFIED_FINITE_ARITHMETIC_BANK_MIXED_UPPER_BOUND':raise ValueError('independent upper admission '+str(row['admission']))
            row['price_over_u']=str(Q(row['certificate']['price'])/u)
            row['frozen_growth_tests']=[dict(**h,passes=PRIOR.PRIOR.TARGET.exact_power_comparison(row['certificate']['price'],u,h['j'],h['constant']))
                                      for h in c['calibrated_growth_hypotheses']]
        except Exception as exc:
            row.update(status='RESOURCE_REJECTED'if isinstance(exc,(BANK.B.ResourceLimit,MemoryError))else'TASK_FAILED',
                       error=str(exc),traceback=traceback.format_exc())
    if task['stage']=='validation':
        lower=lower_search(c,bank,u,task['id'],SPEC['witness_seed']+1000*task['operator_index']+100)
        row['witness_file']='witness_'+lower['id']+'.json'
        row['witness_status']=lower['status']
    row.update(id=task['id'],candidate_id=c['id'],source_id=c['source_id'],family_id=c['family_id'],
               mode=task['mode'],stage=task['stage'],u=u,bank=bank,
               total_elapsed_seconds=time.monotonic()-started,
               worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    write(OUT/('bound_'+task['id']+'.json'),row)
    return {k:row[k]for k in ('id','candidate_id','stage','mode','u','status','total_elapsed_seconds','worker_peak_rss_kib')}


def upper_roster(candidates,modes,u,stage):
    tasks=[]
    for index,c in enumerate(candidates):
        for mode in modes:
            task=dict(id=c['id']+'_'+mode+'_'+str(u),candidate=c,operator_index=index,mode=mode,u=u,stage=stage,
                      bank=c['initial_bank']if mode=='initial'else c['banks'][mode])
            if stage=='training'and mode!='initial':task['incumbent_file']='bound_'+c['id']+'_initial_'+str(u)+'.json'
            tasks.append(task)
    return tasks


def main():
    started=time.monotonic();stage_started=started;timings=[];counts=validate_parent();POOL.stage_check(stage_started,[os.getpid()])
    for key in ('workers','module_seconds','max_aggregate_bytes'):
        if SPEC[key]!=POOL.SPEC[key]:raise ValueError('shared stage guard mismatch '+key)
    if OUT.exists():raise FileExistsError('preserve086 scientific attempt')
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name in FILES:
        (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes());POOL.stage_check(stage_started,[os.getpid()])
    write(OUT/'protocol.json',dict(**SPEC,source_files=FILES,prior_byte_preserved_files=sum(counts)))
    old=read(PRIOR.OUT/'frozen_candidates.json')['candidates']
    if len(old)!=8:raise ValueError('retain all eight prior operators')
    candidates=[]
    for c in old:
        initial=[dict(kind='divisor',cut=copy.deepcopy(d))for d in c['banks']['adaptive']]
        if len(initial)!=8:raise ValueError('bind initial eight adaptive085 identities')
        selected={k:copy.deepcopy(c[k])for k in ('id','source_id','family_id','program','outer_certificate','calibrated_growth_hypotheses')}
        selected.update(initial_bank=initial);candidates.append(selected)
    write(OUT/'frozen_operator_roster.json',dict(candidates=candidates,frozen_before_bank_selection=True))
    known=inventory();write(OUT/'prior_parent_inventory.json',known)
    tasks=[dict(id=c['id'],candidate=c,operator_index=i)for i,c in enumerate(candidates)]
    write(OUT/'enrichment_roster.json',dict(tasks=tasks))
    POOL.stage_check(stage_started,[os.getpid()]);timings.append(dict(stage='setup',elapsed_seconds=time.monotonic()-stage_started))
    stage_started=time.monotonic();selection=POOL.pool_tasks(learn_task,tasks,stage_started,'counterexample_arithmetic_information')
    for c in candidates:
        learned=read(OUT/('bank_'+c['id']+'.json'))
        c['enrichment_status']=learned['status']
        # Retain failed operator searches with the unchanged initial bank.
        c['banks']={mode:learned['arms'][mode]['bank']if learned['status']=='COMPLETE_ARITHMETIC_ENRICHMENT'else copy.deepcopy(c['initial_bank'])for mode in SPEC['modes']}
        POOL.stage_check(stage_started,[os.getpid()])
    write(OUT/'frozen_candidates.json',dict(candidates=candidates,all_prior_operators_retained=True,
          banks_frozen_before_upper_search_and_validation_draw=True,new_auxiliary_coefficients_at_each_geometry=True))
    gc.collect()
    POOL.stage_check(stage_started,[os.getpid()]);timings.append(dict(stage='enrichment_and_bank_freeze',elapsed_seconds=time.monotonic()-stage_started))
    stage_started=time.monotonic()
    initial=upper_roster(candidates,['initial'],SPEC['training_parent'],'training')
    write(OUT/'initial_upper_roster.json',dict(tasks=initial))
    initial_results=POOL.pool_tasks(upper_task,initial,stage_started,'initial_bank_mixed_bounds')
    POOL.stage_check(stage_started,[os.getpid()]);timings.append(dict(stage='initial_upper',elapsed_seconds=time.monotonic()-stage_started))
    stage_started=time.monotonic()
    final=upper_roster(candidates,SPEC['modes'],SPEC['training_parent'],'training')
    write(OUT/'training_upper_roster.json',dict(tasks=final))
    final_results=POOL.pool_tasks(upper_task,final,stage_started,'enriched_bank_mixed_bounds')
    POOL.stage_check(stage_started,[os.getpid()]);timings.append(dict(stage='enriched_upper',elapsed_seconds=time.monotonic()-stage_started))
    stage_started=time.monotonic()
    rng=random.Random(SPEC['validation_seed']);excluded=set(known['parents']);us=[];draws=[]
    for lo,hi in SPEC['validation_bands']:
        accepted=0
        while accepted<SPEC['fresh_parents_per_band']:
            u=rng.randint(lo,hi);ok=u not in excluded
            draws.append(dict(u=u,band=[lo,hi],status='ACCEPTED'if ok else'REJECTED_PREVIOUS_OR_DUPLICATE'))
            if ok:us.append(u);excluded.add(u);accepted+=1
    us.sort();write(OUT/'validation_draw.json',dict(seed=SPEC['validation_seed'],parents=us,draws=draws,
          drawn_after_bank_freeze=True,no_validation_outcomes_seen_before_bank_freeze=True,
          prospective_draw_values_seen_in_preflight=SPEC['prospective_draw_values_seen_in_preflight']))
    fresh=[t for u in us for t in upper_roster(candidates,SPEC['modes'],u,'validation')]
    write(OUT/'validation_roster.json',dict(tasks=fresh,includes_all_operators_and_both_arms=True))
    validation=POOL.pool_tasks(upper_task,fresh,stage_started,'fresh_enriched_bounds_and_compatible_witnesses')
    POOL.stage_check(stage_started,[os.getpid()]);timings.append(dict(stage='fresh_draw_bounds_witnesses',elapsed_seconds=time.monotonic()-stage_started))
    stage_started=time.monotonic()
    outcomes=initial_results+final_results+validation;rows=[read(OUT/('bound_'+r['id']+'.json'))for r in outcomes]
    good=[r for r in rows if r['status']=='EXACT_MIXED_ZERO_SQUARE_PROPOSAL'];fresh_good=[r for r in good if r['stage']=='validation']
    gains=[]
    for c in candidates:
        b=read(OUT/('bank_'+c['id']+'.json'))
        if b['status']=='COMPLETE_ARITHMETIC_ENRICHMENT':
            for mode,arm in b['arms'].items():
                gains.append(dict(id=c['id'],mode=mode,added=arm['added_count'],
                                  prime_pair_additions=sum(s['choice']['selected']['descriptor']['kind']=='prime_pair'for s in arm['steps']if s['status']=='EXACT_INFORMATION_GAIN'),
                                  stop_reason=arm['stop_reason'],final_target_excluded=arm['final_target_excluded']))
    for name in FILES:
        if (ROOT/name).read_bytes()!=(OUT/'source_snapshot'/name).read_bytes():raise ValueError('086 frozen source changed '+name)
        POOL.stage_check(stage_started,[os.getpid()])
    if validate_parent()!=counts:raise ValueError('prior source preservation changed')
    report=dict(status='COMPLETE_COUNTEREXAMPLE_ARITHMETIC_BANK_SEARCH',operators=len(candidates),
        enrichment=selection,information_gains=gains,outcomes=outcomes,upper_rows=len(outcomes),upper_admitted=len(good),
        validation_parents=us,validation_rows=len(validation),validation_upper_admitted=len(fresh_good),
        growth_hypotheses_by_j=[dict(j=j,passes=sum(t['passes']for r in fresh_good for t in r['frozen_growth_tests']if t['j']==j),
                                    tested=sum(t['j']==j for r in fresh_good for t in r['frozen_growth_tests']))for j in SPEC['diagnostic_exponent_parameters']],
        elapsed_seconds=time.monotonic()-started,sampled_aggregate_peak_rss_bytes=POOL._PEAK,
        conservative_process_peak_sum_bytes=1024*(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss+SPEC['workers']*max([r['worker_peak_rss_kib']for r in outcomes+selection]+[0])),
        prior_frozen_files=sum(counts),source_bytes_preserved=True,
        stage_timings=timings,elapsed_limit_scope='7200seconds per explicitly delimited stage; total elapsed is reported separately',
        operation_accounting_scope='instrumented exact work plus prospective estimated numerical work; not instruction counts or rigorous solver instruction bounds',
        all_operators_and_outcomes_retained=True,known_unit_and_all_prime_signs_used=True,
        unknown_composite_signs_used=False,observed_full_source_values_used=False,
        uniform_remaining_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False,hashes_used=False)
    POOL.stage_check(stage_started,[os.getpid()]);timings.append(dict(stage='preservation_and_report',elapsed_seconds=time.monotonic()-stage_started))
    write(OUT/'report.json',report);POOL.stage_check(stage_started,[os.getpid()])
    emit({k:v for k,v in report.items()if k not in ('enrichment','information_gains','outcomes')})


if __name__=='__main__':main()

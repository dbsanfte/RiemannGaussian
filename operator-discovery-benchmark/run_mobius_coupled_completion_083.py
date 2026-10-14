"""Complete physical coupled-identity search, exact admissions and fresh scales."""
import os
for key in ('OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','OMP_NUM_THREADS'):
    os.environ[key]='1'
import json
import multiprocessing as mp
import random
import resource
import time
import traceback
from copy import deepcopy
from fractions import Fraction as Q

import mobius_coupled_completion_083 as SEARCH
import check_mobius_coupled_completion_083 as CHECK
import mobius_coupled_outer_control_083 as OUTER
import check_mobius_coupled_outer_control_083 as OUTER_CHECK
import run_mobius_dense_completion_082 as PRIOR
from run_fractional_prime_kernel_051 import write,emit

ROOT=PRIOR.ROOT
OUT=PRIOR.OUT/'coupled_completion_followup_001'
FILES=['mobius_coupled_completion_083.py','test_mobius_coupled_completion_083.py',
       'mobius_coupled_completion_search_083_development.json',
       'check_mobius_coupled_completion_083.py','test_check_mobius_coupled_completion_083.py',
       'mobius_coupled_completion_checker_083_development.json','MOBIUS_COUPLED_COMPLETION_CHECK_SCOPE_083.txt',
       'mobius_coupled_outer_control_083.py','test_mobius_coupled_outer_control_083.py',
       'mobius_coupled_outer_control_083_development.json','MOBIUS_COUPLED_OUTER_CONTROL_SCOPE_083.txt',
       'check_mobius_coupled_outer_control_083.py','test_check_mobius_coupled_outer_control_083.py',
       'mobius_coupled_outer_control_checker_083_development.json','MOBIUS_COUPLED_OUTER_CONTROL_CHECK_SCOPE_083.txt',
       'MOBIUS_COUPLED_CUT_REVIEW_083.txt','MOBIUS_PRIME_ANCHOR_REVIEW_083.txt',
       'mobius_coupled_completion_protocol_083.txt','run_mobius_coupled_completion_083.py']
SPEC=dict(schema='coupled-drift-search-protocol-v1',source_ids=['q1_p16','q1_p04'],
          calibration_parent=1024,seed=20261011083,
          validation_bands=[[1536,2047],[2560,3071],[3584,4095]],fresh_parents_per_band=2,
          workers=3,native_threads=1,module_seconds=7200,lp_seconds=180,
          max_aggregate_bytes=16*1024**3,theta_box=['-16','16'],gram_box=['0','16'],
          drift_multiplier='3/2',prime_anchor=True,
          selection='smallest exact complete anchored price within each source and family; no validation selection',
          unknown_composite_signs_used=False,observed_full_source_values_used=False,
          known_unit_and_all_prime_signs_used=True,all_physical_squarefree_coordinates_retained=True,
          uniform_full_growth_proved=False,uniform_original_source_bound_proved=False,RH_proved=False,hashes_used=False)


def families():
    return ['raw_index','balanced_index','balanced_fractional','matched_certified']


def energies():
    return PRIOR.energies()


def weights(memory):
    d=memory+1
    rows=[dict(kind='one',arithmetic='all')]
    rows += [dict(kind='source',i=i,arithmetic='all')for i in range(d)]
    rows += [dict(kind='product',i=i,j=i,arithmetic='all')for i in range(d)]
    rows += [dict(kind='product',i=0,j=i,arithmetic='all')for i in range(1,d)]
    rows += [dict(kind='band',left=l,right=r,arithmetic='all')for l,r in [('1/5','1/4'),('1/10','1/8')]]
    for arithmetic in ('prime','composite'):
        rows += [dict(kind='one',arithmetic=arithmetic),dict(kind='source',i=0,arithmetic=arithmetic),
                 dict(kind='product',i=0,j=0,arithmetic=arithmetic)]
    return rows


def zero_outer_weight(w):
    if w['kind']=='source':return w['i']>0
    if w['kind']=='product':return w['j']>0
    return w['kind']=='band' and Q(w['right'])<=Q(1,5)


def make_program(kernel,energy,family):
    roster=weights(energy['memory']);terms=[]
    definitions=[('1','1','0',roster)]
    if family=='balanced_fractional':
        definitions += [('1/4','3/7','4/7',roster),('1','7/5','-2/5',roster)]
    if family=='matched_certified':
        zero=[w for w in roster if zero_outer_weight(w)]
        definitions += [('2','1','0',zero),('1/3','8/11','3/11',zero)]
    for scale,eta,beta,ws in definitions:
        for mirror in (False,True):
            cut=dict(scale=scale,n_exponent=eta,u_exponent=beta,complement=mirror,unit_balance=family!='raw_index')
            for w in ws:terms.append(dict(cut=deepcopy(cut),weight=deepcopy(w),theta='0'))
    p=dict(schema='coupled-divisor-completion-v1',kernel=deepcopy(kernel),memory=energy['memory'],
           rays=deepcopy(energy['rays']),drift_multiplier=SPEC['drift_multiplier'],
           coupled_terms=terms,gram_weights=['0']*(energy['memory']+1),prime_anchor=SPEC['prime_anchor'])
    SEARCH.parse_program(p)
    return p


def validate_parent():
    counts=PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve082 '+name)
    publication=json.loads((PRIOR.OUT/'publication_integrity.json').read_text())
    for name in publication['postrun_files']:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'postrun_snapshot'/name).read_bytes():
            raise ValueError('preserve082 postrun '+name)
    return counts+[len(PRIOR.FILES),len(publication['postrun_files'])]


def require(result,status):
    if result.get('status')!=status:raise ValueError('independent083 admission '+str(result))
    return result


def discovery_task(task):
    started=time.monotonic();name=task['id'];u=SPEC['calibration_parent'];p=task['program'];row={}
    try:
        eq=None
        if task['family_id']=='matched_certified':
            system=require(OUTER.equality_constraints(p),'OUTER_EQUALITY_SYSTEM')
            independent=require(OUTER_CHECK.equality_constraints(p),'OUTER_EQUALITY_SYSTEM')
            if any(system[k]!=independent[k]for k in ('rows','rhs')):raise ValueError('outer equality derivations disagree')
            eq={k:system[k]for k in ('rows','rhs')}
        row=SEARCH.optimize(p,u,time_limit=SPEC['lp_seconds'],equalities=eq)
        if row['status']=='LP_PROPOSAL':
            row['upper_admission']=require(CHECK.verify_certificate(row['program'],u,row['certificate']),
                                           'VERIFIED_FINITE_COUPLED_UPPER_BOUND')
            row['dual_admission']=require(CHECK.verify_price_dual(row['program'],u,row['dual']),
                                          'VERIFIED_FINITE_COUPLED_PRICE_LOWER_BOUND')
            baseline_model=SEARCH.build_model(p,u);baseline,diag=SEARCH.upper_certificate(baseline_model)
            row['baseline_constructor_operations']=baseline_model['meter'].ops
            row['same_geometry_zero_parameter_baseline']=baseline
            row['baseline_admission']=require(CHECK.verify_certificate(p,u,baseline),'VERIFIED_FINITE_COUPLED_UPPER_BOUND')
            row['price_over_u']=str(Q(row['certificate']['price'])/u)
            row['price_over_u2']=str(Q(row['certificate']['price'])/(u*u))
            row['lower_price_over_u2']=str(Q(row['dual']['lower_bound'])/(u*u))
            if eq is not None:
                proof=require(OUTER.synthesize(row['program']),'PROPOSED_UNIFORM_WHOLE_OUTER_CONTROL')
                row['outer_certificate']=proof['certificate']
                row['outer_admission']=require(OUTER_CHECK.verify_certificate(row['program'],proof['certificate']),
                                               'VERIFIED_UNIFORM_WHOLE_OUTER_CONTROL')
    except Exception as exc:
        row.update(status='RESOURCE_REJECTED'if isinstance(exc,(SEARCH.ResourceLimit,MemoryError))else'TASK_FAILED',
                   error=str(exc),traceback=traceback.format_exc())
    row.update(id=name,source_id=task['source_id'],energy_id=task['energy_id'],family_id=task['family_id'],u=u,
               total_elapsed_seconds=time.monotonic()-started,worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    write(OUT/('search_'+name+'.json'),row)
    return {k:row[k]for k in ('id','source_id','energy_id','family_id','status','worker_peak_rss_kib','total_elapsed_seconds')}


def validation_task(task):
    candidate,us=task;started=time.monotonic();p=candidate['program'];rows=[]
    for u in us:
        try:
            model=SEARCH.build_model(p,u);certificate,diagnostics=SEARCH.upper_certificate(model)
            admission=require(CHECK.verify_certificate(p,u,certificate),'VERIFIED_FINITE_COUPLED_UPPER_BOUND')
            rows.append(dict(u=u,status='VERIFIED',certificate=certificate,admission=admission,diagnostics=diagnostics,
                             price_over_u=str(Q(certificate['price'])/u),price_over_u2=str(Q(certificate['price'])/(u*u)),
                             ops=model['meter'].ops,prospective_peak_bytes=model['meter'].peak_bytes))
        except Exception as exc:
            rows.append(dict(u=u,status='VALIDATION_FAILED',error=str(exc),traceback=traceback.format_exc()))
    report=dict(id=candidate['id'],program=p,rows=rows,elapsed_seconds=time.monotonic()-started,
                worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                new_geometry_parents=True,new_unknown_signed_arithmetic_horizon=False,
                known_unit_and_all_prime_signs_used=True,uniform_full_growth_proved=False,
                uniform_original_source_bound_proved=False,RH_proved=False)
    write(OUT/('validation_'+candidate['id']+'.json'),report)
    return {k:v for k,v in report.items()if k not in ('rows','program')}


_PEAK=0
def stage_check(start,pids):
    global _PEAK
    if time.monotonic()-start>SPEC['module_seconds']:raise TimeoutError('083 authorized stage runtime')
    rss=0
    for pid in pids:
        try:
            with open('/proc/'+str(pid)+'/status')as file:
                rss+=next((int(row.split()[1])*1024 for row in file if row.startswith('VmRSS:')),0)
        except FileNotFoundError:pass
    _PEAK=max(_PEAK,rss)
    if rss>SPEC['max_aggregate_bytes']:raise MemoryError('083 aggregate16GiB budget')


def pool_tasks(fn,tasks,start,label):
    results=[];last=time.monotonic()
    with mp.get_context('spawn').Pool(SPEC['workers'])as pool:
        iterator=pool.imap_unordered(fn,tasks,chunksize=1)
        while len(results)<len(tasks):
            stage_check(start,[os.getpid()]+[p.pid for p in pool._pool])
            try:
                result=iterator.next(timeout=1);results.append(result)
                emit(dict(stage=label,completed=len(results),total=len(tasks),id=result['id'],status=result.get('status','COMPLETE')))
            except mp.TimeoutError:pass
            if time.monotonic()-last>30:
                emit(dict(stage=label,completed=len(results),total=len(tasks),elapsed_seconds=time.monotonic()-start));last=time.monotonic()
    return sorted(results,key=lambda r:r['id'])


def inventory():
    earlier=PRIOR.inventory();known=set(earlier['parents'])
    for u in json.loads((PRIOR.OUT/'validation_draw.json').read_text())['parents']+[SPEC['calibration_parent']]:
        known.update(u//(2**i)for i in range(4))
    known.update([1,2,5,6,7,23,91,131,137,211,401,1231,1777])
    return dict(parents=sorted(known),registered082_and_delays=True,development_geometry_included=True,
                scope='registered prior parents/delays and development; no unknown composite signs queried')


def main():
    started=time.monotonic();counts=validate_parent();stage_check(started,[os.getpid()])
    if OUT.exists():raise FileExistsError('preserve083 attempt directory '+str(OUT))
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name in FILES:
        (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes());stage_check(started,[os.getpid()])
    write(OUT/'protocol.json',dict(**SPEC,families=families(),energies=energies(),source_files=FILES,prior_byte_preserved_files=sum(counts)))
    metadata=json.loads((PRIOR.OUT/'source_metadata.json').read_text());write(OUT/'source_metadata.json',metadata)
    known=inventory();write(OUT/'prior_parent_inventory.json',known);tasks=[]
    for source in SPEC['source_ids']:
        for energy in energies():
            for family in families():
                tasks.append(dict(id=source+'_'+energy['id']+'_'+family,source_id=source,energy_id=energy['id'],family_id=family,
                                  program=make_program(metadata[source]['fixed_kernel'],energy,family)))
    write(OUT/'frozen_task_roster.json',dict(tasks=tasks,all_rosters_frozen_before_discovery=True))
    discovery=pool_tasks(discovery_task,tasks,started,'discovery');selected=[]
    for source in SPEC['source_ids']:
        for family in families():
            rows=[json.loads((OUT/('search_'+t['id']+'.json')).read_text())for t in tasks if t['source_id']==source and t['family_id']==family]
            admitted=[r for r in rows if r['status']=='LP_PROPOSAL']
            if not admitted:continue
            best=min(admitted,key=lambda r:(Q(r['certificate']['price']),r['id']))
            selected.append({k:best[k]for k in ('id','source_id','energy_id','family_id','program','u','certificate','dual','outer_certificate','outer_admission')if k in best})
    write(OUT/'frozen_candidates.json',dict(candidates=selected,selected_before_draw=True,ranking_only_exact_complete_bound=True,
                                          uniform_full_growth_proved=False))
    rng=random.Random(SPEC['seed']);excluded=set(known['parents']);draws=[];us=[]
    for lo,hi in SPEC['validation_bands']:
        accepted=0
        while accepted<SPEC['fresh_parents_per_band']:
            u=rng.randint(lo,hi);ok=u not in excluded
            draws.append(dict(u=u,band=[lo,hi],status='ACCEPTED'if ok else'REJECTED_PREVIOUS_OR_DUPLICATE'))
            if ok:us.append(u);excluded.add(u);accepted+=1
    us.sort();write(OUT/'validation_draw.json',dict(seed=SPEC['seed'],draws=draws,parents=us,drawn_after_formula_freeze=True,
                                                  unknown_composite_signs_used=False,observed_full_source_values_used=False))
    validations=pool_tasks(validation_task,[(c,us)for c in selected],started,'validation')
    for name in FILES:
        if (ROOT/name).read_bytes()!=(OUT/'source_snapshot'/name).read_bytes():raise ValueError('083 changed during frozen run '+name)
    if validate_parent()!=counts:raise ValueError('older provenance changed')
    stage_check(started,[os.getpid()])
    searches=[json.loads((OUT/('search_'+t['id']+'.json')).read_text())for t in tasks]
    checks=[r for r in searches if r['status']=='LP_PROPOSAL']
    validation_data=[json.loads((OUT/('validation_'+r['id']+'.json')).read_text())for r in validations]
    vrows=[row for v in validation_data for row in v['rows']];good=[r for r in vrows if r['status']=='VERIFIED']
    report=dict(status='COMPLETE_COUPLED_CERTIFICATE_SEARCH',tasks=len(tasks),admitted_proposals=len(checks),
                selected_candidates=len(selected),uniform_whole_outer_certificates=sum('outer_admission'in r for r in checks),
                fresh_geometry_parents=us,validation_rows=len(vrows),admitted_validation_rows=len(good),
                independent_discovery_upper_checks=2*len(checks),independent_dual_checks=len(checks),
                discovery=discovery,validation=validations,elapsed_seconds=time.monotonic()-started,
                sampled_aggregate_peak_rss_bytes=_PEAK,
                conservative_process_peak_sum_bytes=1024*(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss+
                    SPEC['workers']*max([r['worker_peak_rss_kib']for r in discovery+validations]+[0])),
                constructor_operations=sum(r.get('ops',0)+r.get('baseline_constructor_operations',0)for r in searches)+sum(r['ops']for r in good),
                independent_discovery_operations=sum(sum(r[k]['ops']for k in ('upper_admission','dual_admission','baseline_admission'))for r in checks),
                independent_validation_operations=sum(r['admission']['ops']for r in good),prior_frozen_files=sum(counts),
                frozen_source_bytes_preserved=True,known_unit_and_all_prime_signs_used=True,
                unknown_composite_signs_used=False,observed_full_source_values_used=False,
                uniform_full_growth_proved=False,uniform_original_source_bound_proved=False,RH_proved=False,hashes_used=False)
    write(OUT/'report.json',report);emit({k:v for k,v in report.items()if k not in ('discovery','validation')})


if __name__=='__main__':main()

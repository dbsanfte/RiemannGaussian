"""Frozen geometry-only complete-drift search, followed by new-scale checks."""
import os
for key in ('OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','OMP_NUM_THREADS'):
    os.environ[key]='1'
import json
import multiprocessing as mp
import random
import resource
import time
from copy import deepcopy
from fractions import Fraction as Q

import mobius_dense_completion_082 as SEARCH
import check_mobius_dense_completion_082 as CHECK
import run_mobius_density_packet_081 as PRIOR
from run_fractional_prime_kernel_051 import write, emit

ROOT=PRIOR.ROOT
OUT=PRIOR.OUT/'dense_completion_followup_001'
FILES=['mobius_dense_completion_082.py','test_mobius_dense_completion_082.py',
       'mobius_dense_completion_search_082_development.json','check_mobius_dense_completion_082.py',
       'test_check_mobius_dense_completion_082.py','mobius_dense_completion_checker_082_development.json',
       'MOBIUS_DENSE_COMPLETION_CHECK_SCOPE_082.txt','MOBIUS_DENSE_CERTIFICATE_SCOPE_082.txt',
       'MOBIUS_DENSE_BOUND_DESIGN_082.txt','MOBIUS_DENSE_COMPLETION_REVIEW_082.txt',
       'MOBIUS_DENSE_RANK_ONE_OBSTRUCTION_082.txt',
       'mobius_dense_completion_protocol_082.txt','run_mobius_dense_completion_082.py']
SPEC=dict(schema='dense-drift-search-protocol-v1', source_ids=['q1_p16','q1_p04'],
          calibration_parent=1024, seed=20261011082,
          validation_bands=[[1536,2047],[3072,4095],[6144,8191]], fresh_parents_per_band=2,
          workers=3,native_threads=1,module_seconds=7200,lp_seconds=120,
          max_aggregate_bytes=16*1024**3,theta_box=['-16','16'],gram_box=['0','16'],
          drift_multiplier='3/2',lp_parameter_rounding_bits=24,
          selection='smallest exact full drift price/u^2 in each source/profile family',
          all_mobius_signs_and_saved_source_values_excluded_from_search=True,
          actual_prime_and_composite_coordinates_retained=True,
          uniform_growth_proved=False,RH_proved=False,hashes_used=False)


def families():
    def profiles(rows):
        return [dict(scale=s,eta=e) for s,e in rows]
    return [
        dict(id='full_radius',profiles=profiles([('1/4','1')])),
        dict(id='source_endpoints',profiles=profiles([('1/4','1'),('1/5','1'),('1/8','1'),('1/10','1')])),
        dict(id='full_fractional',profiles=profiles([('1/4','1'),('1','3/7'),('1','7/11'),('1/2','10/13')])),
        dict(id='cofactor_radii',profiles=profiles([('1/4','1'),('1/12','1'),('1/20','1'),('1/28','1')]))]


def energies():
    return [dict(id='current',memory=1,rays=[]),
            dict(id='two_delay',memory=2,rays=[dict(a=['1','1'],weight='1/4')]),
            dict(id='three_delay',memory=3,rays=[dict(a=['1','1','-1'],weight='1')])]


def make_program(kernel,energy,profiles):
    d=energy['memory']+1
    return dict(schema='dense-divisor-completion-v1',kernel=deepcopy(kernel),
                memory=energy['memory'],rays=deepcopy(energy['rays']),
                drift_multiplier=SPEC['drift_multiplier'],profiles=deepcopy(profiles),
                theta=[['0']*d for _ in profiles],gram_weights=['0']*(d+len(profiles)))


def validate_parent():
    counts=PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve081 '+name)
    publication=json.loads((PRIOR.OUT/'publication_integrity.json').read_text())
    for name in publication['postrun_files']:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'postrun_snapshot'/name).read_bytes():
            raise ValueError('preserve081 postrun '+name)
    return counts+[len(PRIOR.FILES),len(publication['postrun_files'])]


def require(result,status):
    if result.get('status')!=status:
        raise ValueError('independent082 admission '+str(result))
    return result


def discovery_task(task):
    started=time.monotonic()
    name,p=task['id'],task['program'];u=SPEC['calibration_parent']
    row=SEARCH.optimize(p,u,time_limit=SPEC['lp_seconds'])
    if row['status']=='LP_PROPOSAL':
        row['upper_admission']=require(CHECK.verify_certificate(row['program'],u,row['certificate']),
                                       'VERIFIED_FINITE_DENSE_UPPER_BOUND')
        row['dual_admission']=require(CHECK.verify_price_dual(row['program'],u,row['dual']),
                                      'VERIFIED_FINITE_GRAMMAR_PRICE_LOWER_BOUND')
        baseline_model=SEARCH.build_model(p,u)
        baseline=SEARCH.upper_certificate(baseline_model)
        row['baseline_constructor_operations']=baseline_model['meter'].ops
        row['same_geometry_zero_parameter_baseline']=baseline
        row['baseline_admission']=require(CHECK.verify_certificate(p,u,baseline),'VERIFIED_FINITE_DENSE_UPPER_BOUND')
        row['price_over_u']=str(Q(row['certificate']['price'])/u)
        row['price_over_u2']=str(Q(row['certificate']['price'])/(u*u))
        row['lower_price_over_u2']=str(Q(row['dual']['lower_bound'])/(u*u))
    row.update(id=name,source_id=task['source_id'],energy_id=task['energy_id'],family_id=task['family_id'],
               u=u,total_elapsed_seconds=time.monotonic()-started,
               worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    write(OUT/('search_'+name+'.json'),row)
    return {k:row[k] for k in ['id','source_id','energy_id','family_id','status','worker_peak_rss_kib','total_elapsed_seconds']}


def validation_task(task):
    candidate,us=task;started=time.monotonic();p=candidate['program'];rows=[]
    for u in us:
        model=SEARCH.build_model(p,u);certificate=SEARCH.upper_certificate(model)
        admission=require(CHECK.verify_certificate(p,u,certificate),'VERIFIED_FINITE_DENSE_UPPER_BOUND')
        rows.append(dict(u=u,certificate=certificate,admission=admission,
                         price_over_u=str(Q(certificate['price'])/u),
                         price_over_u2=str(Q(certificate['price'])/(u*u)),
                         ops=model['meter'].ops,prospective_peak_bytes=model['meter'].peak_bytes))
    report=dict(id=candidate['id'],program=p,rows=rows,elapsed_seconds=time.monotonic()-started,
                worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                new_geometry_parents=True,new_arithmetic_horizon=False,
                uniform_growth_proved=False,uniform_original_source_bound_proved=False,RH_proved=False)
    write(OUT/('validation_'+candidate['id']+'.json'),report)
    return {k:v for k,v in report.items() if k not in ('rows','program')}


_PEAK=0
def stage_check(start,pids):
    global _PEAK
    if time.monotonic()-start>SPEC['module_seconds']:
        raise TimeoutError('082 authorized stage runtime')
    rss=0
    for pid in pids:
        try:
            with open('/proc/'+str(pid)+'/status') as file:
                rss+=next((int(row.split()[1])*1024 for row in file if row.startswith('VmRSS:')),0)
        except FileNotFoundError:
            pass
    _PEAK=max(_PEAK,rss)
    if rss>SPEC['max_aggregate_bytes']:
        raise MemoryError('082 aggregate16GiB budget')


def pool_tasks(fn,tasks,start,label):
    results=[];last=time.monotonic()
    with mp.get_context('spawn').Pool(SPEC['workers']) as pool:
        iterator=pool.imap_unordered(fn,tasks,chunksize=1)
        while len(results)<len(tasks):
            stage_check(start,[os.getpid()]+[p.pid for p in pool._pool])
            try:
                result=iterator.next(timeout=1);results.append(result)
                emit(dict(stage=label,completed=len(results),total=len(tasks),id=result['id']))
            except mp.TimeoutError:
                pass
            if time.monotonic()-last>30:
                emit(dict(stage=label,completed=len(results),total=len(tasks),elapsed_seconds=time.monotonic()-start))
                last=time.monotonic()
    return sorted(results,key=lambda r:r['id'])


def inventory():
    earlier=PRIOR.parent_inventory();known=set(earlier['parents'])
    parents=json.loads((PRIOR.OUT/'validation_draw.json').read_text())['parents']
    frozen=json.loads((PRIOR.OUT/'frozen_candidates.json').read_text())['candidates']
    for candidate in frozen:
        data=json.loads((PRIOR.OUT/('discovery_checks_'+candidate['id']+'.json')).read_text())
        parents+= [row['u'] for row in data['rows']]
    for u in parents:
        known.update(u//(2**i) for i in range(4))
    known.update([1,7,91,131,137,211,401,1024,1777])
    return dict(parents=sorted(known),registered081_and_delays=True,
                development_geometry_and_source_parents_included=True,
                scope='prior registered parents/delays plus081 and082 development; no new Mobius signs queried')


def main():
    started=time.monotonic();counts=validate_parent()
    stage_check(started,[os.getpid()])
    if OUT.exists():
        raise FileExistsError('preserve082 attempt directory '+str(OUT))
    OUT.mkdir()
    (OUT/'source_snapshot').mkdir()
    for name in FILES:
        (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
        stage_check(started,[os.getpid()])
    write(OUT/'protocol.json',dict(**SPEC,families=families(),energies=energies(),source_files=FILES,
                                  prior_byte_preserved_files=sum(counts)))
    metadata=json.loads((PRIOR.OUT/'source_metadata.json').read_text())
    write(OUT/'source_metadata.json',metadata)
    known=inventory();write(OUT/'prior_parent_inventory.json',known)
    stage_check(started,[os.getpid()])
    tasks=[];obstructions=[]
    for source in SPEC['source_ids']:
        kernel=metadata[source]['fixed_kernel']
        for energy in energies():
            for family in families():
                name=source+'_'+energy['id']+'_'+family['id']
                tasks.append(dict(id=name,source_id=source,energy_id=energy['id'],family_id=family['id'],
                                  program=make_program(kernel,energy,family['profiles'])))
            for profiles in [[dict(scale='1',eta='3/7'),dict(scale='1',eta='7/11')],
                             [dict(scale='3/2',eta='10/13'),dict(scale='2/3',eta='12/17')]]:
                p=make_program(kernel,energy,profiles)
                obstructions.append(dict(source_id=source,energy_id=energy['id'],program=p,
                                         certificate=SEARCH.sublinear_obstruction(p)))
            stage_check(started,[os.getpid()])
    write(OUT/'frozen_task_roster.json',dict(tasks=tasks,sublinear_obstructions=obstructions))
    discovery=pool_tasks(discovery_task,tasks,started,'discovery')
    # Freeze all winners before sampling validation scales. No observedmu or U ranking.
    selected=[]
    for source in SPEC['source_ids']:
        for family in families():
            rows=[json.loads((OUT/('search_'+t['id']+'.json')).read_text()) for t in tasks
                  if t['source_id']==source and t['family_id']==family['id']]
            admitted=[r for r in rows if r['status']=='LP_PROPOSAL']
            if not admitted:
                continue
            best=min(admitted,key=lambda r:(Q(r['certificate']['price']),r['id']))
            selected.append({k:best[k] for k in ('id','source_id','energy_id','family_id','program','u','certificate','dual')})
            stage_check(started,[os.getpid()])
    write(OUT/'frozen_candidates.json',dict(candidates=selected,selected_before_draw=True,
                                          ranking_only_exact_complete_bound=True,uniform_growth_proved=False))
    rng=random.Random(SPEC['seed']);excluded=set(known['parents']);draws=[];us=[]
    for lo,hi in SPEC['validation_bands']:
        accepted=0
        while accepted<SPEC['fresh_parents_per_band']:
            u=rng.randint(lo,hi);ok=u not in excluded
            draws.append(dict(u=u,band=[lo,hi],status='ACCEPTED' if ok else 'REJECTED_PREVIOUS_OR_DUPLICATE'))
            if ok:
                us.append(u);excluded.add(u);accepted+=1
    us.sort()
    stage_check(started,[os.getpid()])
    write(OUT/'validation_draw.json',dict(seed=SPEC['seed'],draws=draws,parents=us,
                                         drawn_after_formula_freeze=True,source_signs_not_used=True))
    validations=pool_tasks(validation_task,[(c,us) for c in selected],started,'validation')
    for name in FILES:
        if (ROOT/name).read_bytes()!=(OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('082 changed during frozen run '+name)
    if validate_parent()!=counts:
        raise ValueError('older provenance changed')
    stage_check(started,[os.getpid()])
    searches=[json.loads((OUT/('search_'+t['id']+'.json')).read_text()) for t in tasks]
    checks=[r for r in searches if r['status']=='LP_PROPOSAL']
    validation_data=[json.loads((OUT/('validation_'+r['id']+'.json')).read_text()) for r in validations]
    report=dict(status='COMPLETE_FINITE_DENSE_CERTIFICATE_SEARCH',tasks=len(tasks),admitted_proposals=len(checks),
                reviewed_analytic_sublinear_obstruction_proposals=len(obstructions),
                independently_admitted_uniform_obstruction_certificates=0,selected_candidates=len(selected),
                fresh_geometry_parents=us,validation_rows=len(selected)*len(us),
                independent_discovery_upper_checks=2*len(checks),independent_dual_checks=len(checks),
                discovery=discovery,validation=validations,elapsed_seconds=time.monotonic()-started,
                sampled_aggregate_peak_rss_bytes=_PEAK,
                conservative_process_peak_sum_bytes=1024*(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss+
                    SPEC['workers']*max([r['worker_peak_rss_kib'] for r in discovery+validations]+[0])),
                constructor_operations=sum(r.get('ops',0)+r.get('baseline_constructor_operations',0) for r in searches)+
                    sum(row['ops'] for v in validation_data for row in v['rows']),
                independent_discovery_operations=sum(sum(r[k]['ops'] for k in ('upper_admission','dual_admission','baseline_admission')) for r in checks),
                independent_validation_operations=sum(row['admission']['ops'] for v in validation_data for row in v['rows']),
                prior_byte_preserved_files=sum(counts),stage_frozen_files=len(FILES),
                signs_or_source_values_used=False,arithmetic_horizon_unchanged=True,
                complete_dense_target=True,uniform_growth_proved=False,uniform_original_source_bound_proved=False,RH_proved=False)
    write(OUT/'next_search_input.json',dict(schema='dense-completion-obstruction-feedback-v1',
        original_obligation='DeltaE(u)<=C*u for every positive integeru, C independentofu; then source/parameter/RH transfer',
        exact_complete_target='E(u)-(3/2)*E(floor(u/2)); both original unfolded kernels, all squarefree coordinates',
        finite_candidates=[dict(id=c['id'],program=c['program']) for c in selected],
        sublinear_obstructions=obstructions,
        missing_uniform_lemma='An independently proved B(u)<=C*u or comparable subpolynomial normalized energy bound; finite LP prices do not establish it.',
        next_language_priority='Arithmetically coupled constraints beyond fixed finite floor moments; discover and certify uniform rank-one price obstructions before widening this same relaxation.',
        reviewed_fixed_roster_obstruction_file='MOBIUS_DENSE_RANK_ONE_OBSTRUCTION_082.txt',
        formal_theorem_prover_checked=False,uniform_growth_proved=False,RH_proved=False))
    stage_check(started,[os.getpid()])
    report.update(elapsed_seconds=time.monotonic()-started,sampled_aggregate_peak_rss_bytes=_PEAK)
    write(OUT/'report.json',report)
    stage_check(started,[os.getpid()])
    emit({k:v for k,v in report.items() if k not in ('discovery','validation')})


if __name__=='__main__':
    main()

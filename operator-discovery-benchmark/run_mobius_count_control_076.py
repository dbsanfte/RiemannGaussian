"""New count-adaptive operator search; all075 failures are known input."""
import os
for _key in ('OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','OMP_NUM_THREADS'):
    os.environ[_key]='1'
import json
import multiprocessing as mp
from fractions import Fraction as Q
import resource
import time

import mobius_count_control_076 as SEARCH
import check_mobius_count_control_076 as CHECK
import check_mobius_prime_moment_075 as SOURCE_CHECK
import run_mobius_prime_moment_075 as PRIOR
import run_mobius_prime_storage_073 as RESOURCES
from run_fractional_prime_kernel_051 import write,emit

ROOT=PRIOR.ROOT
OUT=PRIOR.OUT/'count_control_followup_001'
FILES=['mobius_count_control_076.py','test_mobius_count_control_076.py',
       'test_mobius_count_control_integration_076.py','mobius_count_control_search_076_development.json',
       'check_mobius_count_control_076.py','test_check_mobius_count_control_076.py',
       'mobius_count_control_checker_076_development.json','MOBIUS_COUNT_CONTROL_CHECK_SCOPE_076.txt',
       'MOBIUS_COUNT_CONTROL_REVIEW_076.txt','mobius_count_control_protocol_076.txt',
       'run_mobius_count_control_076.py']
SPEC=dict(source=SEARCH.S.SOURCE_SPEC,q=['1','33/32','129/128'],base_u=4096,precision=20,
    certified_gammas=SEARCH.CERTIFIED_GAMMAS,open_gammas=SEARCH.OPEN_GAMMAS,
    classes=['prime_only','joint'],certified_radii=['1/4','1/2','3/4'],open_radii=['1/2'],
    discovery='all1680 admitted075 learning parents, including every075 saved failure',
    adaptation_k_anchors=[80,112,160,224,320,448,640,896,1280,1792,2560,3584,5120,7168,10240,14336,20480,28672],
    final_k_anchors=[40960,49152,65536],phases=list(range(80)),
    all_new_formulas_frozen_before_interstitial_source=True,adaptation_refits=0,
    final_only_after_both_lemmas_clear_all_known_domains=True,
    max_aggregate_bytes=16*1024**3,module_seconds=7200,work_limit=300_000_000_000,
    workers=3,native_threads_per_worker=1,LP_seconds=120,hashes_used=False,
    uniform_innovation_proved=False,uniform_source_bound_proved=False,RH_proved=False)


def scales(anchors):
    return sorted({80*k-phase for k in anchors for phase in SPEC['phases']})


def validate_parent():
    counts=PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve075 pre-run '+name)
    publication=json.loads((PRIOR.OUT/'publication_integrity.json').read_text())
    for name in publication['postrun_files']:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'postrun_snapshot'/name).read_bytes():
            raise ValueError('preserve075 postrun '+name)
    if publication['selected_program_refutations']!=18 or publication['RH_proved']:
        raise ValueError('preserve075 source/control disposition')
    return counts+[len(PRIOR.FILES),len(publication['postrun_files'])]


def source_phase(phase,parents):
    start=time.monotonic()
    pm,cm=SEARCH.S.Meter(SPEC['work_limit']),SOURCE_CHECK.Meter(SPEC['work_limit'])
    data=SEARCH.S.make_data(SPEC['source'],parents,pm)
    admission=SOURCE_CHECK.verify_data(data,cm)
    result=dict(source_admission=admission,source_spec=data['spec'],scales=parents,
        producer_operations=pm.ops,checker_operations=cm.ops,prospective_bytes=max(pm.peak_bytes,cm.peak_bytes),
        elapsed_seconds=time.monotonic()-start)
    PRIOR.require_admitted_source(data,result)
    write(OUT/(phase+'_data.json'),data)
    write(OUT/(phase+'_source_admission.json'),result)
    emit('count_control_source_admitted',phase=phase,rows=len(parents),elapsed_seconds=result['elapsed_seconds'])
    return result


_DATA=_FEEDBACK=None


def initialize_worker():
    global _DATA,_FEEDBACK
    _DATA=json.loads((OUT/'discovery_data.json').read_text())
    admission=json.loads((OUT/'discovery_source_admission.json').read_text())
    PRIOR.require_admitted_source(_DATA,admission)
    _FEEDBACK=json.loads((OUT/'input_feedback075.json').read_text())


def retain_program(items,program,origin,baseline,checker_meter):
    key=(tuple((a['column'],a['gamma']) for a in program['atoms']),tuple(program['operator']),program['correlation_mode'])
    existing=next((x for x in items if x['_key']==key),None)
    if existing:
        existing['origins'].append(origin)
        return
    admission=CHECK.verify_program(program,_DATA,checker_meter)
    if admission['status']=='INVALID' or not admission['conditional_induction_verified']:
        raise ValueError('independent program admission '+str(admission))
    if program['correlation_mode']=='structural_cauchy' and admission['status']!='VERIFIED_ON_FINITE_DOMAIN':
        raise ArithmeticError('exact structural training program failed '+str(admission))
    items.append(dict(_key=key,program=program,origins=[origin],discovery_admission=admission,
        discovery_eligible=admission['status']=='VERIFIED_ON_FINITE_DOMAIN',
        diagnostics=SEARCH.diagnostics(program,baseline),source_dependency='discovery_source_admission.json'))


def candidate_task(q):
    start=time.monotonic()
    pm,cm=SEARCH.S.Meter(SPEC['work_limit']),CHECK.Meter(SPEC['work_limit'])
    baseline=SEARCH.make_program(_DATA,[],[],q,'structural_cauchy',SPEC['base_u'],SPEC['precision'],pm)
    items=[]
    learned=[]
    for kind in SPEC['classes']:
        for mode,gammas,radii in [('structural_cauchy',SPEC['certified_gammas'],SPEC['certified_radii']),
                                  ('arithmetic_claim',SPEC['open_gammas'],SPEC['open_radii'])]:
            atoms=SEARCH.grammar(SPEC['source'],gammas,kind)
            for radius in radii:
                fit=SEARCH.fit_operator(_DATA,atoms,q,radius,SPEC['base_u'],pm)
                learned.append(dict(kind=kind,mode=mode,**fit))
                if fit['status']!='PROPOSED':
                    continue
                program=SEARCH.make_program(_DATA,fit['atoms'],fit['coefficients'],q,mode,
                                            SPEC['base_u'],SPEC['precision'],pm)
                retain_program(items,program,dict(method='mixed_count_power_LP',kind=kind,mode=mode,radius=radius),baseline,cm)
    imported=SEARCH.select_imported(_DATA,_FEEDBACK,q,SPEC['base_u'],pm)
    for selected in imported['selected']:
        program=SEARCH.make_program(_DATA,selected['atoms'],selected['coefficients'],q,selected['mode'],
                                    SPEC['base_u'],SPEC['precision'],pm)
        retain_program(items,program,dict(method='075_feedback_template',kind=selected['kind'],
            template=selected['id'],selection=selected['selection']),baseline,cm)
    retain_program(items,baseline,dict(method='zero_operator_baseline',kind='baseline'),baseline,cm)
    for index,item in enumerate(items):
        del item['_key']
        item['id']='q'+q.replace('/','_')+'_p'+str(index).zfill(2)
        item['unpaid_leaves']=SEARCH.obligations(item['program'],item['discovery_admission'])
    result=dict(q=q,programs=items,learned_proposals=learned,imported_scores=imported,
        producer_operations=pm.ops,checker_operations=cm.ops,
        prospective_bytes=max(pm.peak_bytes,cm.peak_bytes),elapsed_seconds=time.monotonic()-start,
        worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        uniform_source_bound_proved=False,RH_proved=False)
    file='candidates_'+q.replace('/','_')+'.json'
    write(OUT/file,result)
    return dict(q=q,file=file,programs=len(items),discovery_eligible=sum(p['discovery_eligible'] for p in items),
        lp_proposals=len(learned),imported_operators_scored=imported['library_operators'],
        producer_operations=pm.ops,checker_operations=cm.ops,elapsed_seconds=result['elapsed_seconds'],
        worker_peak_rss_kib=result['worker_peak_rss_kib'])


def evaluation_task(task):
    phase,item=task
    if not item['discovery_eligible']:
        raise ValueError('failed discovery program cannot advance')
    if phase=='final' and item.get('adaptation_status')!='VERIFIED_ON_FINITE_DOMAIN':
        raise ValueError('both known lemmas must pass before fresh final')
    data=json.loads((OUT/(phase+'_data.json')).read_text())
    admitted=json.loads((OUT/(phase+'_source_admission.json')).read_text())
    PRIOR.require_admitted_source(data,admitted)
    start=time.monotonic()
    cm=CHECK.Meter(SPEC['work_limit'])
    evaluation=CHECK.verify_program(item['program'],data,cm,scales=[r['u'] for r in data['rows']])
    if evaluation['status']=='INVALID':
        raise ValueError('invalid frozen formula '+str(evaluation))
    result=dict(id=item['id'],phase=phase,evaluation=evaluation,
        unpaid_leaves=SEARCH.obligations(item['program'],evaluation),source_dependency=phase+'_source_admission.json',
        checker_operations=cm.ops,elapsed_seconds=time.monotonic()-start,
        worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        uniform_source_bound_proved=False,RH_proved=False)
    write(OUT/(phase+'_'+item['id']+'.json'),result)
    return result


def collect(pool,function,tasks,start,event):
    results,peak=[],0
    iterator=pool.imap_unordered(function,tasks,chunksize=1)
    last=time.monotonic()
    while len(results)<len(tasks):
        if time.monotonic()-start>SPEC['module_seconds']:
            raise TimeoutError('076 whole-stage deadline')
        used=RESOURCES.rss([os.getpid()]+[p.pid for p in pool._pool])
        peak=max(peak,used)
        if used>SPEC['max_aggregate_bytes']:
            raise MemoryError('076 aggregate memory')
        try:item=iterator.next(timeout=1)
        except mp.TimeoutError:continue
        results.append(item)
        if len(results)==len(tasks) or time.monotonic()-last>10:
            emit(event,completed=len(results),total=len(tasks));last=time.monotonic()
    return results,peak


def main():
    if OUT.exists():raise FileExistsError('preserve every076 attempt')
    start=time.monotonic();counts=validate_parent()
    frozen={name:(ROOT/name).read_bytes() for name in FILES}
    receipts=[json.loads(b) for name,b in frozen.items() if name.endswith('_development.json')]
    if any(r.get('status')!='PASS' for r in receipts):raise ValueError('all latest development outcomes must pass')
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name,content in frozen.items():
        with (OUT/'source_snapshot'/name).open('xb') as f:f.write(content)
    try:
        write(OUT/'spec.json',dict(spec=SPEC,prior_frozen_counts=counts,new_frozen_files=len(FILES)))
        known=json.loads((PRIOR.OUT/'learning_data.json').read_text())
        known_admission=json.loads((PRIOR.OUT/'learning_source_admission.json').read_text())
        PRIOR.require_admitted_source(known,known_admission)
        if set(r['u'] for r in known['rows'])&set(scales(SPEC['adaptation_k_anchors'])):
            raise ValueError('new interstitial domain overlaps training parents')
        write(OUT/'discovery_data.json',known);write(OUT/'discovery_source_admission.json',known_admission)
        write(OUT/'input_feedback075.json',json.loads((PRIOR.OUT/'postrun_next_search_input.json').read_text()))
        known_bytes=(OUT/'discovery_data.json').read_bytes()
        del known,known_admission
        phases=[]
        with mp.get_context('spawn').Pool(SPEC['workers'],initializer=initialize_worker) as pool:
            candidates,peak1=collect(pool,candidate_task,SPEC['q'],start,'count_control_candidates_frozen')
            candidates.sort(key=lambda r:Q(r['q']))
            fixed={r['file']:(OUT/r['file']).read_bytes() for r in candidates}
            programs=[p for content in fixed.values() for p in json.loads(content)['programs']]
            write(OUT/'candidate_summary.json',dict(candidates=candidates,all_frozen_before_new_parent_values=True))
            eligible=[p for p in programs if p['discovery_eligible']]
            adaptation,final,peak2,peak3=[],[],0,0
            if eligible:
                phases.append(source_phase('adaptation',scales(SPEC['adaptation_k_anchors'])))
                adaptation,peak2=collect(pool,evaluation_task,[('adaptation',p) for p in eligible],start,'count_control_interstitial_checked')
                index={r['id']:r for r in adaptation}
                eligible=[dict(p,adaptation_status=index[p['id']]['evaluation']['status']) for p in eligible
                          if index[p['id']]['evaluation']['status']=='VERIFIED_ON_FINITE_DOMAIN']
            if eligible:
                phases.append(source_phase('final',scales(SPEC['final_k_anchors'])))
                final,peak3=collect(pool,evaluation_task,[('final',p) for p in eligible],start,'count_control_final_checked')
            else:
                write(OUT/'final_skipped.json',dict(reason='No frozen program cleared both prior and interstitial lemmas.',
                      fresh_larger_prefix_queries=0,diagnostic_final_tests_of_refuted_programs=0))
        for name,content in fixed.items():
            if (OUT/name).read_bytes()!=content:raise ValueError('frozen program changed')
        if (OUT/'discovery_data.json').read_bytes()!=known_bytes:raise ValueError('admitted old source changed')
        for name,content in frozen.items():
            if (ROOT/name).read_bytes()!=content:raise ValueError('frozen076 source changed '+name)
        validate_parent()
        by_adapt={r['id']:r for r in adaptation};by_final={r['id']:r for r in final}
        dispositions=[]
        for item in programs:
            verdict=item['discovery_admission'];domain='discovery'
            if item['id'] in by_adapt:verdict=by_adapt[item['id']]['evaluation'];domain='adaptation'
            if item['id'] in by_final:verdict=by_final[item['id']]['evaluation'];domain='final'
            dispositions.append(dict(id=item['id'],q=item['program']['q'],origins=item['origins'],last_domain=domain,
                status=verdict['status'],universal_correlation_proved=verdict['universal_correlation_proved'],
                diagnostics=item['diagnostics'],unpaid_leaves=SEARCH.obligations(item['program'],verdict),
                uniform_source_bound_proved=False))
        parent_peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        child_peak=max(r['worker_peak_rss_kib'] for r in candidates+adaptation+final)
        report=dict(status='COUNT_ADAPTIVE_OPERATOR_SEARCH_COMPLETE_UNIFORM_INNOVATION_OPEN',
            candidates=candidates,dispositions=dispositions,candidate_programs=len(programs),
            interstitial_programs=len(adaptation),fresh_final_programs=len(final),
            finite_survivors=sum(r['status']=='VERIFIED_ON_FINITE_DOMAIN' for r in dispositions),
            finite_refutations=sum(r['status']=='REFUTED' for r in dispositions),
            uniform_correlation_certificates=sum(r['universal_correlation_proved'] for r in dispositions),
            source_phases=phases,elapsed_seconds=time.monotonic()-start,
            producer_operations=sum(r['producer_operations'] for r in candidates+phases),
            checker_operations=sum(r['checker_operations'] for r in candidates+adaptation+final+phases),
            parent_peak_rss_kib=parent_peak,largest_worker_peak_rss_kib=child_peak,
            sampled_parallel_rss_peak_bytes=max(peak1,peak2,peak3),
            conservative_sum_process_peaks_bytes=1024*(parent_peak+SPEC['workers']*child_peak),
            prior_frozen_counts=counts,new_frozen_files=len(FILES),development_receipts=receipts,
            old075_failures_used_for_new_operator_training=True,old_science_replayed=False,
            uniform_innovation_proved=False,uniform_source_bound_proved=False,
            uniform_head_bound_proved=False,uniform_core_bound_proved=False,RH_proved=False,hashes_used=False)
        write(OUT/'report.json',report)
        write(OUT/'next_search_input.json',dict(schema='count-adaptive-innovation-obligations-v1',
            source_spec=SPEC['source'],programs=dispositions,
            all_uniform_arithmetic_obligations_paid=False,
            original_joined_remainder_and_head_transfer_still_unpaid=True,RH_proved=False))
        emit('count_control_complete',elapsed_seconds=report['elapsed_seconds'],
             finite_survivors=report['finite_survivors'],refutations=report['finite_refutations'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json',dict(type=type(exc).__name__,message=str(exc),RH_proved=False))
        raise


if __name__=='__main__':main()

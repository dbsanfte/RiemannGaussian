"""Actual signed auxiliary-energy search, frozen before validation."""
import os
for _key in ('OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','OMP_NUM_THREADS'):os.environ[_key]='1'
import json
import multiprocessing as mp
from fractions import Fraction as Q
from pathlib import Path
import resource
import time

import mobius_rough_energy_078 as SEARCH
import check_mobius_rough_energy_078 as CHECK
import run_mobius_residual_fold_077 as PRIOR
from run_fractional_prime_kernel_051 import write,emit

ROOT=PRIOR.ROOT
OUT=PRIOR.OUT/'rough_energy_followup_001'
FILES=['mobius_rough_energy_078.py','test_mobius_rough_energy_078.py',
       'mobius_rough_energy_search_078_development.json','check_mobius_rough_energy_078.py',
       'test_check_mobius_rough_energy_078.py','mobius_rough_energy_checker_078_development.json',
       'MOBIUS_ROUGH_ENERGY_CHECK_SCOPE_078.txt','MOBIUS_ROUGH_ENERGY_REVIEW_078.txt',
       'mobius_rough_energy_protocol_078.txt','run_mobius_rough_energy_078.py']
SPEC=dict(source_ids=['q1_p16','q1_p04','q1_p00'],
    gammas=SEARCH.rational_grid('1/7','2/3',9),eta_denominator_budget=4,
    q=['1','129/128','33/32'],tau=['1/2','3/4','1'],coefficient_budget=64,
    discovery_k=[128,256,512,1024,2048,4096],base_k=64,
    validation_k=[192,384,768,1536,3072,6144,8192,16384,32768,65536],
    phases=list(range(0,80,5))+[79],workers=3,work_limit=300_000_000_000,
    max_aggregate_bytes=16*1024**3,module_seconds=7200,
    known_arithmetic_horizon=1310720,all_selected_scales_are_known076=True,
    exact_half_children_required=True,complete_energy_base_proved=False,
    uniform_drift_proved=False,RH_proved=False,hashes_used=False)


def parents(anchors):return sorted(80*k-phase for k in anchors for phase in SPEC['phases'])


def validate_parent():
    counts=PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'source_snapshot'/name).read_bytes():raise ValueError('preserve077 '+name)
    pub=json.loads((PRIOR.OUT/'publication_integrity.json').read_text())
    for name in pub['postrun_files']:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'postrun_snapshot'/name).read_bytes():raise ValueError('preserve077 signed feedback '+name)
    return counts+[len(PRIOR.FILES),len(pub['postrun_files'])]


def require(result,status):
    if result.get('status')!=status:raise ValueError('078 independent admission '+str(result))
    return result


_SOURCE=None
_PROGRAMS={}
_SAVED={}
_DISCOVERY={}
_INITIAL_CONSTRUCTOR_OPS=0
_INITIAL_CHECKER_OPS=0


def initialize_source(maximum):
    global _SOURCE,_PROGRAMS,_SAVED,_INITIAL_CONSTRUCTOR_OPS,_INITIAL_CHECKER_OPS
    PRIOR.initialize_worker()
    _SOURCE=SEARCH.Arithmetic(maximum)
    checker_meter=CHECK.Meter()
    CHECK.ensure_horizon(maximum,checker_meter)
    _INITIAL_CONSTRUCTOR_OPS=_SOURCE.meter.ops
    _INITIAL_CHECKER_OPS=checker_meter.ops
    for id in SPEC['source_ids']:
        candidate=json.loads((PRIOR.OUT/('construction_'+id+'.json')).read_text())
        _PROGRAMS[id]=candidate
        detail=json.loads((PRIOR.OUT/('checks_'+id+'.json')).read_text())
        compiled={x['u']:x for phase in ('discovery','validation') for x in detail[phase+'_compilation']}
        for phase in ('discovery','validation'):
            for check in detail[phase+'_checks']:
                _SAVED[id,check['u']]=(compiled[check['u']],check['final_intervals'],check['folds'])


def source_task(task):
    global _INITIAL_CONSTRUCTOR_OPS,_INITIAL_CHECKER_OPS
    u,gammas=task
    meter=SEARCH.F.S.Meter(SPEC['work_limit']);start=time.monotonic()
    meter.charge(_INITIAL_CONSTRUCTOR_OPS);_INITIAL_CONSTRUCTOR_OPS=0
    _SOURCE.meter=meter
    if u not in PRIOR._ROWS:raise ValueError('new half-parent source would exceed declared known rows')
    sources={};checker_ops=_INITIAL_CHECKER_OPS;_INITIAL_CHECKER_OPS=0
    for id in SPEC['source_ids']:
        old=_PROGRAMS[id];program=old['program'];schedule=sorted(old['search']['prime_schedule'])
        if (id,u) in _SAVED:
            compiled,intervals,fold_checks=_SAVED[id,u]
            reused=True
        else:
            compiled=PRIOR.bind(program,u,meter);intervals=compiled['intervals'];fold_checks=[];past=[]
            for p in schedule:
                after=SEARCH.F.fold_intervals(intervals,p,past,meter)
                fold_checks.append(require(PRIOR.CHECK.verify_fold(intervals,after,p,past),'VERIFIED_IDENTITY'))
                intervals=after;past.append(p)
            reused=False
        expected=SEARCH.residual_polynomial(program,PRIOR._ROWS[u])
        if not reused:
            checker_ops+=sum(c['ops'] for c in fold_checks+[compiled['binding'],compiled['stencil_admission']])
        sources[id]=dict(folded_intervals=intervals,compiled=compiled,
            prime_schedule=schedule,fold_admissions=fold_checks,reused_frozen077_compilation=reused,
            expected_residual_polynomial=expected,features={},feature_admissions={})
    # Share each actual prime/factor query across residuals at this parent.
    for gamma in gammas:
        for source in sources.values():
            values=_SOURCE.features(source['folded_intervals'],source['prime_schedule'],gamma)
            expected=source['expected_residual_polynomial']
            if SEARCH.sum_features(values)!=expected:raise ArithmeticError('producer signed recombination mismatch')
            admission=require(CHECK.verify_features(source['folded_intervals'],source['prime_schedule'],gamma,values,expected),'VERIFIED_FEATURES')
            source['features'][gamma]=values;source['feature_admissions'][gamma]=admission;checker_ops+=admission['ops']
    payload=dict(u=u,sources=sources,constructor_operations=meter.ops,checker_operations=checker_ops,
        elapsed_seconds=time.monotonic()-start,worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        new_rough_decomposition_over_known_arithmetic=True,new_source_horizon=False,
        uniform_drift_proved=False,RH_proved=False)
    write(OUT/('source_'+str(u)+'.json'),payload)
    return {k:v for k,v in payload.items() if k!='sources'}


def read_rows(us,id,gamma):
    rows={}
    for u in us:
        payload=json.loads((OUT/('source_'+str(u)+'.json')).read_text())['sources'][id]
        if payload['feature_admissions'][gamma]['status']!='VERIFIED_FEATURES':raise ValueError('admitted signed feature required')
        compiled=payload['compiled']
        if compiled['binding']['status']!='VERIFIED_IDENTITY' or compiled['stencil_admission']['status']!='VERIFIED_IDENTITY':raise ValueError('admitted parent token/source binding required')
        rows[u]=dict(u=u,features=payload['features'][gamma],token_intervals=compiled['compiled']['token_intervals'])
    return rows


def initialize_search(us):
    global _DISCOVERY
    _DISCOVERY={id:{} for id in SPEC['source_ids']}
    for u in us:
        payload=json.loads((OUT/('source_'+str(u)+'.json')).read_text())
        for id,source in payload['sources'].items():
            if source['compiled']['binding']['status']!='VERIFIED_IDENTITY' or source['compiled']['stencil_admission']['status']!='VERIFIED_IDENTITY':
                raise ValueError('search requires admitted source/token binding')
            tokens=source['compiled']['compiled']['token_intervals']
            for gamma,features in source['features'].items():
                admission=source['feature_admissions'][gamma]
                if admission['status']!='VERIFIED_FEATURES' or admission['features']!=features:
                    raise ValueError('search requires matching admitted rough features')
                _DISCOVERY[id].setdefault(gamma,{})[u]=dict(u=u,features=features,token_intervals=tokens)


def search_task(task):
    id,gamma=task;start=time.monotonic();meter=SEARCH.F.S.Meter(SPEC['work_limit'])
    train=parents(SPEC['discovery_k']);base=parents([SPEC['base_k']]);rows=_DISCOVERY[id][gamma]
    results=[]
    for q in SPEC['q']:
        for tau in SPEC['tau']:
            proposal=SEARCH.search_energy(rows,train,base,q,tau,coefficient_budget=SPEC['coefficient_budget'],meter=meter)
            results.append(proposal)
    name='proposal_'+id+'_gamma_'+gamma.replace('/','_')+'.json'
    write(OUT/name,dict(id=id,gamma=gamma,proposals=results,elapsed_seconds=time.monotonic()-start,
        worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        constructor_operations=meter.ops,uniform_drift_proved=False,RH_proved=False))
    return dict(id=id,gamma=gamma,file=name,proposals=results,constructor_operations=meter.ops,
        worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def pool_tasks(function,tasks,initializer,initargs,start,label):
    results=[];peak=0;last=time.monotonic()
    with mp.get_context('spawn').Pool(SPEC['workers'],initializer=initializer,initargs=initargs) as pool:
        iterator=pool.imap_unordered(function,tasks,chunksize=1)
        while len(results)<len(tasks):
            if time.monotonic()-start>SPEC['module_seconds']:raise TimeoutError('078 stage runtime')
            used=PRIOR.PRIOR.RESOURCES.rss([os.getpid()]+[p.pid for p in pool._pool]);peak=max(peak,used)
            if used>SPEC['max_aggregate_bytes']:raise MemoryError('078 aggregate memory')
            try:item=iterator.next(timeout=1)
            except mp.TimeoutError:continue
            results.append(item)
            if len(results)==len(tasks) or time.monotonic()-last>15:
                emit(label,completed=len(results),total=len(tasks));last=time.monotonic()
    return results,peak


def checked_energy(program,rows,parent_us,base_us):
    checks=[];base=[]
    for u in parent_us:
        check=CHECK.verify_drift(program,rows[u],rows[u//2],precision=24)
        if check['status'] not in ('CERTIFIED_FINITE','REFUTED_FINITE','UNRESOLVED_INTERVAL'):
            raise ValueError('drift admission '+str(check))
        checks.append(check)
    for u in base_us:
        base.append(require(CHECK.verify_energy(program,rows[u],precision=24),'VERIFIED_ENERGY_ENCLOSURE'))
    return dict(drift_checks=checks,observed_base_checks=base,
        certified=sum(c['status']=='CERTIFIED_FINITE' for c in checks),
        refuted=sum(c['status']=='REFUTED_FINITE' for c in checks),
        unresolved=sum(c['status']=='UNRESOLVED_INTERVAL' for c in checks),
        checker_operations=sum(c['ops'] for c in checks+base),
        complete_base_proved=False,uniform_drift_proved=False)


def main():
    if OUT.exists():raise FileExistsError('preserve every078 attempt')
    start=time.monotonic();counts=validate_parent();frozen={n:(ROOT/n).read_bytes() for n in FILES}
    for n,b in frozen.items():
        if n.endswith('_development.json') and json.loads(b)['status']!='PASS':raise ValueError('development must pass')
    discovery=parents(SPEC['discovery_k']);bases=parents([SPEC['base_k']])
    dus=sorted(set(discovery+bases+[u//2 for u in discovery]))
    validation=parents(SPEC['validation_k']);vus=sorted(set(validation+[u//2 for u in validation]))
    PRIOR.initialize_worker()
    if any(u not in PRIOR._ROWS for u in dus+vus):raise ValueError('all source/half rows must already exist')
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for n,b in frozen.items():
        with (OUT/'source_snapshot'/n).open('xb') as f:f.write(b)
    try:
        write(OUT/'spec.json',dict(spec=SPEC,prior_frozen_counts=counts,new_frozen_files=len(FILES),
            discovery_parents=discovery,observed_bases=bases,validation_parents=validation))
        write(OUT/'source_dependencies.json',dict(old_programs077=[str(PRIOR.OUT/('construction_'+id+'.json')) for id in SPEC['source_ids']],
            independent076_source_admissions=[str(PRIOR.PRIOR.OUT/(p+'_source_admission.json')) for p in ('discovery','adaptation','final')],
            known_source_rows=len(PRIOR._ROWS),new_arithmetic_horizon=False,new_rough_features=True,
            not_fresh_historical_holdout=True,old076_refutations_retained=True))
        data,peak1=pool_tasks(source_task,[(u,SPEC['gammas']) for u in dus],initialize_source,(max(dus)//4,),start,'rough_discovery_source')
        proposals,peak2=pool_tasks(search_task,[(id,gamma) for id in SPEC['source_ids'] for gamma in SPEC['gammas']],initialize_search,(dus,),start,'rough_energy_proposal')
        candidates=[];baseline_candidates=[];checker_ops=0
        for id in SPEC['source_ids']:
            for q in SPEC['q']:
                for tau in SPEC['tau']:
                    options=[dict(p,id=id,gamma=x['gamma'],file=x['file']) for x in proposals if x['id']==id
                             for p in x['proposals'] if p.get('program',{}).get('q')==q and p['program']['tau']==tau]
                    if not options:continue
                    # Prefer a real auxiliary if it improves; zero-ray proposals
                    # remain baselines, never discoveries by nomenclature.
                    best=min(options,key=lambda x:(x['approximate_score'],x['positive_rays'],Q(x['gamma'])))
                    rows=read_rows(dus,id,best['gamma'])
                    program,calibration=SEARCH.calibrate(best['program'],rows,discovery,bases)
                    baseline=dict(schema='rough-energy-program-v1',q=q,tau=tau,rays=[],innovation_C='0')
                    baseline,bcal=SEARCH.calibrate(baseline,rows,discovery,bases)
                    key=id+'_q'+q.replace('/','_')+'_tau'+tau.replace('/','_')
                    candidate=dict(id=key,source_id=id,gamma=best['gamma'],program=program,
                        calibration=calibration,baseline_program=baseline,baseline_calibration=bcal,
                        exact_discovery_score_ratio=str(Q(calibration['discovery_score'])/Q(bcal['discovery_score'])) if Q(bcal['discovery_score']) else None,
                        selected_proposal=best['file'],positive_auxiliary_rays=len(program['rays']),
                        frozen_before_validation=True,complete_energy_base_proved=False,
                        uniform_drift_proved=False,uniform_source_bound_proved=False,RH_proved=False)
                    write(OUT/('candidate_'+key+'.json'),candidate)
                    fixed=(OUT/('candidate_'+key+'.json')).read_bytes()
                    admitted=checked_energy(program,rows,discovery,bases)
                    bcheck=checked_energy(baseline,rows,discovery,bases)
                    if admitted['refuted'] or admitted['unresolved'] or bcheck['refuted'] or bcheck['unresolved']:
                        raise ArithmeticError('rounded discovery calibration failed exact check')
                    checker_ops+=admitted['checker_operations']+bcheck['checker_operations']
                    write(OUT/('discovery_checks_'+key+'.json'),dict(candidate=admitted,baseline=bcheck))
                    candidates.append((candidate,fixed))
                    emit('rough_energy_frozen',completed=len(candidates),source=id,q=q,tau=tau,rays=len(program['rays']))
        write(OUT/'frozen_candidates.json',dict(candidates=[c for c,_ in candidates],validation_arithmetic_not_started=True))
        needed_gammas=sorted({c['gamma'] for c,_ in candidates},key=Q)
        missing=[u for u in vus if u not in dus]
        vdata,peak3=pool_tasks(source_task,[(u,needed_gammas) for u in missing],initialize_source,(max(vus)//4,),start,'rough_validation_source')
        results=[]
        for c,fixed in candidates:
            rows=read_rows(vus,c['source_id'],c['gamma'])
            checks=checked_energy(c['program'],rows,validation,[])
            baseline=checked_energy(c['baseline_program'],rows,validation,[])
            checker_ops+=checks['checker_operations']+baseline['checker_operations']
            if (OUT/('candidate_'+c['id']+'.json')).read_bytes()!=fixed:raise ValueError('candidate changed after validation')
            write(OUT/('validation_checks_'+c['id']+'.json'),dict(candidate=checks,baseline=baseline))
            witnesses=[dict(u=x['u'],child_u=x['child_u'],lower=x['lower'],upper=x['upper'],C=x['threshold']) for x in checks['drift_checks'] if x['status']=='REFUTED_FINITE']
            result=dict(id=c['id'],source_id=c['source_id'],q=c['program']['q'],tau=c['program']['tau'],gamma=c['gamma'],
                positive_auxiliary_rays=c['positive_auxiliary_rays'],discovery_score_ratio=c['exact_discovery_score_ratio'],
                validation_certified=checks['certified'],validation_refuted=checks['refuted'],validation_unresolved=checks['unresolved'],
                baseline_validation_refuted=baseline['refuted'],refutation_witnesses=witnesses,
                finite_only=True,complete_energy_base_proved=False,uniform_drift_proved=False,RH_proved=False)
            results.append(result)
            emit('rough_energy_validation',completed=len(results),total=len(candidates),refuted=checks['refuted'])
        for n,b in frozen.items():
            if (ROOT/n).read_bytes()!=b:raise ValueError('frozen078 source changed '+n)
        validate_parent()
        all_data=data+vdata
        parent_peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        child_peak=max(x['worker_peak_rss_kib'] for x in all_data+proposals)
        report=dict(status='SIGNED_ROUGH_AUXILIARY_ENERGY_SEARCH_COMPLETE',results=results,
            source_programs=len(SPEC['source_ids']),cutoff_exponents=len(SPEC['gammas']),ray_atoms=len(SEARCH.atom_dictionary()),
            floating_LP_proposals=sum(len(x['proposals']) for x in proposals),frozen_candidates=len(candidates),
            signed_feature_rows=sum(len(SPEC['source_ids'])*len(SPEC['gammas']) for _ in data)+sum(len(SPEC['source_ids'])*len(needed_gammas) for _ in vdata),
            discovery_parent_count=len(discovery),validation_parent_count=len(validation),
            new_rough_source_parent_count=len(all_data),new_arithmetic_horizon=False,
            constructor_operations=sum(x['constructor_operations'] for x in all_data+proposals),
            checker_operations=sum(x['checker_operations'] for x in all_data)+checker_ops,
            elapsed_seconds=time.monotonic()-start,sampled_parallel_rss_peak_bytes=max(peak1,peak2,peak3),
            conservative_sum_process_peaks_bytes=1024*(parent_peak+SPEC['workers']*child_peak),
            prior_frozen_counts=counts,new_frozen_files=len(FILES),hashes_used=False,
            complete_energy_base_proved=False,uniform_drift_proved=False,
            uniform_residual_bound_proved=False,uniform_source_bound_proved=False,
            uniform_head_bound_proved=False,uniform_core_bound_proved=False,RH_proved=False)
        write(OUT/'report.json',report)
        write(OUT/'next_search_input.json',dict(schema='rough-energy-drift-obligations-v1',candidates=results,
            failed_finite_drift_formulas_are_refuted_not_arithmetic_operators=True,
            obligations=['complete residual-energy base at all integers below recurrence start',
                'all-integer signed quadratic drift including inherited parent token changes and rough-cutoff boundary flux',
                'original source correlation and full head/core/RH transfer'],
            ranking_priority=['smaller proved growth exponent','uniform recurrence or paid arithmetic reduction','finite numerical score'],
            uniform_drift_proved=False,RH_proved=False))
        emit('rough_energy_complete',candidates=len(results),elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json',dict(type=type(exc).__name__,message=str(exc),RH_proved=False));raise


if __name__=='__main__':main()

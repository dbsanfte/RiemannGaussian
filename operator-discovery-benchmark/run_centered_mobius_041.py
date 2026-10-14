"""Frozen signed-covariance discovery and independent parallel finite replay."""
from copy import deepcopy
import json
import multiprocessing as mp
from pathlib import Path
import random
import resource
import time

import centered_mobius_backend_041 as BACKEND
import centered_mobius_search_041 as SEARCH
import check_centered_mobius_arguments_041 as ARGUMENT
import centered_mobius_interval_041 as INTERVAL
import check_periodic_normalization_040 as PARENT_CHECK


ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'periodic-normalization-results/pilot-001'
OUT=ROOT/'centered-mobius-bound-results/recovery-001'
FAILED=ROOT/'centered-mobius-bound-results/pilot-001'
RECEIPTS=['centered_mobius_backend_041_development.json','centered_mobius_search_041_development.json',
          'check_centered_mobius_arguments_041_development.json','centered_mobius_interval_041_development.json',
          'centered_mobius_runner_041_development.json']
FILES=['centered_mobius_backend_041.py','centered_mobius_search_041.py',
       'check_centered_mobius_arguments_041.py','centered_mobius_interval_041.py',
       'run_centered_mobius_041.py','centered_mobius_protocol_041.txt',
       'test_centered_mobius_backend_041.py','test_centered_mobius_search_041.py',
       'test_check_centered_mobius_arguments_041.py','test_centered_mobius_interval_041.py',
       'test_centered_mobius_runner_041.py','CENTERED_MOBIUS_BACKEND_041.txt',
       'CENTERED_MOBIUS_ARGUMENT_SCOPE_041.txt','CENTERED_MOBIUS_INTERVAL_041.txt']+RECEIPTS
_AUDIT_STATE=None


def read(path):return json.loads(path.read_text())


def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('x') as stream:
        json.dump(value,stream,indent=2,sort_keys=True);stream.write('\n')


def emit(event,**fields):print(json.dumps(dict(event=event,**fields)),flush=True)


def _audit_shard(task):
    started=time.monotonic()
    state=dict(_AUDIT_STATE)
    state['meter']=INTERVAL.Meter(cap=1_000_000_000,seconds=1200)
    state['meter'].reserve(state['H'],state['precision'])
    state['_gram_cache']={}
    result=INTERVAL.audit(state,task['programs'],task['scales_by_m'])
    result['worker_resource']=dict(elapsed_seconds=time.monotonic()-started,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    return result


def parallel_audit(state,programs,scales_by_m,workers=2):
    """Partition complete(m,X) windows, never split a signed moment."""
    global _AUDIT_STATE
    if type(workers) is not int or not 1<=workers<=8:raise ValueError('one..eight audit workers')
    multipliers={p['m'] for p in programs}
    windows=[(m,X) for m in sorted(multipliers) for X in scales_by_m[m]]
    if not windows or len(set(windows))!=len(windows):raise ValueError('distinct complete audit windows')
    workers=min(workers,len(windows));buckets=[[] for _ in range(workers)];costs=[0]*workers
    for window in sorted(windows,key=lambda w:(-w[0]*w[1],w)):
        i=min(range(workers),key=lambda j:(costs[j],j));buckets[i].append(window);costs[i]+=window[0]*window[1]
    reserve=state['meter'].counts()['peak_bytes_estimate']
    if reserve*(workers+1)>15*1024**3:raise MemoryError('aggregate conservative audit memory guard')
    tasks=[]
    for bucket in buckets:
        scales={m:sorted(X for mm,X in bucket if mm==m) for m in sorted({m for m,X in bucket})}
        tasks.append(dict(programs=[p for p in programs if p['m'] in scales],scales_by_m=scales))
    previous=_AUDIT_STATE;_AUDIT_STATE=state
    try:
        if workers==1:parts=[_audit_shard(tasks[0])]
        else:
            with mp.get_context('fork').Pool(workers) as pool:parts=pool.map(_audit_shard,tasks)
    finally:_AUDIT_STATE=previous
    rows=sorted([row for part in parts for row in part['rows']],key=lambda row:(row['id'],row['X']))
    expected={(p['id'],X) for p in programs for X in scales_by_m[p['m']]}
    actual=[(row['id'],row['X']) for row in rows]
    if len(actual)!=len(set(actual)) or set(actual)!=expected:raise ValueError('complete selected-program replay coverage')
    return dict(schema='centered-mobius-parallel-audit-v1',source=parts[0]['source'],
        normalization=state.get('normalization'),programs=programs,scales_by_m=scales_by_m,rows=rows,
        complete_coverage_verified=True,cached_base_grams=sum(p['cached_base_grams'] for p in parts),
        audit_operations=sum(p['counts']['operations'] for p in parts),
        workers=[dict(counts=p['counts'],**p['worker_resource']) for p in parts],
        aggregate_memory_reserve_bytes=reserve*(workers+1),
        finite_evidence_only=True,uniform_signed_bound_proved=False,RH_proved=False)


def final_scales(programs,H,seed=410041):
    rng=random.Random(seed);scales={};irregular={}
    for m in sorted({p['m'] for p in programs}):
        maximum=(H+1)//(2*m)
        if maximum<max(SEARCH.CHECK_SCALES):raise ValueError('complete final child horizon')
        chosen=set()
        while len(chosen)<4:
            X=rng.randrange(65537,maximum+1)
            if X not in SEARCH.CHECK_SCALES:chosen.add(X)
        irregular[m]=sorted(chosen);scales[m]=sorted(set(SEARCH.CHECK_SCALES)|chosen)
    return dict(seed=seed,scales_by_m=scales,irregular_scales_by_m=irregular,
                generated_after_candidate_freeze=True,adaptation_uses_these_values=False)


def main():
    started=time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS,(16*1024**3,resource.getrlimit(resource.RLIMIT_AS)[1]))
    if read(PARENT/'report.json')['status']!='PERIODIC_NORMALIZATION_REDUCTION_VERIFIED_LINEAR_SIGNED_BOUND_OPEN':
        raise ValueError('verified040 reduction required')
    for name in ('check_periodic_normalization_040.py','check_source_pole_guard.py'):
        if (ROOT/name).read_bytes()!=(PARENT/'source_snapshot'/name).read_bytes():
            raise ValueError('changed inherited proof code: '+name)
    parent_search=read(PARENT/'search.json');source=parent_search['source_binding']
    parent_verification=PARENT_CHECK.verify(source,parent_search,read(PARENT/'source_normalization.json'))
    previous=read(PARENT/'next_search_input.json');frontier=read(PARENT/'bound_search_frontier.json')
    r=frontier['new_target']['r'];q=frontier['new_target']['q']
    if r!=parent_search['family']['r'] or q!=parent_search['selected']['q'] or frontier['new_target']['uniform_bound_proved']:
        raise ValueError('exact original OPEN centered-Mobius endpoint')
    OUT.mkdir(parents=True,exist_ok=False)
    try:
        for name in FILES:
            path=OUT/'source_snapshot'/name;path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes((ROOT/name).read_bytes())
        for name in ('next_search_input.json','bound_search_frontier.json','source_normalization.json'):
            (OUT/'source_snapshot'/('parent040_'+name)).write_bytes((PARENT/name).read_bytes())
        training_H=2*max(SEARCH.MULTIPLIERS)*max(SEARCH.TRAIN_SCALES)-1
        spec=dict(schema='centered-mobius-run-spec-v1',r=r,q=q,grammar=SEARCH.dictionary(r),
            training_scales=list(SEARCH.TRAIN_SCALES),training_horizon=training_H,
            final_horizon=SEARCH.HORIZON,check_scales=list(SEARCH.CHECK_SCALES),irregular_seed=410041,
            irregular_per_multiplier=4,precision=192,audit_workers=2,memory_gib=16,
            selection_needs_no_model_calls=True,no_preselected_winner=True,constants_fitted=False,
            previous_attempt=dict(path=str(FAILED.relative_to(ROOT)),failure=read(FAILED/'failure.json'),
                phase='analytic normalization before source coefficients or training observations',
                correction='extract exact fmpz from the Arb integer ceiling',
                grammar_or_selection_changed=False))
        write(OUT/'run_spec.json',spec)
        emit('protocol_frozen',training_horizon=training_H,final_horizon=SEARCH.HORIZON,
             canonical_programs=spec['grammar']['canonical_program_count'])
        float_meter=BACKEND.Meter(cap=500_000_000,seconds=600)
        float_state=BACKEND.build_state(training_H,r,q,meter=float_meter)
        normalization=float_state['normalization'];coefficient_certificate=float_state['certificate']
        training=SEARCH.training_evidence(float_state)
        write(OUT/'training_evidence.json',training)
        search=SEARCH.search(training,r,q)
        write(OUT/'search.json',search)
        write(OUT/'selected_programs.json',search['candidates'])
        emit('candidate_batch_frozen',coverage=search['coverage'],candidates=search['candidates'])
        del float_state
        manifest=final_scales(search['candidates'],SEARCH.HORIZON)
        write(OUT/'evaluation_scales.json',manifest)
        argument_meter=ARGUMENT.Meter()
        proofs=[ARGUMENT.verify_program(p,r,q,normalization['absolute_ceiling'],coefficient_certificate,argument_meter)
                for p in search['candidates']]
        write(OUT/'conditional_verification.json',dict(verified=True,parent040_replayed=parent_verification['verified'],
            coefficient_normalization=normalization,candidates=proofs,operations=argument_meter.operations,
            covariance_proved=False,uniform_target_bound_proved=False,RH_proved=False))
        emit('conditional_arguments_verified',count=len(proofs),uniform_covariance_proved=False)
        interval_meter=INTERVAL.Meter(cap=1_000_000_000,seconds=1200)
        emit('independent_source_started',horizon=SEARCH.HORIZON,precision=192)
        interval_state=INTERVAL.build_state(SEARCH.HORIZON,r,q,precision=192,meter=interval_meter)
        source_counts=interval_meter.counts()
        emit('independent_source_ready',counts=source_counts,audit_workers=2)
        audited=parallel_audit(interval_state,search['candidates'],manifest['scales_by_m'],workers=2)
        write(OUT/'interval_audit.json',audited)
        assessments=[]
        proof_by_id={p['program']['id']:p for p in proofs}
        for program in search['candidates']:
            rows=[row for row in audited['rows'] if row['id']==program['id']]
            failed=[row['X'] for row in rows if row['status']=='fail']
            unresolved=[row['X'] for row in rows if row['status']=='unresolved']
            status='REFUTED_ON_OBSERVED_SCALE' if failed else 'FINITE_COMPARISON_UNRESOLVED' if unresolved else 'FINITE_SURVIVOR_UNPROVED'
            proof=proof_by_id[program['id']]
            assessments.append(dict(program=program,status=status,
                role='declared_endpoint_control' if program['id']==search['control'] else 'selected_covariance_hypothesis',
                tested_scales=len(rows),failure_scales=failed,unresolved_scales=unresolved,
                conditional_bound=proof['conditional_energy_bound'],
                endpoint_equivalent=proof['open_covariance']['endpoint_equivalent'],
                genuine_innovation_dissipation=SEARCH.Q(program['delta'])>0,
                generic_norm_rule=proof['proof_attempt']['status'],
                uniform_covariance_bound_proved=False))
        survivors=[a for a in assessments if a['status']=='FINITE_SURVIVOR_UNPROVED']
        obstruction=dict(schema='centered-mobius-covariance-frontier-v1',source_binding=frontier['new_target'],
            complete_source_retained=True,assessments=assessments,
            open_covariances=[dict(program=a['program'],obligation=proof_by_id[a['program']['id']]['open_covariance'])
                              for a in survivors],
            proof_frontiers=[dict(program=p['program'],paid_increment=p['paid_increment'],
                paid_haar_variance=p['paid_boundary'],paid_forcing=p['paid_forcing'],
                dependencies=p['dependency_graph'],arithmetic_identities=p['arithmetic_innovation'],
                generic_rule_rejection=p['proof_attempt']) for p in proofs],
            inherited_original_F_and_040_obligations_retained=True,
            arithmetic_covariance_bounds_proved=0,whole_signed_bound_proved=False,RH_proved=False)
        write(OUT/'bound_search_frontier.json',obstruction)
        continuation=deepcopy(previous)
        continuation['authoritative_parent']=str((PARENT/'next_search_input.json').relative_to(ROOT))
        continuation['centered_mobius_covariance_search']=dict(
            results=str(OUT.relative_to(ROOT)),canonical_hypotheses=search['coverage']['canonical_programs'],
            finite_assessments=assessments,uniform_covariance_bounds_proved=0,
            frontier=str((OUT/'bound_search_frontier.json').relative_to(ROOT)),
            source_endpoint_replaced=False,actual_prime_coefficients_retained=True,
            numerical_evidence_is_not_an_all_scale_premise=True)
        continuation['previous_construction']=continuation['next_construction']
        continuation['next_construction']=dict(id='signed_parent_innovation_covariance',priority=1,status='OPEN',
            input='complete J_q Haar/prime innovation and exact multiplicative divisibility identities',
            candidate_programs=[a['program'] for a in survivors],
            required_output='an all-integer signed covariance certificate, or a complete new auxiliary plus independently priced remainder',
            forbidden_shortcuts=['pay parent and innovation separately by magnitudes',
                                 'use the target or an equivalent endpoint as a paid premise',
                                 'drop the q-prime valuation-one crossing',
                                 'optimize only the already paid Haar variance'],
            frontier=str((OUT/'bound_search_frontier.json').relative_to(ROOT)),
            original_F_obligation_replaced=False)
        write(OUT/'next_search_input.json',continuation)
        report=dict(status='CENTERED_MOBIUS_COVARIANCE_CANDIDATES_AUDITED_UNIFORM_BOUND_OPEN',
            coverage=search['coverage'],assessments=assessments,finite_survivors=len(survivors),
            dissipative_finite_survivors=sum(a['genuine_innovation_dissipation'] for a in survivors),
            conditional_arguments_verified=len(proofs),source_horizon=SEARCH.HORIZON,
            training_horizon=training_H,independent_moment_windows=audited['cached_base_grams'],
            finite_inequalities_checked=len(audited['rows']),no_archived_numerical_source_read=True,
            final_cases_generated_after_selection=True,whole_signed_bound_proved=False,RH_proved=False,
            uniform_covariance_bounds_proved=0,float_source_counts=float_meter.counts(),
            argument_checker_operations=argument_meter.operations,interval_source_counts=source_counts,
            interval_audit_operations=audited['audit_operations'],audit_workers=audited['workers'],
            aggregate_audit_memory_reserve_bytes=audited['aggregate_memory_reserve_bytes'],
            development_receipts={name:read(ROOT/name) for name in RECEIPTS},
            elapsed_seconds=time.monotonic()-started,
            parent_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        for name in FILES:
            if (ROOT/name).read_bytes()!=(OUT/'source_snapshot'/name).read_bytes():
                raise ValueError('frozen041 source changed: '+name)
        write(OUT/'report.json',report)
        emit('completed',status=report['status'],finite_survivors=len(survivors),
             dissipative_survivors=report['dissipative_finite_survivors'],
             assessments=assessments,elapsed_seconds=report['elapsed_seconds'],RH_proved=False)
    except Exception as error:
        write(OUT/'failure.json',dict(type=type(error).__name__,message=str(error),elapsed_seconds=time.monotonic()-started))
        raise


if __name__=='__main__':main()

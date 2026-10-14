"""Frozen interval residual-construction experiment on admitted076 source."""
import os
for _key in ('OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','OMP_NUM_THREADS'):os.environ[_key]='1'
import json
import multiprocessing as mp
from fractions import Fraction as Q
import resource
import time

import mobius_residual_fold_077 as SEARCH
import check_mobius_residual_fold_077 as CHECK
import run_mobius_count_control_076 as PRIOR
from run_fractional_prime_kernel_051 import write,emit

ROOT=PRIOR.ROOT
OUT=PRIOR.OUT/'residual_fold_followup_001'
FILES=['mobius_residual_fold_077.py','test_mobius_residual_fold_077.py',
       'mobius_residual_fold_search_077_development.json','check_mobius_residual_fold_077.py',
       'test_check_mobius_residual_fold_077.py','mobius_residual_fold_checker_077_development.json',
       'MOBIUS_RESIDUAL_FOLD_CHECK_SCOPE_077.txt','MOBIUS_RESIDUAL_FOLD_REVIEW_077.txt',
       'mobius_residual_fold_protocol_077.txt','run_mobius_residual_fold_077.py']
SPEC=dict(primes=[2,3,5,7,11,13],depth=4,width=3,discovery_k=[64,256,1024,4096],
    validation_k=[16384,32768,65536],phases=[0,79],workers=3,
    max_aggregate_bytes=16*1024**3,module_seconds=7200,work_limit=300_000_000_000,
    discovery_and_validation_are_already_observed076_source=True,
    mobius_values_used_for_construction_selection=False,new_mobius_source_queries=0,
    fixed_schedule_uniform_l1_obstruction_is_not_arithmetic_refutation=True,
    uniform_residual_bound_proved=False,RH_proved=False,hashes_used=False)


def parents(anchors):return sorted(80*k-phase for k in anchors for phase in SPEC['phases'])


def validate_parent():
    counts=PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'source_snapshot'/name).read_bytes():raise ValueError('preserve076 '+name)
    pub=json.loads((PRIOR.OUT/'publication_integrity.json').read_text())
    for name in pub['postrun_files']:
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/'postrun_snapshot'/name).read_bytes():raise ValueError('preserve076 feedback '+name)
    return counts+[len(PRIOR.FILES),len(pub['postrun_files'])]


def select_jobs(programs):
    jobs={}
    for item in programs:
        p=item['program']
        key=(p['q'],tuple((a['column'],a['gamma']) for a in p['atoms']),tuple(p['operator']))
        if key not in jobs:jobs[key]=dict(id=item['id'],aliases=[],program=p)
        jobs[key]['aliases'].append(item['id'])
    return list(jobs.values())


_ROWS={}


def initialize_worker():
    global _ROWS
    for phase in ('discovery','adaptation','final'):
        data=json.loads((PRIOR.OUT/(phase+'_data.json')).read_text())
        admission=json.loads((PRIOR.OUT/(phase+'_source_admission.json')).read_text())
        PRIOR.PRIOR.require_admitted_source(data,admission)
        for row in data['rows']:
            if row['u'] in _ROWS and _ROWS[row['u']]!=row:raise ValueError('conflicting admitted source')
            _ROWS[row['u']]=row


def require(result,status):
    if result.get('status')!=status:raise ValueError('independent077 admission '+str(result))
    return result


def bind(program,u,meter):
    if u not in _ROWS:raise ValueError('only admitted known arithmetic may enter construction')
    compiled=SEARCH.compile_row(program,_ROWS[u],meter)
    compiled['binding']=require(CHECK.verify_compiled(program,_ROWS[u],compiled['prime_groups'],compiled['compiled']),'VERIFIED_IDENTITY')
    compiled['stencil_admission']=require(CHECK.verify_stencil(compiled['compiled']['components'],compiled['intervals']),'VERIFIED_IDENTITY')
    return compiled


def evaluate(compiled,schedule,program,meter):
    before=compiled['intervals'];certificates=[];prior=[]
    for p in schedule:
        after=SEARCH.fold_intervals(before,p,prior,meter)
        certificates.append(require(CHECK.verify_fold(before,after,p,prior),'VERIFIED_IDENTITY'))
        before=after;prior.append(p)
    own=SEARCH.bound_intervals(before,compiled['compiled']['token_intervals'],schedule,meter)
    checked=require(CHECK.bound_intervals(before,compiled['compiled']['token_intervals'],schedule),'VERIFIED_BOUND')
    if checked['l1_upper']!=own['upper'] or checked['l1_lower']!=own['lower']:raise ArithmeticError('independent coefficient price disagreement')
    lo,hi=SEARCH.S.B.power_bounds(compiled['u'],Q(program['q']),20)
    C=Q(program['innovation_C'])
    return dict(u=compiled['u'],folds=certificates,bound=checked,final_intervals=before,
        normalized_squared_upper=str(Q(own['upper'])**2/lo),
        normalized_squared_lower=str(Q(own['lower'])**2/hi),
        coefficient_method_exceeds_old_residual_budget=Q(own['lower'])**2>C*hi,
        signed_arithmetic_residual_refuted=False,uniform_residual_proved=False)


def construction_task(job):
    start=time.monotonic();meter=SEARCH.S.Meter(SPEC['work_limit']);p=job['program']
    discovery=[bind(p,u,meter) for u in parents(SPEC['discovery_k'])]
    result=SEARCH.search_schedules(discovery,p['q'],SPEC['primes'],SPEC['depth'],SPEC['width'],meter)
    schedule=result['prime_schedule']
    barrier=SEARCH.uniform_obstruction(SEARCH.KERNEL,2,schedule,p['q'])
    theorem=require(CHECK.verify_bulk_obstruction(SEARCH.KERNEL,2,schedule,barrier),'VERIFIED_UNIFORM_COEFFICIENT_OBSTRUCTION')
    # This candidate's source is exactly the075 G kernel and all literal
    # primes/direct multipliers are>=2, independently bound in bind().
    candidate=dict(id=job['id'],aliases=job['aliases'],program=p,search=result,
        uniform_coefficient_obstruction=barrier,obstruction_admission=theorem,
        kernel_binding=dict(kernel=SEARCH.KERNEL,child_min_divisor=2,source_spec=p['spec']),
        frozen_before_validation=True,uniform_residual_bound_proved=False,RH_proved=False)
    filename='construction_'+job['id']+'.json'
    write(OUT/filename,candidate);fixed=(OUT/filename).read_bytes()
    discovery_checks=[evaluate(row,schedule,p,meter) for row in discovery]
    validation=[bind(p,u,meter) for u in parents(SPEC['validation_k'])]
    validation_checks=[evaluate(row,schedule,p,meter) for row in validation]
    if (OUT/filename).read_bytes()!=fixed:raise ValueError('construction changed after validation')
    source_checks=[c for row in discovery+validation for c in (row['binding'],row['stencil_admission'])]
    bound_checks=[c for row in discovery_checks+validation_checks for c in row['folds']+[row['bound']]]
    detail=dict(id=job['id'],prime_schedule=schedule,discovery_compilation=discovery,
        validation_compilation=validation,discovery_checks=discovery_checks,validation_checks=validation_checks,
        constructor_operations=meter.ops,checker_operations=sum(c['ops'] for c in source_checks+bound_checks+[theorem]),
        prospective_bytes=max([meter.peak_bytes]+[c['peak_bytes'] for c in source_checks+bound_checks+[theorem]]),
        elapsed_seconds=time.monotonic()-start,worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        fixed_prime_l1_method_obstructed=True,signed_candidate_rejected=False,
        original076_disposition_must_be_preserved=True,uniform_residual_bound_proved=False,RH_proved=False)
    write(OUT/('checks_'+job['id']+'.json'),detail)
    return dict(id=job['id'],aliases=job['aliases'],q=p['q'],prime_schedule=schedule,
        discovery_reduction_ratio=str(Q(result['normalized_squared_upper'])/Q(result['initial_normalized_squared_upper'])),
        discovery_normalized_squared_upper=result['normalized_squared_upper'],
        validation_normalized_squared_upper=max((x['normalized_squared_upper'] for x in validation_checks),key=Q),
        rows_with_coefficient_price_exceeding_old_budget=sum(x['coefficient_method_exceeds_old_residual_budget'] for x in discovery_checks+validation_checks),
        rows_checked=len(discovery_checks)+len(validation_checks),
        uniform_coefficient_obstruction=theorem,
        constructor_operations=detail['constructor_operations'],checker_operations=detail['checker_operations'],
        elapsed_seconds=detail['elapsed_seconds'],worker_peak_rss_kib=detail['worker_peak_rss_kib'],
        signed_candidate_rejected=False,uniform_residual_bound_proved=False,RH_proved=False)


def main():
    if OUT.exists():raise FileExistsError('preserve every077 attempt')
    start=time.monotonic();counts=validate_parent();frozen={n:(ROOT/n).read_bytes() for n in FILES}
    for n,b in frozen.items():
        if n.endswith('_development.json') and json.loads(b)['status']!='PASS':raise ValueError('development must pass')
    report076=json.loads((PRIOR.OUT/'report.json').read_text())
    originals=[p for item in report076['candidates'] for p in json.loads((PRIOR.OUT/item['file']).read_text())['programs']]
    jobs=select_jobs(originals)
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for n,b in frozen.items():
        with (OUT/'source_snapshot'/n).open('xb') as f:f.write(b)
    try:
        write(OUT/'spec.json',dict(spec=SPEC,prior_frozen_counts=counts,new_frozen_files=len(FILES)))
        write(OUT/'input_programs076.json',dict(programs=originals,dispositions=report076['dispositions'],jobs=jobs))
        initialize_worker()
        required=parents(SPEC['discovery_k'])+parents(SPEC['validation_k'])
        if any(u not in _ROWS for u in required):raise ValueError('requested parent not already observed')
        write(OUT/'source_dependencies.json',dict(known_total_rows=len(_ROWS),new_mu_queries=0,
            construction_discovery_parents=parents(SPEC['discovery_k']),construction_validation_parents=parents(SPEC['validation_k']),
            independent_source_files=[str(PRIOR.OUT/(phase+'_source_admission.json')) for phase in ('discovery','adaptation','final')],
            arithmetic_is_not_new_historical_holdout=True))
        results=[];peak=0;last=time.monotonic()
        with mp.get_context('spawn').Pool(SPEC['workers'],initializer=initialize_worker) as pool:
            iterator=pool.imap_unordered(construction_task,jobs,chunksize=1)
            while len(results)<len(jobs):
                if time.monotonic()-start>SPEC['module_seconds']:raise TimeoutError('077 whole-stage runtime')
                used=PRIOR.RESOURCES.rss([os.getpid()]+[p.pid for p in pool._pool]);peak=max(peak,used)
                if used>SPEC['max_aggregate_bytes']:raise MemoryError('077 aggregate memory')
                try:item=iterator.next(timeout=1)
                except mp.TimeoutError:continue
                results.append(item)
                if len(results)==len(jobs) or time.monotonic()-last>10:
                    emit('residual_fold_checked',completed=len(results),total=len(jobs));last=time.monotonic()
        results.sort(key=lambda x:x['id'])
        for n,b in frozen.items():
            if (ROOT/n).read_bytes()!=b:raise ValueError('frozen077 source changed '+n)
        validate_parent()
        parent_peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss;child_peak=max(x['worker_peak_rss_kib'] for x in results)
        report=dict(status='INTERVAL_RESIDUAL_CONSTRUCTIONS_VERIFIED_FIXED_PRIME_L1_METHOD_OBSTRUCTED',
            programs076=len(originals),distinct_formula_q_jobs=len(jobs),results=results,
            uniform_coefficient_obstructions=len(results),signed_arithmetic_candidates_rejected_by_this_run=0,
            source_dependencies='source_dependencies.json',new_mu_queries=0,new_final_arithmetic_queries=0,
            constructor_operations=sum(x['constructor_operations'] for x in results),checker_operations=sum(x['checker_operations'] for x in results),
            elapsed_seconds=time.monotonic()-start,sampled_parallel_rss_peak_bytes=peak,
            conservative_sum_process_peaks_bytes=1024*(parent_peak+SPEC['workers']*child_peak),
            prior_frozen_counts=counts,new_frozen_files=len(FILES),hashes_used=False,
            uniform_residual_bound_proved=False,uniform_source_bound_proved=False,
            uniform_head_bound_proved=False,uniform_core_bound_proved=False,RH_proved=False)
        write(OUT/'report.json',report)
        write(OUT/'next_search_input.json',dict(schema='folded-signed-arithmetic-obligations-v1',
            input_programs='input_programs076.json',constructions=results,
            prohibited_inference='a fixed finite prime schedule plus coefficient absolute values supplies the required subquadratic squared growth',
            remaining_target='prove a signed bound for the retained coprime Mobius aggregate, including interaction of prime and composite contributions',
            original076_refutations_and_all_unpaid_leaves_retained=True,
            no_all_scale_signed_candidate_refutation=True,uniform_residual_bound_proved=False,RH_proved=False))
        emit('residual_fold_complete',jobs=len(results),elapsed_seconds=report['elapsed_seconds'],uniform_residual_bound_proved=False)
        return report
    except BaseException as exc:
        write(OUT/'failure.json',dict(type=type(exc).__name__,message=str(exc),RH_proved=False));raise


if __name__=='__main__':main()

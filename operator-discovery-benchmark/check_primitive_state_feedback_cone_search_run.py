"""One bounded independent cached-chart trace and exact endpoint check.
The designated publication024 chart supplies the prior span premise. No tape,
source manifest or hashes are replayed; native search claims remain numerical.
"""
import argparse
import contextvars
import json
import math
import os
from pathlib import Path
import re
import resource
import time
import check_primitive_state_feedback_cone_search as CORE
ROOT=Path(__file__).resolve().parent;BASE='cancellation-arithmetic-results/'
PARENT=BASE+'primitive-state-feedback-affine-002';PUBLICATION=BASE+'publication-024'
CHART=PARENT+'/jobs/chart.json';AFFINE=PARENT+'/jobs/affine.json';REVIEW=PARENT+'/independent_verification.json'
NORMS=BASE+'primitive-state-cone-jacobi-search-001/jobs/norms.json'
CACHE=BASE+'primitive-state-cached-primal-variants-001/jobs/prepare/source-cache.json'
CONSTRAINT=BASE+'publication-023/constraint.json'
SCOPE='primitive_state_feedback_cone_search_resource_scope.txt'
INPUTS=[PUBLICATION+'/report.json',CHART,AFFINE,REVIEW,NORMS,CACHE,CONSTRAINT,SCOPE]
TESTS=['test_primitive_state_feedback_cone_search','test_run_primitive_state_feedback_cone_search','test_check_primitive_state_feedback_cone_search','test_check_primitive_state_feedback_cone_search_run','test_primitive_state_feedback_cone_search_soundness','test_publish_cancellation_primitive_state_feedback_cone_search']
LIMITS=dict(max_work=450000000,preparation_work_reserve=50000000,synthetic_test_work_reserve=20000000,map_setup_operations=25000000,proposal_operations=200000000,endpoint_operations=25000000,independent_operations=150000000,cooperative_seconds=3600,independent_cooperative_seconds=3600,max_coefficient_bits=4096,max_temporary_bits=8193,max_cells=6000000,max_map_bytes=8388608,max_trace_bytes=16777216,max_endpoint_bytes=2097152,max_check_bytes=65536,max_metadata_bytes=65536,max_protocol_bytes=65536,max_source_snapshot_bytes=8388608,max_cache_bytes=33554432,max_chart_bytes=8388608,max_affine_bytes=1048576,max_norm_bytes=2097152,max_constraint_bytes=131072,max_input_bytes=33554432)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=7200,max_jobs=1,max_result_bytes=65536)
CAPS={PUBLICATION+'/report.json':1048576,CHART:8388608,AFFINE:1048576,REVIEW:1048576,NORMS:2097152,CACHE:33554432,CONSTRAINT:131072}
FLAGS=CORE.FLAGS
require=CORE.require

_IO=contextvars.ContextVar('feedback_affine_io',default=None)


def read(path,cap=1048576):
    require(type(cap)is int and 0<cap<=33554432,'bounded mathematical input cap')
    with Path(path).open('rb')as f:data=f.read(cap+1)
    if len(data)>cap:raise OverflowError('mathematical input byte cap')
    io=_IO.get()
    if io is not None:
        io[0]+=2*(len(data)//64+1);io[1]+=len(data)
        if io[0]>10000000:raise OverflowError('independent IO reserve within preparation')
        if time.monotonic()>io[2]:raise TimeoutError('independent input deadline')
    return json.loads(data)


def false_flags(value):
    require(type(value)is dict,'explicit scope object')
    for k in FLAGS:
        if k in value:require(value[k]is False,'no unverified formal/cone/global admission '+k)



def parent():return dict(publication=PUBLICATION,chart=CHART,center=AFFINE,review=REVIEW,old_scales=NORMS,necessary_row=CONSTRAINT,original_source=CACHE)


def verify_protocol(value):
    expected=dict(schema='primitive-state-feedback-cone-search-run-v1',inputs=INPUTS,input_caps=CAPS,limits=LIMITS,parallel=PARALLEL,tests=TESTS,precision=CORE.PRECISION,search=CORE.SEARCH,model=CORE.MODEL,scaling=CORE.SCALING,seed_rule=CORE.SEED,original_rows=5641,original_variables=1957,projected_variables=1224,pivots=780,free_coordinates=444,producer_count=1,worker_independent_checks=0,final_independent_checks=1,centered_map='x_mp=rounded80digit x024+N(D*z); z0=0',exact_endpoint='free=exact x024_free+D*final269bit z; descending augmented backsub; canonical1957 lift',no_hashes=True,no_new_elimination=True,no_full_tape_replay=True,exact_original_and_feedback_equations_required=True,**FLAGS)
    require(value==expected,'fixed cached cone mathematical protocol')


def verify_ledger(value):
    expected=dict(max_work=450000000,allocations=dict(preparation=50000000,map_setup=25000000,proposal=200000000,exact_endpoint=25000000,final_independent=150000000),total_work_reserve=450000000,remaining_work=0,precision='fixed conservative reservations; no unaudited producer refinement',final_independent_stages_reserved=True)
    require(value==expected,'single joint450m allocation including final audit')


def verify_job(d,execution,mapreceipt,proposal,endpoint):
    rows=execution.get('results');require(type(rows)is list and len(rows)==1 and type(rows[0].get('index'))is int and rows[0]['index']==0 and rows[0].get('status')in('available','missing_resource','error'),'single search transport')
    row=rows[0];cost=execution.get('cost',{})
    for k,v in dict(requested_workers=1,workers=1,max_in_flight=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn').items():require(type(cost.get(k))is type(v)and cost[k]==v,'actual resource boundary '+k)
    for k in ('elapsed_seconds','result_bytes','payload_bytes'):require(type(cost.get(k))in(int,float)and math.isfinite(cost[k])and cost[k]>=0,'finite transport cost')
    require(cost['result_bytes']<=69632,'bounded result transport')
    for k,status in [('available','available'),('missing','missing_resource'),('errors','error')]:require(type(cost.get(k))is int and cost[k]==int(row['status']==status),'transport counts')
    if row['status']!='available':require('value'not in row,'failed transport has no accepted value')
    record=read(d/'jobs/search-job.json',65536)if(d/'jobs/search-job.json').exists()else None;progress=read(d/'jobs/progress.json',65536)if(d/'jobs/progress.json').exists()else None
    for v in (record,progress):
        if v is None:continue
        false_flags(v)
        if 'ledger'in v:verify_ledger(v['ledger'])
        else:require(v is record and v.get('status')=='UNKNOWN'and v.get('endpoint_complete')is False,'outer failure never promotes')
        for name,file in v.get('artifacts',{}).items():require(name in ('map','proposal','endpoint')and file==name+'.json'and(d/'jobs'/file).exists(),'saved mathematical artifact')
    if record:
        require(record.get('status')in('endpoint_complete','UNKNOWN')and type(record.get('producer_complete'))is bool and type(record.get('endpoint_complete'))is bool and type(record.get('deadline_exceeded'))is bool,'explicit numerical resource disposition')
        c=record.get('cost');require(type(c)is dict,'worker cost')
        for k in ('elapsed_seconds','cpu_seconds','peak_rss_kib'):require(type(c.get(k))in(int,float)and math.isfinite(c[k])and c[k]>=0,'finite worker cost')
        require(type(c.get('pid'))is int and c['pid']>0 and c.get('observed_threads_at_completion')==1,'one numerical worker thread')
    if progress:require(progress.get('phase')in('map_setup_started','map_setup_complete','feedback_cone_iteration','proposal_complete','proposal_returned','exact_endpoint_started','terminal_endpoint_complete','terminal_UNKNOWN'),'declared lifecycle')
    if row['status']=='available':require(record is not None and row.get('value')==dict(file='jobs/search-job.json',status=record['status'],cost=record['cost'],**FLAGS),'actual terminal transport')
    complete=row['status']=='available'and record is not None and record['status']=='endpoint_complete'and record['producer_complete']is True and record['endpoint_complete']is True and record['deadline_exceeded']is False
    if complete:
        require(record['cost']['elapsed_seconds']<=3600 and record['cost']['peak_rss_kib']<=6*1024**2,'successful worker respects cooperative and memory caps')
        require(all(v is not None and v.get('complete')is True for v in (mapreceipt,proposal,endpoint))and progress is not None and progress.get('phase')=='terminal_endpoint_complete','complete saved endpoint window')
        require(record.get('artifacts')==progress.get('artifacts')==dict(map='map.json',proposal='proposal.json',endpoint='endpoint.json'),'terminal artifact commitment')
        expected=dict(map_setup=mapreceipt['counts'],proposal=proposal['counts'],exact_endpoint=endpoint['counts']);require(record.get('stage_counts')==progress.get('stage_counts')==expected,'all stage diagnostic counts bound')
        require(record.get('stop_reason')==proposal.get('stop_reason'),'actual stopping reason')
    return dict(transport_status=row['status'],worker_status=record.get('status')if record else None,producer_complete=complete,deadline_exceeded=record.get('deadline_exceeded')if record else None,progress_retained=progress is not None)


def _audit(directory,*,time_limit=3600,max_operations=150000000,max_cells=6000000):
    require(type(time_limit)in(int,float)and math.isfinite(time_limit)and 0<time_limit<=3600,'strict final audit deadline')
    for v,cap in ((max_operations,150000000),(max_cells,6000000)):require(type(v)is int and 0<v<=cap,'strict final independent caps')
    d=Path(directory);start=time.monotonic();deadline=start+time_limit;_IO.get()[2]=deadline
    verify_protocol(read(d/'protocol.json',65536));require(read(d/'parent.json',65536)==parent(),'designated immutable mathematical inputs')
    report=read(ROOT/(PUBLICATION+'/report.json'));require(report.get('schema')==24 and report.get('chart_verified')is True and report.get('candidate_equations_verified')is True and report.get('independent_audit_complete')is True and report.get('classification')=='independent'and report.get('coefficient_rank')==780 and report.get('augmented_rank')==780 and report.get('free_count')==444 and report.get('chosen_pivot')==148 and report.get('chart_path')==CHART and report.get('affine_receipt_path')==AFFINE,'actual published024 cached chart and center premise')
    false_flags(report)
    tests=read(d/'tests.json');match=re.search(r'Ran (\d+) tests?',tests.get('stderr',''));require(tests.get('returncode')==0 and match and tests['stderr'].rstrip().endswith('OK'),'joint-reserved synthetic tests')
    require(read(d/'run_started.json',65536)==dict(one_fixed_search=True),'single search')
    artifacts={name:read(d/'jobs'/(name+'.json'),cap)if(d/'jobs'/(name+'.json')).exists()else None for name,cap in [('map',8388608),('proposal',16777216),('endpoint',2097152)]}
    for v in artifacts.values():
        if v is not None:false_flags(v)
    job=verify_job(d,read(d/'execution.json'),*artifacts.values());check=None;failure=None;attempted=False
    if artifacts['map']is not None and artifacts['map'].get('complete')is True:
        attempted=True
        try:
            cache=read(ROOT/CACHE,CAPS[CACHE]);chart=read(ROOT/CHART,CAPS[CHART]);center=read(ROOT/AFFINE,CAPS[AFFINE]);necessary=read(ROOT/CONSTRAINT,CAPS[CONSTRAINT]);norms=read(ROOT/NORMS,CAPS[NORMS]);review=read(ROOT/REVIEW,CAPS[REVIEW])
            check=CORE.verify_search(cache,chart,center,necessary,norms,review,*artifacts.values(),deadline=deadline,max_operations=max_operations,max_cells=max_cells)
        except(OverflowError,TimeoutError,MemoryError)as error:failure=dict(reason=str(error)or type(error).__name__,error_type=type(error).__name__)
    accepted=bool(job['producer_complete']and check and check['endpoint_verified']);result=dict(schema='primitive-state-feedback-cone-search-independent-review-v1',all_passed=failure is None,status='ENDPOINT_CHECKED'if accepted else'UNKNOWN',independent_search_check=check,endpoint_verified=accepted,candidate_equations_verified=accepted,finite_candidate_feasible=check['finite_candidate_feasible']if accepted else None,accepted_iterations=check.get('accepted_iterations',0)if check else 0,stop_reason=check.get('stop_reason')if check else None,initial_block_penalties=check.get('initial_block_penalties')if check else None,final_block_penalties=check.get('final_block_penalties')if check else None,initial_objective=check.get('initial_objective')if check else None,final_objective=check.get('final_objective')if check else None,original_finite_equations=5641,original_variables=1957,rank=780,free_coordinates=444,parent_source_rebuilds=0,full_elimination_replayed=False,objective_preserved=False,gradient_or_merit_certified=False,resource_failure=failure,job=job,tests_passed=int(match.group(1)),independent_check_attempted=attempted,joint_work=dict(max_work=450000000,total_work_reserve=450000000,preparation_reserved=50000000,map_setup_reserved=25000000,proposal_reserved=200000000,exact_endpoint_reserved=25000000,independent_reserved=150000000,independent_operations=check['audit_operations']if check else(None if attempted else 0),independent_io_operations=_IO.get()[0],independent_io_bytes=_IO.get()[1],independent_io_reserve_within_preparation=10000000),elapsed_seconds=time.monotonic()-start,**FLAGS)
    if time.monotonic()>deadline:result.update(all_passed=False,status='UNKNOWN',endpoint_verified=False,candidate_equations_verified=False,finite_candidate_feasible=None,resource_failure=dict(reason='final independent deadline',error_type='TimeoutError'))
    return result

def audit(directory,*,write=False,**kwargs):
    target=Path(directory)/'independent_verification.json'
    if write and target.exists():raise FileExistsError('independent cone review exists')
    old=resource.getrlimit(resource.RLIMIT_AS);cap=6*1024**3;require(old[1]==resource.RLIM_INFINITY or old[1]>=cap,'supported6GiB audit boundary');start=time.monotonic();cpu=time.process_time();token=_IO.set([0,0,float('inf')])
    try:
        resource.setrlimit(resource.RLIMIT_AS,(cap,old[1]))
        try:result=_audit(directory,**kwargs)
        except(OverflowError,TimeoutError,MemoryError)as error:result=dict(schema='primitive-state-feedback-cone-search-independent-review-v1',all_passed=False,status='UNKNOWN',independent_search_check=None,endpoint_verified=False,candidate_equations_verified=False,finite_candidate_feasible=None,resource_failure=dict(reason=str(error)or type(error).__name__,error_type=type(error).__name__),joint_work=dict(max_work=450000000,total_work_reserve=450000000),**FLAGS)
        result['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,pid=os.getpid(),observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),audit_memory_limit_bytes=cap,audit_memory_limit_enforced=True,memory_boundary='restorable soft RLIMIT_AS')
        if time.monotonic()-start>kwargs.get('time_limit',3600):result.update(all_passed=False,status='UNKNOWN',endpoint_verified=False,candidate_equations_verified=False,finite_candidate_feasible=None,resource_failure=dict(reason='final cost deadline',error_type='TimeoutError'))
        if len(CORE.encoded(result))>65536:
            result=dict(schema='primitive-state-feedback-cone-search-independent-review-v1',all_passed=False,status='UNKNOWN',independent_search_check=None,endpoint_verified=False,candidate_equations_verified=False,finite_candidate_feasible=None,resource_failure=dict(reason='bounded independent check output bytes',error_type='OverflowError'),joint_work=dict(max_work=450000000,total_work_reserve=450000000),cost=result['cost'],**FLAGS)
        if write:
            with target.open('xb')as f:f.write(CORE.encoded(result))
        return result
    finally:resource.setrlimit(resource.RLIMIT_AS,old);_IO.reset(token);require(resource.getrlimit(resource.RLIMIT_AS)==old,'restored audit memory boundary')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('directory');p.add_argument('--write',action='store_true');a=p.parse_args();r=audit(a.directory,write=a.write);print(json.dumps({k:r.get(k)for k in('schema','all_passed','status','endpoint_verified','candidate_equations_verified','finite_candidate_feasible','rank','free_coordinates','resource_failure','cost')},sort_keys=True))

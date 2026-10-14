"""Single independent all-row replay of a bounded feedback affine archive.

Actual source/seed/constraint values are checked, without hash or archive sweeps.
The final replay shares the job's fixed450m reservation and6GiB boundary.
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
import check_primitive_state_feedback_affine as CORE

ROOT=Path(__file__).resolve().parent
BASE='cancellation-arithmetic-results/'
CACHE=BASE+'primitive-state-cached-primal-variants-001/jobs/prepare/source-cache.json'
BASIS=BASE+'primitive-state-exact-row-basis-probe-002/jobs/basis.json'
PROJECTION=BASE+'primitive-state-exact-row-basis-probe-002/jobs/projection.json'
SEED=BASE+'primitive-state-balanced-cone-search-001/jobs/endpoint.json'
CONSTRAINT=BASE+'publication-023/constraint.json'
PUBLICATION=BASE+'publication-023'
SCOPE='primitive_state_feedback_affine_resource_scope.txt'
CALIBRATION_PREDECESSOR=BASE+'primitive-state-feedback-affine-001'
INPUTS=[CACHE,BASIS,PROJECTION,SEED,CONSTRAINT,PUBLICATION+'/report.json',SCOPE]
TESTS=['test_primitive_state_feedback_affine','test_run_primitive_state_feedback_affine_v2','test_check_primitive_state_feedback_affine','test_check_primitive_state_feedback_affine_run_v2','test_primitive_state_feedback_affine_soundness_v2','test_publish_cancellation_primitive_state_feedback_affine']
LIMITS=dict(max_work=450000000,preparation_work_reserve=50000000,synthetic_test_work_reserve=20000000,producer_operations=150000000,independent_operations=250000000,cooperative_seconds=3600,independent_cooperative_seconds=3600,max_coefficient_bits=4096,max_temporary_bits=8193,max_cells=6000000,max_chart_bytes=33554432,max_receipt_bytes=8388608,max_metadata_bytes=65536,max_protocol_bytes=65536,max_source_snapshot_bytes=8388608,max_cache_bytes=33554432,max_basis_bytes=16777216,max_projection_bytes=65536,max_seed_bytes=1048576,max_constraint_bytes=131072,max_input_bytes=33554432)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=7200,max_jobs=1,max_result_bytes=65536)
CAPS={CACHE:33554432,BASIS:16777216,PROJECTION:65536,SEED:1048576,CONSTRAINT:131072,PUBLICATION+'/report.json':1048576}
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


def parent():return dict(publication=PUBLICATION,necessary_row=CONSTRAINT,seed_endpoint=SEED,source_cache=CACHE,old_basis=BASIS,old_projection=PROJECTION)


def verify_protocol(value):
    expected=dict(schema='primitive-state-feedback-affine-run-v2',inputs=INPUTS,input_caps=CAPS,limits=LIMITS,parallel=PARALLEL,tests=TESTS,original_rows=5641,original_variables=1957,projected_variables=1224,old_rank=779,old_free=445,source_program=dict(target='mu',q=6,C='32',claim='critical'),feedback_X=7,feedback_prime=65537,fixed_seed='exact publication021 original vector; no coordinate clipping',policy=CORE.POLICY,producer_count=1,worker_independent_replay_count=0,final_independent_replay_count=1,materialization='retained transcript exact normalized rows; no new elimination of the old system',independent_license='complete old transcript and actual column dependencies replayed by final checker',no_hashes=True,no_new_solver=True,no_cone_optimization=True,joint_work=450000000,calibration_predecessor=CALIBRATION_PREDECESSOR,calibration_attempts=2,preparation_reservation_includes_both_calibrations=True,**FLAGS)
    require(value==expected,'fixed exact affine mathematical protocol')


def verify_ledger(value):
    expected=dict(max_work=450000000,allocations=dict(preparation=50000000,producer_affine=150000000,final_independent_affine=250000000),total_work_reserve=450000000,remaining_work=0,precision='fixed conservative allocations; diagnostic counts do not refine reservations',final_independent_stages_reserved=True)
    require(value==expected,'single joint450m fixed allocation')


def verify_job(d,execution,affine,chart):
    rows=execution.get('results');require(type(rows)is list and len(rows)==1 and type(rows[0].get('index'))is int and rows[0]['index']==0 and rows[0].get('status')in('available','missing_resource','error'),'one exact affine producer transport')
    row=rows[0];cost=execution.get('cost',{})
    for k,v in dict(requested_workers=1,workers=1,max_in_flight=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn').items():require(type(cost.get(k))is type(v)and cost[k]==v,'declared resource enforcement '+k)
    for k in('elapsed_seconds','result_bytes','payload_bytes'):require(type(cost.get(k))in(int,float)and math.isfinite(cost[k])and cost[k]>=0,'finite actual transport cost')
    require(cost['result_bytes']<=69632,'bounded transport metadata')
    for k,status in [('available','available'),('missing','missing_resource'),('errors','error')]:require(type(cost.get(k))is int and cost[k]==int(row['status']==status),'complete transport accounting')
    if row['status']!='available':require('value'not in row,'failed transport cannot invent completion')
    record=read(d/'jobs/affine-job.json',65536)if(d/'jobs/affine-job.json').exists()else None;progress=read(d/'jobs/progress.json',65536)if(d/'jobs/progress.json').exists()else None
    def artifacts(v):
        false_flags(v);require(type(v.get('artifacts',{}))is dict,'actual affine artifact references')
        for name,file in v.get('artifacts',{}).items():require(name in('affine','chart')and file==name+'.json'and(d/'jobs'/file).exists(),'saved mathematical artifact')
    if record:
        artifacts(record);require(record.get('status')in('affine_complete','UNKNOWN')and type(record.get('producer_complete'))is bool and type(record.get('chart_available'))is bool and type(record.get('deadline_exceeded'))is bool,'explicit affine completion/resource disposition')
        if 'ledger'in record:verify_ledger(record['ledger'])
        else:require(record['status']=='UNKNOWN'and record['producer_complete']is False,'outer failure cannot license chart')
        c=record.get('cost');require(type(c)is dict,'actual worker cost')
        for k in('elapsed_seconds','cpu_seconds','peak_rss_kib'):require(type(c.get(k))in(int,float)and math.isfinite(c[k])and c[k]>=0,'actual finite worker cost')
        require(type(c.get('pid'))is int and c['pid']>0 and type(c.get('observed_threads_at_completion'))is int and c['observed_threads_at_completion']==1,'one worker process/thread')
    if progress:
        artifacts(progress);verify_ledger(progress['ledger']);require(progress.get('phase')in('affine_started','decoding_source','verifying_dependencies','replaying_retained_rows','reducing_feedback','repairing_seed','checking_endpoint','complete','terminal_affine_complete','terminal_UNKNOWN'),'bounded known affine lifecycle')
        if record and 'ledger'in record:require(progress['ledger']==record['ledger'],'shared conservative reservation')
    if row['status']=='available':require(record is not None and row.get('value')==dict(file='jobs/affine-job.json',status=record['status'],cost=record['cost'],**FLAGS),'actual terminal transport status/cost')
    complete=row['status']=='available'and record is not None and record['status']=='affine_complete'and record['producer_complete']is True and record['deadline_exceeded']is False
    if complete:
        require(affine is not None and affine.get('complete')is True and progress is not None and progress.get('phase')=='terminal_affine_complete'and 'ledger'in record,'complete committed affine result')
        require(record.get('artifacts')==progress.get('artifacts')==dict(affine='affine.json',**(dict(chart='chart.json')if chart is not None else{})),'terminal exact artifact references')
        for k,field in [('classification','classification'),('chart_available','chart_available'),('producer_counts','counts'),('coefficient_rank','coefficient_rank'),('augmented_rank','augmented_rank'),('free_dimension','free_dimension')]:require(record.get(k)==affine.get(field),'actual terminal affine result '+k)
    return dict(transport_status=row['status'],worker_status=record.get('status')if record else None,producer_complete=complete,deadline_exceeded=record.get('deadline_exceeded')if record else None,progress_retained=progress is not None)


def verify_calibration_predecessor():
    prior=ROOT/CALIBRATION_PREDECESSOR
    tests=read(prior/'tests.json',1048576)
    if tests.get('returncode')!=1 or 'FAILED (errors=1)' not in tests.get('stderr',''):
        raise ValueError('retained failed synthetic calibration')
    if (prior/'execution.json').exists() or (prior/'jobs').exists():
        raise ValueError('calibration replacement requires zero prior research executions')


def _audit(directory,*,time_limit=3600,max_operations=250000000,max_live_cells=6000000,max_fill_cells=20000000):
    require(type(time_limit)in(int,float)and math.isfinite(time_limit)and 0<time_limit<=3600,'strict independent deadline')
    for v,cap in [(max_operations,250000000),(max_live_cells,6000000),(max_fill_cells,20000000)]:require(type(v)is int and 0<v<=cap,'strict independent exact replay cap')
    d=Path(directory);start=time.monotonic();deadline=start+time_limit;_IO.get()[2]=deadline
    verify_calibration_predecessor();verify_protocol(read(d/'protocol.json',65536));require(read(d/'parent.json',65536)==parent(),'actual fixed mathematical input locations')
    report=read(ROOT/(PUBLICATION+'/report.json'))
    require(report.get('schema')==23 and report.get('independent_audit_complete')is True and report.get('feedback_constraint_available')is True and report.get('feedback_constraint_file')=='constraint.json'and report.get('scale')==7 and report.get('horizon')==27,'complete independently checked necessary feedback constraint')
    for k in('RH_proved','global_bound_proved','universal_identity_proved','exact_admission'):require(report.get(k)is False,'finite feedback does not prove '+k)
    tests=read(d/'tests.json');match=re.search(r'Ran (\d+) tests?',tests.get('stderr',''));require(tests.get('returncode')==0 and match and tests['stderr'].rstrip().endswith('OK'),'reserved synthetic tests passed')
    require(read(d/'run_started.json',65536)==dict(one_fixed_affine_job=True),'one fixed affine producer')
    affine=read(d/'jobs/affine.json',8388608)if(d/'jobs/affine.json').exists()else None;chart=read(d/'jobs/chart.json',33554432)if(d/'jobs/chart.json').exists()else None
    if chart is not None:false_flags(chart)
    job=verify_job(d,read(d/'execution.json'),affine,chart);check=None;failure=None;attempted=False
    if affine is not None:
        false_flags(affine);require(type(affine.get('complete'))is bool,'explicit affine evidence completion')
        if affine['complete']:
            attempted=True
            try:
                inputs=tuple(read(ROOT/name,CAPS[name])for name in(CACHE,PROJECTION,BASIS,SEED,CONSTRAINT))
                require(len(inputs[0]['original']['monomials'])==5641,'complete original finite5641-equation scope')
                check=CORE.verify_feedback(*inputs,chart,affine,deadline=deadline,max_operations=max_operations,max_live_cells=max_live_cells,max_fill_cells=max_fill_cells)
            except(OverflowError,TimeoutError,MemoryError)as error:failure=dict(reason=str(error)or type(error).__name__,error_type=type(error).__name__)
        else:require(affine.get('status')=='UNKNOWN'and affine.get('chart_available')is False and affine.get('candidate_original_vector')is None and affine.get('diagnostics')is None,'partial evidence licenses no chart/endpoint')
    accepted=job['producer_complete']and check is not None;classification=check['classification']if check else None
    status={'independent':'AFFINE_UPDATED','redundant':'REDUNDANT','inconsistent':'FORMAL_SYSTEM_INCONSISTENT'}[classification]if accepted else'UNKNOWN'
    result=dict(schema='primitive-state-feedback-affine-independent-review-v1',all_passed=True,status=status,classification=classification,independent_affine_check=check,chart_verified=bool(accepted and check['normalized_chart_verified']),candidate_equations_verified=bool(accepted and check['candidate_equations_verified']),finite_candidate_feasible=check['finite_candidate_feasible']if accepted else None,old_rank=check['old_rank']if check else None,new_rank=check['new_rank']if check else None,augmented_rank=check['augmented_rank']if check else None,free_count=check['new_free_count']if accepted else None,resource_failure=failure,job=job,tests_passed=int(match.group(1)),independent_replay_attempted=attempted,joint_work=dict(max_work=450000000,total_work_reserve=450000000,preparation_reserved=50000000,producer_reserved=150000000,independent_reserved=250000000,independent_operations=check['audit_operations']if check else(None if attempted else 0),independent_io_operations=_IO.get()[0],independent_io_bytes=_IO.get()[1],independent_io_reserve_within_preparation=10000000),elapsed_seconds=time.monotonic()-start,**FLAGS)
    if time.monotonic()>deadline:result.update(status='UNKNOWN',chart_verified=False,candidate_equations_verified=False,finite_candidate_feasible=None,resource_failure=dict(reason='final independent deadline',error_type='TimeoutError'))
    return result


def audit(directory,*,write=False,**kwargs):
    target=Path(directory)/'independent_verification.json'
    if write and target.exists():raise FileExistsError('independent affine review exists')
    old=resource.getrlimit(resource.RLIMIT_AS);cap=6*1024**3;require(old[1]==resource.RLIM_INFINITY or old[1]>=cap,'supported6GiB audit boundary');start=time.monotonic();cpu=time.process_time();token=_IO.set([0,0,float('inf')])
    try:
        resource.setrlimit(resource.RLIMIT_AS,(cap,old[1]))
        try:result=_audit(directory,**kwargs)
        except(OverflowError,TimeoutError,MemoryError)as error:result=dict(schema='primitive-state-feedback-affine-independent-review-v1',all_passed=False,status='UNKNOWN',independent_affine_check=None,chart_verified=False,candidate_equations_verified=False,finite_candidate_feasible=None,resource_failure=dict(reason=str(error)or type(error).__name__,error_type=type(error).__name__),joint_work=dict(max_work=450000000,total_work_reserve=450000000),**FLAGS)
        result['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,pid=os.getpid(),observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),audit_memory_limit_bytes=cap,audit_memory_limit_enforced=True,memory_boundary='restorable soft RLIMIT_AS')
        if time.monotonic()-start>kwargs.get('time_limit',3600):result.update(status='UNKNOWN',chart_verified=False,candidate_equations_verified=False,finite_candidate_feasible=None,resource_failure=dict(reason='final cost deadline',error_type='TimeoutError'))
        if write:
            with target.open('x')as f:json.dump(result,f,sort_keys=True,indent=2,allow_nan=False)
        return result
    finally:resource.setrlimit(resource.RLIMIT_AS,old);_IO.reset(token);require(resource.getrlimit(resource.RLIMIT_AS)==old,'restored audit memory boundary')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('directory');p.add_argument('--write',action='store_true');a=p.parse_args();r=audit(a.directory,write=a.write);print(json.dumps({k:r.get(k)for k in('schema','all_passed','status','chart_verified','candidate_equations_verified','finite_candidate_feasible','old_rank','new_rank','free_count','resource_failure','cost')},sort_keys=True))

"""One bounded independent direct scalar replay, sharing the joint450m plan.

No symbolic source construction, cryptographic hash or archive integrity sweep.
Only actual mathematical inputs, complete exact row and modular result are checked.
"""
import argparse
import contextvars
import json
import math
import os
from pathlib import Path
import resource
import time
import re
import check_primitive_state_direct_identity_probe as CORE

ROOT=Path(__file__).resolve().parent
PARENT='cancellation-arithmetic-results/primitive-state-balanced-cone-search-001'
PRIOR='cancellation-arithmetic-results/primitive-state-uniform-identity-probe-001'
PUBLICATION='cancellation-arithmetic-results/publication-022'
FLAGS=CORE.FLAGS
require=CORE.require
TESTS=['test_primitive_state_direct_identity_probe','test_run_primitive_state_direct_identity_probe','test_check_primitive_state_direct_identity_probe','test_check_primitive_state_direct_identity_probe_run','test_primitive_state_direct_identity_probe_soundness','test_publish_cancellation_primitive_state_direct_identity_probe']
LIMITS=dict(max_work=450000000,producer_direct_operations=200000000,independent_direct_operations=200000000,max_overhead_operations=50000000,preparation_work_reserve=50000000,synthetic_test_work_reserve=20000000,cooperative_seconds=3600,independent_cooperative_seconds=3600,max_coefficient_bits=4096,max_temporary_bits=8193,max_cells=6000000,max_receipt_bytes=1048576,max_plan_bytes=262144,max_metadata_bytes=65536,max_protocol_bytes=65536,max_horizon=27,max_source_snapshot_bytes=8388608,max_input_bytes=1048576,metadata_work_reserve=1048576)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=7200,max_jobs=1,max_result_bytes=65536)
_IO=contextvars.ContextVar('direct_probe_io',default=None)

def read(path,cap=1048576):
    with Path(path).open('rb')as f:data=f.read(cap+1)
    require(type(cap)is int and 0<cap<=1048576 and len(data)<=cap,'bounded mathematical JSON read')
    io=_IO.get()
    if io is not None:
        io[0]+=2*(len(data)//64+1);io[1]+=len(data)
        if io[0]>10000000:raise OverflowError('independent IO proxy within preparation')
    return json.loads(data)

def false_flags(value):
    for k in FLAGS:
        if k in value:require(value[k]is False,'no theorem admission '+k)

def verify_protocol(value):
    expected=dict(schema='primitive-state-direct-identity-probe-run-v1',predecessor_publication='cancellation-arithmetic-results/publication-022',predecessor_status='UNKNOWN before any candidate evaluation; symbolic source LINE_EVENTS exhausted',parent=dict(publication='cancellation-arithmetic-results/publication-021',candidate_source=PARENT+'/jobs/endpoint.json',n_variables=1957,one_fixed_candidate=True),program=CORE.PROGRAM,spec=CORE.SPEC,layout=CORE.LAYOUT,source_constructor=CORE.SOURCE_CONSTRUCTOR,domain_policy=CORE.DOMAIN_POLICY,limits=LIMITS,parallel=PARALLEL,tests=TESTS,producer_direct_evaluations=1,final_independent_direct_evaluations=1,worker_independent_direct_evaluations=0,joint450m=True,no_expanded_1957_columns=True,no_new_elimination_or_solver=True,no_actual_arithmetic_sign_assignment=True,exact_rational_feedback_row=True,modular_candidate_test=True,evaluation_metric='all rational operations plus upfront complete domain/weight reserve in one budget',no_symbolic_polynomial_materialization=True,no_python_source_tracing=True,**FLAGS)
    require(value==expected,'fixed complete mathematical direct protocol')


def verify_ledger(value):
    require(value==dict(max_work=450000000,allocations=dict(preparation=50000000,producer_direct_evaluation=200000000,final_independent_direct_evaluation=200000000),total_work_reserve=450000000,remaining_work=0,precision='conservative fixed reserves; no producer count refinement',final_independent_stages_reserved=True),'one joint fixed450m direct allocation')

def verify_job(d,execution,plan,probe):
    rows=execution.get('results');require(type(rows)is list and len(rows)==1 and rows[0].get('index')==0 and rows[0].get('status')in ('available','error','missing_resource'),'one fixed direct producer transport')
    cost=execution.get('cost',{});
    for k,v in dict(requested_workers=1,workers=1,max_in_flight=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn').items():require(type(cost.get(k))is type(v)and cost[k]==v,'declared resource boundary '+k)
    for k in ('elapsed_seconds','result_bytes','payload_bytes'):require(type(cost.get(k))in(int,float)and math.isfinite(cost[k])and cost[k]>=0,'actual transport cost')
    require(cost['result_bytes']<=69632,'bounded transport')
    record=read(d/'jobs/probe-job.json',65536)if(d/'jobs/probe-job.json').exists()else None;progress=read(d/'jobs/progress.json',65536)if(d/'jobs/progress.json').exists()else None
    if record:
        false_flags(record);require(record.get('nonconstant_formal_identity_refuted')is False,'producer cannot claim checked formal refutation')
        if 'ledger'in record:verify_ledger(record['ledger'])
        else:require(record.get('status')=='UNKNOWN'and record.get('producer_complete')is False and record.get('probe_complete')is False,'outer failure cannot claim completion')
        require(record.get('status')in('probe_complete','UNKNOWN')and type(record.get('deadline_exceeded'))is bool,'explicit worker completion')
        for k in ('elapsed_seconds','cpu_seconds','peak_rss_kib'):require(type(record['cost'].get(k))in(int,float)and math.isfinite(record['cost'][k])and record['cost'][k]>=0,'actual worker cost')
        require(type(record['cost'].get('observed_threads_at_completion'))is int and record['cost']['observed_threads_at_completion']==1 and type(record['cost'].get('pid'))is int and record['cost']['pid']>0,'one worker thread/process')
    if progress:
        false_flags(progress);verify_ledger(progress['ledger']);require(progress.get('phase')in('preflight_started','direct_evaluation_started','direct_columns_started','direct_probe_evaluated','probe_returned','terminal_probe_complete','terminal_UNKNOWN'),'known direct lifecycle')
        if record and 'ledger'in record:require(progress['ledger']==record['ledger'],'shared committed reservation')
    available=rows[0]['status']=='available'
    if available:
        require(record is not None and rows[0].get('value')==dict(file='jobs/probe-job.json',status=record['status'],cost=record['cost'],**FLAGS),'actual transport record')
    complete=available and record['status']=='probe_complete'and record['deadline_exceeded']is False
    if complete:
        require('ledger'in record and plan is not None and probe is not None and probe.get('complete')is True and record.get('probe_complete')is True and progress is not None and progress.get('phase')=='terminal_probe_complete','complete committed direct result')
        require(record.get('producer_complete')is True and record.get('producer_status')==probe.get('status'),'committed producer disposition')
        require(record.get('artifacts')==progress.get('artifacts')==dict(plan='plan.json',probe='probe.json'),'committed actual mathematical artifacts')
        require(record.get('nonconstant_difference')==probe.get('nonconstant_difference')and record.get('evaluation_counts')==probe.get('counts'),'terminal direct result counters')
    return dict(transport_status=rows[0]['status'],worker_status=record.get('status')if record else None,producer_complete=complete,deadline_exceeded=record.get('deadline_exceeded')if record else None,progress_retained=progress is not None)

def _audit(directory,*,time_limit=3600,max_operations=200000000,max_cells=6000000):
    require(type(time_limit)in(int,float)and math.isfinite(time_limit)and 0<time_limit<=3600,'strict independent time cap')
    require(type(max_operations)is int and 0<max_operations<=200000000 and type(max_cells)is int and 0<max_cells<=6000000,'strict independent work/cell cap')
    d=Path(directory);start=time.monotonic();deadline=start+time_limit;protocol=read(d/'protocol.json',65536);verify_protocol(protocol);vector=read(d/'candidate.json')
    fixed=read(ROOT/(PRIOR+'/candidate.json'));original=read(ROOT/(PARENT+'/jobs/endpoint.json'));require(vector==fixed==original.get('candidate_original_vector')and original.get('complete')is True,'actual unchanged021 candidate and022 snapshot')
    tests=read(d/'tests.json');match=re.search(r'Ran (\d+) tests?',tests.get('stderr',''));require(tests.get('returncode')==0 and match and tests['stderr'].rstrip().endswith('OK'),'reserved synthetic tests passed')
    require(read(d/'run_started.json',65536)==dict(one_fixed_probe=True),'one fixed direct evaluation')
    plan=read(d/'jobs/plan.json',262144)if(d/'jobs/plan.json').exists()else None;probe=read(d/'jobs/probe.json')if(d/'jobs/probe.json').exists()else None
    job=verify_job(d,read(d/'execution.json'),plan,probe);check=None;failure=None;attempted=False
    if plan is not None:require(plan==CORE.expected_plan(vector,7),'fixedX7 complete actual mathematical plan')
    if probe is not None:
        false_flags(probe);require(plan is not None and type(probe.get('complete'))is bool,'actual complete/partial direct result')
        if probe['complete']:
            attempted=True
            try:check=CORE.verify_probe(vector,plan,probe,deadline=deadline,max_operations=max_operations,max_cells=max_cells)
            except(OverflowError,TimeoutError,MemoryError)as error:failure=dict(reason=str(error)or type(error).__name__,error_type=type(error).__name__)
        else:require(probe.get('status')=='UNKNOWN'and probe.get('feedback_row')is None and probe.get('nonconstant_difference')is None,'incomplete direct result is no row/witness')
    admitted=job['producer_complete']and check is not None;refuted=admitted and check['nonconstant_formal_identity_refuted']
    result=dict(schema='primitive-state-direct-identity-probe-independent-review-v1',all_passed=True,status=check['status']if admitted else'UNKNOWN',nonconstant_formal_identity_refuted=bool(refuted),necessary_formal_identity_constraint=check['necessary_formal_identity_constraint']if admitted else None,independent_probe_check=check,independent_nonzero_diagnostic_retained=check is not None and check['nonconstant_formal_identity_refuted'],resource_failure=failure,candidate_origin='publication-021',tests_passed=int(match.group(1)),job=job,joint_work=dict(max_work=450000000,total_work_reserve=450000000,preparation_reserved=50000000,producer_evaluation_reserved=200000000,independent_evaluation_reserved=200000000,independent_evaluation_operations=check['audit_operations']if check else(None if attempted else 0),independent_io_operations=_IO.get()[0],independent_io_bytes=_IO.get()[1],independent_io_reserve_within_preparation=10000000),independent_evaluation_attempted=attempted,symbolic_source_constructed=False,expanded_1957_columns_built=False,elapsed_seconds=time.monotonic()-start,**FLAGS)
    if time.monotonic()>deadline:result.update(status='UNKNOWN',nonconstant_formal_identity_refuted=False,necessary_formal_identity_constraint=None,resource_failure=dict(reason='final independent deadline',error_type='TimeoutError'))
    return result

def audit(directory,*,write=False,**kwargs):
    target=Path(directory)/'independent_verification.json'
    if write and target.exists():raise FileExistsError('independent review exists')
    token=_IO.set([0,0]);old=resource.getrlimit(resource.RLIMIT_AS);cap=6*1024**3;require(old[1]==resource.RLIM_INFINITY or old[1]>=cap,'supported6GiB boundary');start=time.monotonic();cpu=time.process_time()
    try:
        resource.setrlimit(resource.RLIMIT_AS,(cap,old[1]))
        try:result=_audit(directory,**kwargs)
        except(OverflowError,TimeoutError,MemoryError)as error:result=dict(schema='primitive-state-direct-identity-probe-independent-review-v1',all_passed=False,status='UNKNOWN',nonconstant_formal_identity_refuted=False,necessary_formal_identity_constraint=None,independent_probe_check=None,resource_failure=dict(reason=str(error)or type(error).__name__,error_type=type(error).__name__),joint_work=dict(max_work=450000000,total_work_reserve=450000000),**FLAGS)
        result['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,pid=os.getpid(),observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),audit_memory_limit_bytes=cap,audit_memory_limit_enforced=True,memory_boundary='restorable soft RLIMIT_AS')
        if time.monotonic()-start>kwargs.get('time_limit',3600):result.update(status='UNKNOWN',nonconstant_formal_identity_refuted=False,necessary_formal_identity_constraint=None,resource_failure=dict(reason='final cost deadline',error_type='TimeoutError'))
        if write:
            with target.open('x')as f:json.dump(result,f,sort_keys=True,indent=2,allow_nan=False)
        return result
    finally:
        resource.setrlimit(resource.RLIMIT_AS,old);_IO.reset(token);require(resource.getrlimit(resource.RLIMIT_AS)==old,'restored audit memory boundary')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('directory');p.add_argument('--write',action='store_true');a=p.parse_args();print(json.dumps(audit(a.directory,write=a.write),sort_keys=True,indent=2))

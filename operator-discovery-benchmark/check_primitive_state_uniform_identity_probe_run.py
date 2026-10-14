"""Bounded independent mathematical replay of one fresh formal identity probe.

No new archive/source hashes or integrity sweeps. Actual fixed candidate and
mathematical protocol are compared directly; one complete source is reconstructed
and one exact necessary row is checked under the same450m joint resource plan.
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
import check_primitive_state_uniform_identity_probe as CORE

ROOT=Path(__file__).resolve().parent
PARENT='cancellation-arithmetic-results/primitive-state-balanced-cone-search-001'
PUBLICATION='cancellation-arithmetic-results/publication-021'
TESTS=['test_primitive_state_uniform_identity_probe','test_run_primitive_state_uniform_identity_probe','test_check_primitive_state_uniform_identity_probe','test_check_primitive_state_uniform_identity_probe_run','test_primitive_state_uniform_identity_probe_soundness','test_publish_cancellation_primitive_state_uniform_identity_probe']
LIMITS=dict(max_work=450000000,producer_source_line_events=150000000,independent_source_line_events=150000000,producer_evaluation_operations=50000000,independent_evaluation_operations=50000000,max_overhead_operations=50000000,cooperative_seconds=3600,independent_cooperative_seconds=3600,max_coefficient_bits=4096,max_temporary_bits=8193,max_source_cells=4000000,max_live_cells=6000000,max_polynomial_terms=100000,max_receipt_bytes=1048576,max_plan_bytes=262144,max_metadata_bytes=65536,max_protocol_bytes=65536,max_horizon=27,preparation_work_reserve=50000000,synthetic_test_work_reserve=20000000,max_source_snapshot_bytes=8388608,max_input_bytes=1048576,metadata_work_reserve=1048576)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=7200,max_jobs=1,max_result_bytes=65536)
PROGRAM=dict(target='mu',q=6,C='32',claim='critical')
FLAGS=CORE.FLAGS
require=CORE.require
_IO=contextvars.ContextVar('uniform_identity_probe_io',default=None)


def read(path,cap=1048576):
    path=Path(path);size=path.stat().st_size;require(type(cap)is int and 0<cap<=1048576 and size<=cap,'bounded necessary mathematical JSON input')
    b=_IO.get()
    if b is not None:b.charge(2*(size//64+1),cells=size//64+1)
    with path.open('rb')as f:data=f.read(cap+1)
    require(len(data)<=cap,'bounded complete mathematical input read');return json.loads(data)


def scope(value):
    require(type(value)is dict,'explicit scoped object')
    for k in FLAGS:
        if k in value:require(value[k]is False,'producer cannot admit a formal/scalar/arithmetic theorem '+k)


def fixed_parent():return dict(publication=PUBLICATION,candidate_source=PARENT+'/jobs/endpoint.json',n_variables=1957,one_fixed_candidate=True)


def verify_protocol(value):
    expected=dict(schema='primitive-state-uniform-identity-probe-run-v1',parent=fixed_parent(),program=PROGRAM,spec=CORE.SPEC,layout=CORE.LAYOUT,semantic_keys=['instance','gram_blocks','storage_blocks','gram_specs','gram_program','primitive_state_spec'],native_constructor=CORE.NATIVE_CONSTRUCTOR,limits=LIMITS,parallel=PARALLEL,tests=TESTS,producer_source_builds=1,final_independent_source_builds=1,worker_independent_source_builds=0,joint450m=True,no_expanded_1957_columns=True,no_new_elimination_or_solver=True,no_actual_arithmetic_sign_assignment=True,exact_rational_feedback_row=True,modular_candidate_test=True,source_metric='global Python LINE_EVENTS, not arithmetic operations; every nested reset included',evaluation_metric='bounded rational/evaluation/serialization scalar work proxy',**FLAGS)
    require(value==expected,'fixed actual mathematical probe and complete joint resource declaration')


def verify_execution(execution):
    rows=execution.get('results');cost=execution.get('cost',{});require(type(rows)is list and len(rows)==1 and type(rows[0].get('index'))is int and rows[0]['index']==0 and rows[0].get('status')in ('available','missing_resource','error'),'one declared native producer transport')
    for k,v in dict(requested_workers=1,workers=1,max_in_flight=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn').items():require(type(cost.get(k))is type(v)and cost[k]==v,'enforced producer runtime '+k)
    for k in ('elapsed_seconds','result_bytes','payload_bytes'):require(type(cost.get(k))in (int,float)and math.isfinite(cost[k])and cost[k]>=0,'finite actual transport cost')
    require(cost['result_bytes']<=69632,'bounded transport metadata')
    for k,s in [('available','available'),('missing','missing_resource'),('errors','error')]:require(type(cost.get(k))is int and cost[k]==int(rows[0]['status']==s),'complete transport accounting')
    if rows[0]['status']!='available':require('value'not in rows[0],'failed transport has no invented result')
    return rows[0]


def worker_cost(cost):
    require(type(cost)is dict,'explicit actual producer cost')
    for k in ('elapsed_seconds','cpu_seconds','peak_rss_kib'):require(type(cost.get(k))in (int,float)and math.isfinite(cost[k])and cost[k]>=0,'finite actual cost '+k)
    require(type(cost.get('pid'))is int and cost['pid']>0 and type(cost.get('observed_threads_at_completion'))is int and cost['observed_threads_at_completion']==1,'one-thread source event meter')


def verify_ledger(value):
    expected=dict(preparation=50000000,producer_source=150000000,producer_evaluation=50000000,final_independent_source=150000000,final_independent_evaluation=50000000)
    require(type(value)is dict and value.get('max_work')==450000000 and value.get('allocations')==expected and value.get('total_work_reserve')==450000000 and value.get('remaining_work')==0 and value.get('precision')=='conservative fixed reserves; no producer count refinement' and value.get('final_independent_stages_reserved')is True,'one joint450m fixed source/evaluation/preparation reservation')
    return dict(verified=True,total_work_reserve=450000000,producer_reserved=200000000,independent_reserved=200000000,preparation_reserved=50000000)


def verify_job(directory,row,plan,probe):
    path=directory/'jobs/probe-job.json';record=read(path,65536)if path.exists()else None;progress=read(directory/'jobs/progress.json',65536)if(directory/'jobs/progress.json').exists()else None;ledger=None
    def artifacts(value):
        scope(value);require(type(value.get('artifacts',{}))is dict,'explicit actual mathematical artifact references')
        for name,filename in value.get('artifacts',{}).items():require(name in ('plan','probe')and filename==name+'.json'and(directory/'jobs'/filename).exists(),'saved mathematical artifact exists')
    if row['status']=='available':
        value=row.get('value');require(type(value)is dict and record is not None,'actual available producer record');scope(value)
        require(value.get('file')=='jobs/probe-job.json'and value.get('status')==record.get('status')and value.get('cost')==record.get('cost'),'terminal transport status/cost')
    if record is not None:
        artifacts(record);worker_cost(record.get('cost'));require(record.get('status')in ('probe_complete','UNKNOWN')and type(record.get('deadline_exceeded'))is bool,'explicit native probe completion/deadline');require(record.get('nonconstant_formal_identity_refuted')is False,'producer cannot reject from unverified source')
        if 'parent'in record:require(record['parent']==fixed_parent(),'actual fixed parent context')
        if 'ledger'in record:ledger=verify_ledger(record['ledger'])
    if progress is not None:
        artifacts(progress);verify_ledger(progress['ledger']);require(progress.get('phase')in ('preflight_started','source_build_started','complete_native_source_built','source_build_returned','squares_evaluated','relations_evaluated','probe_evaluated','probe_returned','terminal_probe_complete','terminal_UNKNOWN'),'known source/probe lifecycle')
        if record is not None and 'ledger'in record:require(progress['ledger']==record['ledger'],'unchanged shared conservative ledger')
    available=row['status']=='available'and record is not None and record['status']=='probe_complete'and record['deadline_exceeded']is False
    if available:
        require(plan is not None and probe is not None and probe.get('complete')is True and record.get('probe_complete')is True and ledger is not None and progress is not None and progress.get('phase')=='terminal_probe_complete'and record.get('artifacts')==progress.get('artifacts')and set(record['artifacts'])=={'plan','probe'},'complete committed mathematical inputs/results')
        require(record.get('producer_status')==probe.get('status')and record.get('nonconstant_difference')==probe.get('nonconstant_difference')and record.get('evaluation_counts')==probe.get('counts'),'producer terminal exact/modular result and cost')
        meter=record.get('source_meter');require(type(meter)is dict and meter.get('metric')=='all Python LINE_EVENTS during complete native source call'and type(meter.get('line_events'))is int and 0<=meter['line_events']<=150000000 and meter.get('cap')==150000000 and meter.get('nested_resets_counted')is True and meter.get('one_affine_source_build')is True and meter.get('optional_expanded_hashes')is False,'declared complete aggregate source metric')
    elif record is not None:require(type(record.get('probe_complete'))is bool,'retained completion is explicit; failed transport never promotes')
    return dict(transport_status=row['status'],worker_status=record.get('status')if record else None,producer_complete=available,progress_retained=progress is not None,ledger=ledger,deadline_exceeded=record.get('deadline_exceeded')if record else None)


def _audit(directory,*,time_limit=3600,max_source_line_events=150000000,max_evaluation_operations=50000000,max_overhead_operations=10000000,max_audit_cells=60000000):
    require(type(time_limit)in (int,float)and math.isfinite(time_limit)and 0<time_limit<=3600,'bounded independent deadline')
    for value,cap in [(max_source_line_events,150000000),(max_evaluation_operations,50000000),(max_overhead_operations,10000000),(max_audit_cells,60000000)]:require(type(value)is int and 0<value<=cap,'strict bounded source/evaluation/IO cap')
    d=Path(directory).resolve();started=time.monotonic();deadline=started+time_limit;io=CORE.Budget(deadline,max_overhead_operations,max_audit_cells);token=_IO.set(io)
    try:
        verify_protocol(read(d/'protocol.json',65536));vector=read(d/'candidate.json');published=read(ROOT/(PARENT+'/jobs/endpoint.json'))
        require(published.get('complete')is True and published.get('candidate_original_vector')==vector,'actual fixed complete publication021 candidate coordinates')
        tests=read(d/'tests.json');match=re.search(r'Ran (\d+) tests?',tests.get('stderr',''));require(tests.get('returncode')==0 and match and tests['stderr'].rstrip().endswith('OK'),'jointly reserved synthetic calibration passed')
        require(read(d/'run_started.json',65536)==dict(one_fixed_probe=True),'one fixed native producer startup')
        transport=verify_execution(read(d/'execution.json'));folder=d/'jobs';plan=read(folder/'plan.json',262144)if(folder/'plan.json').exists()else None;probe=read(folder/'probe.json')if(folder/'probe.json').exists()else None
        require(probe is None or plan is not None,'probe requires actual mathematical plan');job=verify_job(d,transport,plan,probe);check=None;source_cost=None;ordinary=0;cells=0;failure=None;source_attempted=False
        if plan is not None:
            preflight=CORE.Budget(deadline,max_evaluation_operations,max_audit_cells);CORE.verify_plan(plan,vector,preflight);require(plan['X']==7 and plan['H']==27,'single fresh scale, no substitute calibration scale');ordinary+=preflight.operations;cells+=preflight.cells
        if probe is not None:
            scope(probe);require(type(probe.get('complete'))is bool,'explicit complete/incomplete source evaluation')
            if probe['complete']:
                source_attempted=True
                try:
                    license=CORE.rebuild_source(plan,vector,deadline=deadline,max_source_line_events=max_source_line_events,max_operations=max_evaluation_operations-ordinary,max_cells=max_audit_cells-cells)
                    ordinary+=license.counts['audit_operations'];cells+=license.counts['audit_cells'];source_cost=license.counts
                    check=CORE.verify_probe(license,vector,plan,probe,deadline=deadline,max_operations=max_evaluation_operations-ordinary-len(CORE.encoded(probe))-1,max_cells=max_audit_cells-cells);ordinary+=check['audit_operations'];cells+=check['audit_cells']
                except (OverflowError,TimeoutError,MemoryError) as error:
                    failure=dict(reason=str(error)or type(error).__name__,error_type=type(error).__name__)

            else:require(probe.get('status')=='UNKNOWN'and probe.get('nonconstant_difference')is None and type(probe.get('reason'))is str,'incomplete source/evaluation has no witness')
        require(io.operations<=10000000 and ordinary<=50000000,'joint source/evaluation/preparation caps');proven=job['producer_complete']and check is not None;refuted=proven and check['nonconstant_formal_identity_refuted'];status=('REFUTED'if refuted else'NOT_REFUTED_BY_THIS_PROBE')if proven else'UNKNOWN'
        joint=dict(max_work=450000000,total_work_reserve=450000000,producer_source_line_event_reserve=150000000,producer_evaluation_reserve=50000000,independent_source_line_event_reserve=150000000,independent_evaluation_reserve=50000000,preparation_reserve=50000000,independent_io_reserve_within_preparation=10000000,independent_source_line_events=source_cost['native_line_events']if source_cost else (None if source_attempted else 0),independent_evaluation_operations=ordinary,independent_io_operations=io.operations)
        result=dict(schema='primitive-state-uniform-identity-probe-independent-review-v1',all_passed=True,status=status,nonconstant_formal_identity_refuted=bool(refuted),necessary_formal_identity_constraint=check['necessary_formal_identity_constraint']if check else None,independent_probe_check=check,independent_resource_failure=failure,independent_nonzero_diagnostic_retained=check is not None and check['nonconstant_formal_identity_refuted'],tests_passed=int(match.group(1)),candidate_origin='publication-021',job=job,joint_work=joint,independent_source_builds=int(source_cost is not None),independent_source_builds_attempted=int(source_attempted),producer_source_builds=1 if job['producer_complete']else None,expanded_1957_columns_built=False,source_metric='Python LINE_EVENTS, not arithmetic operations',audit_operations=ordinary,audit_cells=cells,overhead_operations=io.operations,independent_audit_limits=dict(seconds=time_limit,max_source_line_events=max_source_line_events,max_evaluation_operations=max_evaluation_operations,max_overhead_operations=max_overhead_operations,max_cells=max_audit_cells),elapsed_seconds=time.monotonic()-started,legacy_hashes_scope='none in actual mathematical reconstruction; no source serialization or cryptographic digests',**FLAGS)
        if time.monotonic()>deadline:
            result.update(status='UNKNOWN',nonconstant_formal_identity_refuted=False,necessary_formal_identity_constraint=None,independent_resource_failure=dict(reason='final independent deadline',error_type='TimeoutError'))
        return result
    finally:_IO.reset(token)


def audit(directory,*,write=False,**kwargs):
    target=Path(directory)/'independent_verification.json'
    if write and target.exists():raise FileExistsError('independent verification already exists')
    old=resource.getrlimit(resource.RLIMIT_AS);cap=6*1024**3;require(old[1]==resource.RLIM_INFINITY or old[1]>=cap,'declared6GiB audit boundary supported');start=time.monotonic();cpu=time.process_time()
    try:
        resource.setrlimit(resource.RLIMIT_AS,(cap,old[1]))
        try:result=_audit(directory,**kwargs)
        except (OverflowError,TimeoutError,MemoryError) as error:
            result=dict(schema='primitive-state-uniform-identity-probe-independent-review-v1',all_passed=False,status='UNKNOWN',nonconstant_formal_identity_refuted=False,necessary_formal_identity_constraint=None,independent_probe_check=None,independent_resource_failure=dict(reason=str(error)or type(error).__name__,error_type=type(error).__name__),independent_source_builds=None,independent_source_builds_attempted=None,joint_work=dict(max_work=450000000,total_work_reserve=450000000,preparation_reserve=50000000,producer_source_line_event_reserve=150000000,producer_evaluation_reserve=50000000,independent_source_line_event_reserve=150000000,independent_evaluation_reserve=50000000),**FLAGS)
        result['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,pid=os.getpid(),observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),audit_memory_limit_bytes=cap,audit_memory_limit_enforced=True,memory_boundary='restorable soft RLIMIT_AS; declared independent checker CLI')
        if time.monotonic()-start>kwargs.get('time_limit',3600):
            result.update(status='UNKNOWN',nonconstant_formal_identity_refuted=False,necessary_formal_identity_constraint=None,independent_resource_failure=dict(reason='final independent cost deadline',error_type='TimeoutError'))
        if write:
            with target.open('x')as f:json.dump(result,f,sort_keys=True,indent=2,allow_nan=False)
        return result
    finally:
        resource.setrlimit(resource.RLIMIT_AS,old);require(resource.getrlimit(resource.RLIMIT_AS)==old,'audit memory limit restored')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('directory');parser.add_argument('--write',action='store_true');args=parser.parse_args();print(json.dumps(audit(args.directory,write=args.write),sort_keys=True,indent=2))

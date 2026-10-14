"""One jointly bounded, hash-free augmented cached-chart endpoint audit.

Designated published mathematical reviews are premises, not recursive archive
verification. One exclusive marker prevents a second150m independent replay.
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
import check_primitive_state_augmented_cone_search as CORE
ROOT=Path(__file__).resolve().parent;BASE='cancellation-arithmetic-results/'
PARENT=BASE+'primitive-state-feedback-affine-002';PUBLICATION=BASE+'publication-024'
CHART=PARENT+'/jobs/chart.json';AFFINE=PARENT+'/jobs/affine.json';REVIEW=PARENT+'/independent_verification.json'
WARM=BASE+'primitive-state-backtracking-cone-search-001';WARM_PUBLICATION=BASE+'publication-026'
MAP=WARM+'/jobs/map.json';ENDPOINT=WARM+'/recovered-endpoint.json';WARM_REVIEW=WARM+'/independent_recovery_verification.json'
FRESH=BASE+'publication-027';EXTENSION=FRESH+'/affine-extension.json';FRESH_REVIEW=BASE+'primitive-state-fresh-identity-probe-001/independent_verification.json'
CACHE=BASE+'primitive-state-cached-primal-variants-001/jobs/prepare/source-cache.json'
CONSTRAINT=BASE+'publication-023/constraint.json';NEW_CONSTRAINTS=[FRESH+'/constraint-00.json',FRESH+'/constraint-01.json']
SCOPE='primitive_state_augmented_cone_search_resource_scope.txt'
INPUTS=[PUBLICATION+'/report.json',CHART,AFFINE,REVIEW,FRESH+'/report.json',EXTENSION,FRESH_REVIEW,*NEW_CONSTRAINTS,WARM_PUBLICATION+'/report.json',MAP,ENDPOINT,WARM_REVIEW,CACHE,CONSTRAINT,SCOPE]
TESTS=['test_primitive_state_augmented_cone_search','test_run_primitive_state_augmented_cone_search','test_check_primitive_state_augmented_cone_search','test_check_primitive_state_augmented_cone_search_run','test_primitive_state_augmented_cone_search_soundness','test_publish_cancellation_primitive_state_augmented_cone_search']
LIMITS=dict(max_work=450000000,preparation_work_reserve=50000000,synthetic_test_work_reserve=20000000,map_setup_operations=30000000,proposal_operations=195000000,endpoint_operations=25000000,independent_operations=150000000,cooperative_seconds=3600,independent_cooperative_seconds=3600,max_coefficient_bits=4096,max_temporary_bits=8193,max_cells=6000000,max_map_bytes=8388608,max_trace_bytes=33554432,max_endpoint_bytes=2097152,max_center_bytes=2097152,max_check_bytes=8388608,max_metadata_bytes=65536,max_protocol_bytes=65536,max_source_snapshot_bytes=8388608,max_cache_bytes=33554432,max_chart_bytes=8388608,max_affine_bytes=1048576,max_constraint_bytes=131072,max_input_bytes=33554432)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=7200,max_jobs=1,max_result_bytes=65536)
CAPS={PUBLICATION+'/report.json':1048576,CHART:8388608,AFFINE:1048576,REVIEW:1048576,FRESH+'/report.json':1048576,EXTENSION:8388608,FRESH_REVIEW:8388608,WARM_PUBLICATION+'/report.json':1048576,MAP:8388608,ENDPOINT:2097152,WARM_REVIEW:8388608,CACHE:33554432,CONSTRAINT:131072,**{p:131072 for p in NEW_CONSTRAINTS}}
FLAGS=CORE.FLAGS
require=CORE.require
_IO=contextvars.ContextVar("augmented_cone_io",default=None)

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




def parent():return dict(publication=PUBLICATION,chart=CHART,affine=AFFINE,review=REVIEW,extension_publication=FRESH,extension=EXTENSION,extension_review=FRESH_REVIEW,recovered_publication=WARM_PUBLICATION,recovered_endpoint=ENDPOINT,recovered_review=WARM_REVIEW,inherited_map=MAP,necessary_rows=[CONSTRAINT,*NEW_CONSTRAINTS],original_source=CACHE)

def expected_protocol():
    return dict(schema='primitive-state-augmented-cone-search-run-v1',inputs=INPUTS,input_caps=CAPS,limits=LIMITS,parallel=PARALLEL,tests=TESTS,precision=CORE.PRECISION,search=CORE.SEARCH,model=CORE.MODEL,scaling=CORE.SCALING,seed_rule=CORE.SEED,original_rows=5641,learned_rows=3,full_equations=5644,original_variables=1957,projected_variables=1224,pivots=782,free_coordinates=442,appended_pivots=[160,170],affected_columns=98,unchanged_columns=344,producer_count=1,worker_independent_checks=0,final_independent_checks=1,no_hashes=True,no_new_elimination=True,no_full_tape_replay=True,no_fresh_probe=True,scalar_first_endpoint=True,**FLAGS)

def ledger():return dict(max_work=450000000,allocations=dict(preparation=50000000,map_setup=30000000,proposal=195000000,exact_endpoint=25000000,final_independent=150000000),total_work_reserve=450000000,remaining_work=0,precision='fixed conservative reservations; no unaudited producer refinement',final_independent_stages_reserved=True)

def verify_protocol(value):require(value==expected_protocol(),"fixed augmented mathematical protocol")

def verify_ledger(value):require(value==ledger(),"single joint450m allocation")

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
        for name,file in v.get('artifacts',{}).items():require(name in ('chart','center','map','proposal','endpoint')and file==name+'.json'and(d/'jobs'/file).exists(),'saved mathematical artifact')
    if record:
        require(record.get('status')in('endpoint_complete','UNKNOWN')and type(record.get('producer_complete'))is bool and type(record.get('endpoint_complete'))is bool and type(record.get('deadline_exceeded'))is bool,'explicit numerical resource disposition')
        c=record.get('cost');require(type(c)is dict,'worker cost')
        for k in ('elapsed_seconds','cpu_seconds','peak_rss_kib'):require(type(c.get(k))in(int,float)and math.isfinite(c[k])and c[k]>=0,'finite worker cost')
        require(type(c.get('pid'))is int and c['pid']>0 and c.get('observed_threads_at_completion')==1,'one numerical worker thread')
    if progress:require(progress.get('phase')in('map_setup_started','map_setup_complete','backtracking_iteration','proposal_complete','proposal_returned','exact_endpoint_started','terminal_endpoint_complete','terminal_UNKNOWN'),'declared lifecycle')
    if row['status']=='available':require(record is not None and row.get('value')==dict(file='jobs/search-job.json',status=record['status'],cost=record['cost'],**FLAGS),'actual terminal transport')
    complete=row['status']=='available'and record is not None and record['status']=='endpoint_complete'and record['producer_complete']is True and record['endpoint_complete']is True and record['deadline_exceeded']is False
    if complete:
        require(record['cost']['elapsed_seconds']<=3600 and record['cost']['peak_rss_kib']<=6*1024**2,'successful worker respects cooperative and memory caps')
        require(all(v is not None and v.get('complete')is True for v in (mapreceipt,proposal,endpoint))and progress is not None and progress.get('phase')=='terminal_endpoint_complete','complete saved endpoint window')
        require(record.get('artifacts')==progress.get('artifacts')==dict(chart='chart.json',center='center.json',map='map.json',proposal='proposal.json',endpoint='endpoint.json'),'terminal artifact commitment')
        expected=dict(map_setup=mapreceipt['counts'],proposal=proposal['counts'],exact_endpoint=endpoint['counts']);require(record.get('stage_counts')==progress.get('stage_counts')==expected,'all stage diagnostic counts bound')
        require(record.get('stop_reason')==proposal.get('stop_reason'),'actual stopping reason')
    return dict(transport_status=row['status'],worker_status=record.get('status')if record else None,producer_complete=complete,deadline_exceeded=record.get('deadline_exceeded')if record else None,progress_retained=progress is not None)


SCHEMA='primitive-state-augmented-cone-search-independent-review-v1'

def unknown(error,check=None):
    counts=getattr(error,'independent_audit_counts',None)
    return dict(schema=SCHEMA,status='UNKNOWN',all_passed=False,chart_verified=False,center_verified=False,endpoint_verified=False,candidate_equations_verified=False,finite_candidate_feasible=None,independent_search_check=check,resource_failure=dict(reason=str(error)or type(error).__name__,error_type=type(error).__name__,consumed_counts=counts),joint_work=dict(max_work=450000000,total_work_reserve=450000000,preparation_reserved=50000000,map_setup_reserved=30000000,proposal_reserved=195000000,exact_endpoint_reserved=25000000,independent_reserved=150000000,independent_operations=counts.get('operations')if counts else None),**FLAGS)


def _audit(directory,*,deadline,max_operations,max_cells):
    d=Path(directory);verify_protocol(read(d/'protocol.json',65536));require(read(d/'parent.json',65536)==parent(),'designated mathematical inputs')
    report024=read(ROOT/(PUBLICATION+'/report.json'));require(report024.get('schema')==24 and report024.get('chart_verified')is True and report024.get('candidate_equations_verified')is True and report024.get('independent_audit_complete')is True and report024.get('coefficient_rank')==780 and report024.get('free_count')==444,'actual published024 finite chart premise')
    report027=read(ROOT/(FRESH+'/report.json'));require(report027.get('schema')==27 and report027.get('independent_audit_complete')is True and report027.get('coefficient_rank')==782 and report027.get('augmented_rank')==782 and report027.get('free_count')==442,'completed027 two-row formal extension')
    report026=read(ROOT/(WARM_PUBLICATION+'/report.json'));require(report026.get('schema')==26 and report026.get('independent_audit_complete')is True and report026.get('endpoint_verified')is True and report026.get('candidate_equations_verified')is True,'completed026 recovery, not old producer success')
    for v in(report024,report027,report026):false_flags(v)
    tests=read(d/'tests.json');match=re.search(r'Ran (\d+) tests?',tests.get('stderr',''));require(tests.get('returncode')==0 and match and tests['stderr'].rstrip().endswith('OK'),'joint-reserved synthetic suite')
    require(read(d/'run_started.json',65536)==dict(one_fixed_search=True),'one fixed numerical search')
    caps=dict(chart=8388608,center=2097152,map=8388608,proposal=33554432,endpoint=2097152)
    artifacts={name:read(d/'jobs'/(name+'.json'),cap)if(d/'jobs'/(name+'.json')).exists()else None for name,cap in caps.items()}
    for v in artifacts.values():
        if v is not None:false_flags(v)
    job=verify_job(d,read(d/'execution.json'),artifacts['map'],artifacts['proposal'],artifacts['endpoint']);check=None
    if all(artifacts[k]is not None and artifacts[k].get('complete')is True for k in('chart','center','map')):
        args=[read(ROOT/CACHE,CAPS[CACHE]),read(ROOT/CHART,CAPS[CHART]),read(ROOT/AFFINE,CAPS[AFFINE]),read(ROOT/CONSTRAINT,CAPS[CONSTRAINT]),read(ROOT/REVIEW,CAPS[REVIEW]),read(ROOT/EXTENSION,CAPS[EXTENSION]),[read(ROOT/p,CAPS[p])for p in NEW_CONSTRAINTS],read(ROOT/FRESH_REVIEW,CAPS[FRESH_REVIEW]),report027,read(ROOT/ENDPOINT,CAPS[ENDPOINT]),read(ROOT/WARM_REVIEW,CAPS[WARM_REVIEW]),read(ROOT/MAP,CAPS[MAP])]
        check=CORE.verify_search(*args,artifacts['chart'],artifacts['center'],artifacts['map'],artifacts['proposal'],artifacts['endpoint']if artifacts['endpoint']and artifacts['endpoint'].get('complete')is True else None,deadline=deadline,max_operations=max_operations,max_cells=max_cells)
    accepted=bool(job['producer_complete']and check and check['complete']and check['endpoint_verified'])
    status=('SCALAR_REJECTED'if check['endpoint_check']['negative_scalar_count']else'CONE_CHECKED')if accepted else'UNKNOWN'
    result=dict(schema=SCHEMA,status=status,all_passed=accepted,chart_verified=accepted,center_verified=accepted,endpoint_verified=accepted,candidate_equations_verified=accepted,finite_candidate_feasible=check['finite_candidate_feasible']if accepted else None,independent_search_check=check,job=job,tests_passed=int(match.group(1)),resource_failure=None,original_finite_equations=5641,learned_rows=3,full_equations=5644,original_variables=1957,rank=782,free_coordinates=442,parent_source_rebuilds=0,full_elimination_replayed=False,gradient_or_merit_certified=False,objective_preserved=False,joint_work=dict(max_work=450000000,total_work_reserve=450000000,preparation_reserved=50000000,map_setup_reserved=30000000,proposal_reserved=195000000,exact_endpoint_reserved=25000000,independent_reserved=150000000,independent_operations=check['audit_operations']if check else 0),**FLAGS)
    for k in('accepted_iterations','stop_reason','initial_objective','final_objective','initial_block_penalties','final_block_penalties'):result[k]=check.get(k)if check else None
    if time.monotonic()>deadline:raise TimeoutError('final mathematical input/audit deadline')
    return result


def audit(directory,*,write=False,time_limit=3600,max_operations=150000000,max_cells=6000000):
    require(type(time_limit)in(int,float)and math.isfinite(time_limit)and 0<time_limit<=3600,'strict final3600s deadline')
    for q,cap in((max_operations,150000000),(max_cells,6000000)):require(type(q)is int and 0<q<=cap,'strict shared independent cap')
    d=Path(directory);target=d/'independent_verification.json';marker=d/'independent_started.json'
    if target.exists()or marker.exists():raise FileExistsError('one final150m audit already consumed or started')
    with marker.open('x')as f:json.dump(dict(one_final_independent_audit=True,max_operations=max_operations,max_cells=max_cells),f)
    old=resource.getrlimit(resource.RLIMIT_AS);cap=6*1024**3;require(old[1]==resource.RLIM_INFINITY or old[1]>=cap,'supported6GiB final audit');start=time.monotonic();cpu=time.process_time();deadline=start+time_limit;token=_IO.set([0,0,deadline])
    created=False
    try:
        resource.setrlimit(resource.RLIMIT_AS,(cap,old[1]))
        try:result=_audit(d,deadline=deadline,max_operations=max_operations,max_cells=max_cells)
        except(OverflowError,TimeoutError,MemoryError)as error:result=unknown(error)
        cost=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,pid=os.getpid(),observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),audit_memory_limit_bytes=cap,audit_memory_limit_enforced=True,memory_boundary='restorable soft RLIMIT_AS')
        result['cost']=cost
        try:
            io=_IO.get();result['joint_work'].update(independent_io_operations=io[0],independent_io_bytes=io[1],independent_io_reserve_within_preparation=10000000)
            data=CORE.encoded(result)
            if len(data)>8388608:raise OverflowError('bounded8MiB independent summary')
            input_bytes=io[1];stable=False
            for _ in range(8):
                old_length=len(data);io[0]+=2*(old_length//64+1)
                result['joint_work'].update(independent_io_operations=io[0],independent_io_bytes=input_bytes+old_length);data=CORE.encoded(result)
                if len(data)>8388608:raise OverflowError('final8MiB independent summary')
                if io[0]>10000000:raise OverflowError('final output IO reserve')
                if len(data)==old_length:stable=True;break
            if not stable:raise OverflowError('bounded final IO counter serialization')
            io[1]=input_bytes+len(data)
            if time.monotonic()>deadline:raise TimeoutError('final output/cost deadline')
            if write:
                with target.open('xb')as f:
                    created=True;f.write(data)
                if time.monotonic()>deadline:raise TimeoutError('post-write independent deadline')
        except(OverflowError,TimeoutError,MemoryError)as error:
            consumed=result.get('independent_search_check')or {};error.independent_audit_counts=dict(operations=consumed.get('audit_operations'),audit_cells=consumed.get('audit_cells'),peak_live_cells=consumed.get('peak_live_cells'))
            result=unknown(error);result['cost']=cost;result['joint_work'].update(independent_io_operations=_IO.get()[0],independent_io_bytes=_IO.get()[1]);data=CORE.encoded(result)
            if write:
                with target.open('wb'if created else'xb')as f:f.write(data)
        return result
    finally:resource.setrlimit(resource.RLIMIT_AS,old);_IO.reset(token);require(resource.getrlimit(resource.RLIMIT_AS)==old,'restored final audit memory boundary')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('directory');p.add_argument('--write',action='store_true');a=p.parse_args();r=audit(a.directory,write=a.write);print(json.dumps({k:r.get(k)for k in('schema','status','all_passed','chart_verified','center_verified','endpoint_verified','finite_candidate_feasible','resource_failure','cost')},sort_keys=True))

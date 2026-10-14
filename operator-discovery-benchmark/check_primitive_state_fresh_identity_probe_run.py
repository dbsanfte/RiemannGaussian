"""One shared independent four-pass formal probe and sequential row audit.
No hashes, manifests, source cache, old elimination or candidate repair execute.
The designated024 chart is a prior complete row-span premise.
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
import check_primitive_state_fresh_identity_probe as CORE
ROOT=Path(__file__).resolve().parent;BASE='cancellation-arithmetic-results/'
PARENT=BASE+'primitive-state-backtracking-cone-search-001';PUBLICATION=BASE+'publication-026'
ENDPOINT=PARENT+'/recovered-endpoint.json';REVIEW=PARENT+'/independent_recovery_verification.json'
CHART=BASE+'primitive-state-feedback-affine-002/jobs/chart.json'
CHART_REVIEW=BASE+'primitive-state-feedback-affine-002/independent_verification.json'
CHART_PUBLICATION=BASE+'publication-024'
SCOPE='primitive_state_fresh_identity_probe_resource_scope.txt'
INPUTS=[PUBLICATION+'/report.json',ENDPOINT,REVIEW,CHART,CHART_REVIEW,CHART_PUBLICATION+'/report.json',SCOPE]
CASES=[dict(index=0,X=9,H=35,assignment_rule='u_n=2*n+1',assignment=[2*n+1 for n in range(1,36)]),dict(index=1,X=9,H=35,assignment_rule='u_n=(-1)^n*(n*n+1)',assignment=[(-1)**n*(n*n+1)for n in range(1,36)])]
TESTS=['test_primitive_state_fresh_identity_probe','test_run_primitive_state_fresh_identity_probe','test_check_primitive_state_fresh_identity_probe','test_check_primitive_state_fresh_identity_probe_run','test_primitive_state_fresh_identity_probe_soundness','test_publish_cancellation_primitive_state_fresh_identity_probe']
LIMITS=dict(max_work=450000000,producer_case_operations=100000000,producer_total_operations=200000000,independent_operations=200000000,preparation_work_reserve=50000000,synthetic_test_work_reserve=20000000,cooperative_seconds=3600,independent_cooperative_seconds=3600,max_coefficient_bits=4096,max_temporary_bits=8193,producer_case_cells=6000000,independent_cells=12000000,max_receipt_bytes=1048576,max_candidate_bytes=1048576,max_plan_bytes=262144,max_metadata_bytes=65536,max_protocol_bytes=65536,max_review_bytes=8388608,max_chart_bytes=8388608,max_source_snapshot_bytes=8388608,max_input_bytes=8388608)
PARALLEL=dict(workers=2,worker_memory_bytes=3*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=7200,max_jobs=2,max_result_bytes=65536)
FLAGS=CORE.FLAGS;PROGRAM=CORE.PROGRAM
require=CORE.require
CAPS={PUBLICATION+'/report.json':1048576,ENDPOINT:2097152,REVIEW:1048576,CHART:8388608,CHART_REVIEW:1048576,CHART_PUBLICATION+'/report.json':1048576}

_IO=contextvars.ContextVar("fresh_probe_io",default=None)

def parent():return dict(publication=PUBLICATION,candidate_source=ENDPOINT,recovery_review=REVIEW,chart=CHART,chart_review=CHART_REVIEW,chart_publication=CHART_PUBLICATION,n_variables=1957,one_fixed_recovered_point=True,original_producer_unknown_not_promoted=True)
def expected_protocol():
    return dict(schema='primitive-state-fresh-identity-probe-run-v1',parent=parent(),inputs=INPUTS,input_caps=CAPS,cases=CASES,program=PROGRAM,prime=65537,baseline='all-zero including u_1',spec=CORE.SPEC,layout=CORE.LAYOUT,source_constructor=CORE.SOURCE_CONSTRUCTOR,domain_policy=CORE.DOMAIN_POLICY,limits=LIMITS,parallel=PARALLEL,tests=TESTS,producer_cases=2,worker_independent_checks=0,final_independent_audits=1,independent_case_budget_shared=True,sequential_row_reduction='case0 then case1 against licensed024 chart and any independent prior-case row; all pivots ascending',no_old_basis_replay=True,no_candidate_repair=True,no_solver=True,no_hashes=True,exact_rational_feedback_rows=True,**FLAGS)


def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()


def account_bytes(length):
    io=_IO.get()
    if io is not None:
        io[0]+=2*(length//64+1);io[1]+=length
        if io[0]>10000000:raise OverflowError('joint preparation IO proxy')
        if time.monotonic()>io[2]:raise TimeoutError('independent input/output deadline')


def read(path,cap=1048576):
    require(type(cap)is int and 0<cap<=8388608,'bounded mathematical input cap')
    with Path(path).open('rb')as f:data=f.read(cap+1)
    if len(data)>cap:raise OverflowError('mathematical input byte cap')
    account_bytes(len(data));return json.loads(data)


def false_flags(value):
    require(type(value)is dict,'explicit scope record')
    for k in FLAGS:
        if k in value:require(value[k]is False,'no finite formal/global promotion '+k)


def verify_protocol(value):require(value==expected_protocol(),'fixed explicit two-case mathematical protocol')


def verify_ledger(value):
    expected=dict(max_work=450000000,allocations=dict(preparation=50000000,producer_cases={'case-00':100000000,'case-01':100000000},final_independent=200000000),total_work_reserve=450000000,remaining_work=0,precision='fixed reservations; no case sub-operation reset or unaudited refinement',final_independent_stages_reserved=True)
    require(value==expected,'single450m shared logical job')


def verify_jobs(d,execution,plans,probes):
    rows=execution.get('results');require(type(rows)is list and len(rows)==2 and [r.get('index')for r in rows]==[0,1]and all(type(r['index'])is int and r.get('status')in('available','error','missing_resource')for r in rows),'both ordered producer transports')
    cost=execution.get('cost',{})
    for k,v in dict(requested_workers=2,workers=2,max_in_flight=2,worker_memory_bytes=3*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn').items():require(type(cost.get(k))is type(v)and cost[k]==v,'actual parallel resource boundary '+k)
    for k in('elapsed_seconds','result_bytes','payload_bytes'):require(type(cost.get(k))in(int,float)and math.isfinite(cost[k])and cost[k]>=0,'finite transport cost')
    require(cost['result_bytes']<=139264,'bounded two-result transport')
    for k,status in [('available','available'),('missing','missing_resource'),('errors','error')]:require(type(cost.get(k))is int and cost[k]==sum(r['status']==status for r in rows),'complete transport accounting')
    jobs=[]
    for index,(row,plan,probe)in enumerate(zip(rows,plans,probes)):
        sub=d/'jobs'/('case-%02d'%index);record=read(sub/'probe-job.json',65536)if(sub/'probe-job.json').exists()else None;progress=read(sub/'progress.json',65536)if(sub/'progress.json').exists()else None
        if row['status']!='available':require('value'not in row,'failed transport does not invent completion')
        if record:
            false_flags(record);require(record.get('nonconstant_formal_identity_refuted')is False and record.get('case_index')==index and type(record.get('case_index'))is int and record.get('status')in('probe_complete','UNKNOWN')and type(record.get('producer_complete'))is bool and type(record.get('probe_complete'))is bool and type(record.get('deadline_exceeded'))is bool,'producer cannot claim checked refutation')
            if 'ledger'in record:verify_ledger(record['ledger'])
            else:require(record['status']=='UNKNOWN'and record['producer_complete']is False and record['probe_complete']is False,'outer failure admits nothing')
            c=record.get('cost');require(type(c)is dict,'worker cost')
            for k in('elapsed_seconds','cpu_seconds','peak_rss_kib'):require(type(c.get(k))in(int,float)and math.isfinite(c[k])and c[k]>=0,'finite worker cost')
            require(type(c.get('observed_threads_at_completion'))is int and c['observed_threads_at_completion']==1 and type(c.get('pid'))is int and c['pid']>0,'one thread per worker')
        if progress:
            false_flags(progress);verify_ledger(progress['ledger']);require(progress.get('case_index')==index and progress.get('phase')in('preflight_started','direct_evaluation_started','direct_columns_started','direct_probe_evaluated','probe_returned','terminal_probe_complete','terminal_UNKNOWN'),'bounded known case lifecycle')
        for value in (record,progress):
            if value is None:continue
            for name,file in value.get('artifacts',{}).items():require(name in('plan','probe')and file==name+'.json'and(sub/file).exists(),'actual saved mathematical artifact')
        if row['status']=='available':require(record is not None and row.get('value')==dict(file='jobs/case-%02d/probe-job.json'%index,status=record['status'],case_index=index,cost=record['cost'],**FLAGS),'actual case transport metadata')
        complete=row['status']=='available'and record is not None and record['status']=='probe_complete'and record['producer_complete']is True and record['probe_complete']is True and record['deadline_exceeded']is False
        if complete:
            require(record.get('producer_case_reserve')==100000000,'one fixed100m producer case allocation')
            require(record['cost']['elapsed_seconds']<=3600 and record['cost']['peak_rss_kib']<=3*1024**2,'successful case within declared resources')
            require(plan is not None and probe is not None and probe.get('complete')is True and progress is not None and progress.get('phase')=='terminal_probe_complete'and 'ledger'in record,'complete committed case result')
            require(record.get('artifacts')==progress.get('artifacts')==dict(plan='plan.json',probe='probe.json')and record.get('producer_status')==probe.get('status')and record.get('nonconstant_difference')==probe.get('nonconstant_difference')and record.get('evaluation_counts')==probe.get('counts'),'committed complete mathematical output')
        jobs.append(dict(index=index,transport_status=row['status'],worker_status=record.get('status')if record else None,producer_complete=complete,deadline_exceeded=record.get('deadline_exceeded')if record else None,progress_retained=progress is not None))
    return jobs


def unknown_result(failure=None,**fields):
    return dict(schema='primitive-state-fresh-identity-probe-independent-review-v1',all_passed=False,status='UNKNOWN',nonconstant_formal_identity_refuted=False,necessary_formal_identity_constraints=[],affine_extension=None,case_checks=[],resource_failure=failure,joint_work=dict(max_work=450000000,total_work_reserve=450000000,preparation_reserved=50000000,producer_case_reserved=100000000,producer_total_reserved=200000000,independent_reserved=200000000,independent_operations=None,second_final_audit=False),**fields,**FLAGS)


def _audit(directory,deadline,max_operations,max_cells):
    d=Path(directory);verify_protocol(read(d/'protocol.json',65536));vector=read(d/'candidate.json');require(type(vector)is list and len(vector)==1957,'full fixed recovered original point')
    report=read(ROOT/(PUBLICATION+'/report.json'));review=read(ROOT/REVIEW);endpoint=read(ROOT/ENDPOINT,2097152)
    require(report.get('schema')==26 and report.get('independent_audit_complete')is True and report.get('endpoint_verified')is True and report.get('candidate_equations_verified')is True and report.get('endpoint_path')==ENDPOINT and report.get('independent_review_path')==REVIEW,'designated completed026 recovered point')
    check=review.get('independent_search_check');require(review.get('schema')=='primitive-state-backtracking-recovery-independent-review-v1'and review.get('all_passed')is True and review.get('endpoint_verified')is True and review.get('candidate_equations_verified')is True and review.get('original_producer_status')=='UNKNOWN'and type(check)is dict and check.get('verified')is True and check.get('complete')is True and check.get('endpoint_verified')is True,'independent recovery premise; original failed producer remains UNKNOWN')
    require(endpoint.get('schema')=='primitive-state-backtracking-recovered-endpoint-v1'and endpoint.get('complete')is True and endpoint.get('candidate_original_vector')==vector,'actual unchanged026 exact1957 vector')
    false_flags(report);false_flags(review);false_flags(endpoint)
    tests=read(d/'tests.json');match=re.search(r'Ran (\d+) tests?',tests.get('stderr',''));require(tests.get('returncode')==0 and match and tests['stderr'].rstrip().endswith('OK'),'joint-reserved synthetic tests passed')
    require(read(d/'run_started.json',65536)==dict(two_fixed_probes=True),'exactly two preregistered probes')
    plans=[read(d/'jobs'/('case-%02d'%i)/'plan.json',262144)if(d/'jobs'/('case-%02d'%i)/'plan.json').exists()else None for i in range(2)]
    probes=[read(d/'jobs'/('case-%02d'%i)/'probe.json')if(d/'jobs'/('case-%02d'%i)/'probe.json').exists()else None for i in range(2)]
    jobs=verify_jobs(d,read(d/'execution.json'),plans,probes)
    for case,plan,probe in zip(CASES,plans,probes):
        if plan is not None:require(plan==CORE.expected_plan(vector,case['X'],case['assignment'],case['index']),'preregistered actual complete case plan')
        if probe is not None:
            false_flags(probe);require(plan is not None and type(probe.get('complete'))is bool,'explicit case evidence')
            if not probe['complete']:require(probe.get('status')=='UNKNOWN'and probe.get('feedback_row')is None and probe.get('nonconstant_difference')is None,'partial case cannot authorize any row')
    if not all(p is not None and p.get('complete')is True for p in probes):return None,unknown_result(dict(reason='both complete producer receipts required before shared final replay',error_type='MissingResource'),jobs=jobs,tests_passed=int(match.group(1)))
    chart=read(ROOT/CHART,8388608);chart_review=read(ROOT/CHART_REVIEW);chart_report=read(ROOT/(CHART_PUBLICATION+'/report.json'));require(chart_report.get('chart_path')==CHART,'designated024 prior chart file')
    result=CORE.verify_cases(vector,plans,probes,chart,chart_review,chart_report,deadline=deadline,max_operations=max_operations,max_cells=max_cells,chart_path=CHART)
    if not all(j['producer_complete']for j in jobs):return result,unknown_result(dict(reason='failed producer transport or final resource disposition; independent diagnostics retained',error_type='MissingResource'),jobs=jobs,tests_passed=int(match.group(1)))
    refuted=result['nonconstant_formal_identity_refuted'];review=dict(schema='primitive-state-fresh-identity-probe-independent-review-v1',all_passed=True,status='REFUTED'if refuted else'NOT_REFUTED_BY_THIS_PROBE',nonconstant_formal_identity_refuted=refuted,case_checks=result['case_checks'],necessary_formal_identity_constraints=result['necessary_formal_identity_constraints'],affine_extension=result['affine_extension'],resource_failure=None,candidate_origin='publication-026 independently recovered point',original_producer_status='UNKNOWN',jobs=jobs,tests_passed=int(match.group(1)),scalar_passes=4,symbolic_source_constructed=False,old_elimination_replayed=False,candidate_repaired=False,joint_work=dict(max_work=450000000,total_work_reserve=450000000,preparation_reserved=50000000,producer_case_reserved=100000000,producer_total_reserved=200000000,independent_reserved=200000000,independent_operations=result['audit_operations'],independent_cells=result['audit_cells'],second_final_audit=False),**FLAGS)
    return result,review


def audit(directory,*,write=False,time_limit=3600,max_operations=200000000,max_cells=12000000):
    require(type(time_limit)in(int,float)and math.isfinite(time_limit)and 0<time_limit<=3600,'strict independent deadline')
    for v,cap in ((max_operations,200000000),(max_cells,12000000)):require(type(v)is int and 0<v<=cap,'strict shared audit caps')
    d=Path(directory);target=d/'independent_verification.json';marker=d/'independent_started.json'
    for path in(target,marker):
        if path.exists():raise FileExistsError('single shared final audit reserve already started or used')
    old=resource.getrlimit(resource.RLIMIT_AS);cap=6*1024**3;require(old[1]==resource.RLIM_INFINITY or old[1]>=cap,'supported6GiB independent boundary');start=time.monotonic();cpu=time.process_time();deadline=start+time_limit
    with marker.open('x')as f:json.dump(dict(one_shared_final_audit=True,max_operations=200000000,second_final_audit=False),f)
    token=_IO.set([0,0,deadline]);diagnostic=None
    try:
        resource.setrlimit(resource.RLIMIT_AS,(cap,old[1]))
        try:diagnostic,result=_audit(d,deadline,max_operations,max_cells)
        except(OverflowError,TimeoutError,MemoryError)as error:
            result=unknown_result(dict(reason=str(error)or type(error).__name__,error_type=type(error).__name__,phase=getattr(error,'independent_phase',None),consumed_counts=getattr(error,'independent_audit_counts',None)))
            if hasattr(error,'independent_audit_counts'):result['joint_work'].update(independent_operations=error.independent_audit_counts['operations'],independent_cells=error.independent_audit_counts['cumulative_scalar_cells'])
        consumed=result.get('joint_work',{}).get('independent_operations')
        try:
            result['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,pid=os.getpid(),observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),audit_memory_limit_bytes=cap,audit_memory_limit_enforced=True,memory_boundary='restorable soft RLIMIT_AS')
            payload=encoded(result)
            account_bytes(len(payload))
            result['joint_work'].update(independent_io_operations=_IO.get()[0],independent_io_bytes=_IO.get()[1],independent_io_reserve_within_preparation=10000000)
            payload=encoded(result)
            if len(payload)>8388608 or time.monotonic()>deadline:
                result=unknown_result(dict(reason='final independent output byte/deadline cap',error_type='OverflowError'if len(payload)>8388608 else'TimeoutError'),cost=result['cost'])
            if write:
                with target.open('xb')as f:f.write(encoded(result))
            if time.monotonic()>deadline:
                result=unknown_result(dict(reason='final independent write deadline',error_type='TimeoutError'),cost=result['cost'])
                if write:target.write_bytes(encoded(result))
        except(OverflowError,TimeoutError,MemoryError)as error:
            result=unknown_result(dict(reason=str(error)or type(error).__name__,error_type=type(error).__name__,phase='final serialization/accounting/output'),cost=result.get('cost',{}))
            result['joint_work'].update(independent_operations=consumed,independent_io_operations=_IO.get()[0],independent_io_bytes=_IO.get()[1])
            if write:
                data=encoded(result)
                if target.exists():target.write_bytes(data)
                else:
                    with target.open('xb')as f:f.write(data)
        return result
    finally:resource.setrlimit(resource.RLIMIT_AS,old);_IO.reset(token);require(resource.getrlimit(resource.RLIMIT_AS)==old,'restored independent memory boundary')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('directory');p.add_argument('--write',action='store_true');a=p.parse_args();r=audit(a.directory,write=a.write);print(json.dumps({k:r.get(k)for k in('schema','all_passed','status','nonconstant_formal_identity_refuted','resource_failure','joint_work','cost')},sort_keys=True))

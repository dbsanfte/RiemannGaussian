"""Two preregistered direct formal probes with one shared independent audit."""
import argparse
import ast
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
from detector_parallel import run_jobs
from detector_workflow_guard import require_verified_runtime
import primitive_state_fresh_identity_probe as P

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
FLAGS=P.FLAGS;PROGRAM=P.PROGRAM
CAPS={PUBLICATION+'/report.json':1048576,ENDPOINT:2097152,REVIEW:1048576,CHART:8388608,CHART_REVIEW:1048576,CHART_PUBLICATION+'/report.json':1048576}

def read(path,cap=1048576):
    if type(cap)is not int or not 0<cap<=8388608:raise ValueError('bounded JSON read cap')
    with Path(path).open('rb')as f:data=f.read(cap+1)
    if len(data)>cap:raise OverflowError('bounded JSON input bytes')
    return json.loads(data)

def write(path,value,cap=65536):
    data=P.encoded(value)
    if len(data)>cap:raise OverflowError('bounded artifact bytes')
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);tmp=path.with_name(path.name+'.tmp')
    with tmp.open('wb')as f:f.write(data);f.flush();os.fsync(f.fileno())
    os.replace(tmp,path)

def sources():
    pending=['run_primitive_state_fresh_identity_probe','check_primitive_state_fresh_identity_probe_run',*TESTS];seen=set()
    while pending:
        name=pending.pop();path=ROOT/(name+'.py')
        if name in seen or not path.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0]for a in node.names)
            elif isinstance(node,ast.ImportFrom)and node.module:pending.append(node.module.split('.')[0])
    return sorted([*(name+'.py'for name in seen),SCOPE,'primitive_state_fresh_identity_probe_soundness_v1.txt'])

def parent():return dict(publication=PUBLICATION,candidate_source=ENDPOINT,recovery_review=REVIEW,chart=CHART,chart_review=CHART_REVIEW,chart_publication=CHART_PUBLICATION,n_variables=1957,one_fixed_recovered_point=True,original_producer_unknown_not_promoted=True)

def load_parent():
    """Read actual recovery premise/point; never run its original failed stage."""
    report=read(ROOT/(PUBLICATION+'/report.json'));review=read(ROOT/REVIEW);endpoint=read(ROOT/ENDPOINT,2097152)
    if report.get('schema')!=26 or report.get('independent_audit_complete')is not True or report.get('endpoint_verified')is not True or report.get('candidate_equations_verified')is not True or report.get('endpoint_path')!=ENDPOINT or report.get('independent_review_path')!=REVIEW:raise ValueError('completed publication026 independently recovered exact point')
    check=review.get('independent_search_check',{})
    if review.get('schema')!='primitive-state-backtracking-recovery-independent-review-v1'or review.get('all_passed')is not True or review.get('endpoint_verified')is not True or review.get('candidate_equations_verified')is not True or check.get('verified')is not True or check.get('complete')is not True or check.get('endpoint_verified')is not True:raise ValueError('actual completed recovery license')
    vector=endpoint.get('candidate_original_vector')
    if endpoint.get('complete')is not True or type(vector)is not list or len(vector)!=1957:raise ValueError('complete recovered original1957 point')
    chart_report=read(ROOT/(CHART_PUBLICATION+'/report.json'));chart_review=read(ROOT/CHART_REVIEW)
    if chart_report.get('schema')!=24 or chart_report.get('chart_verified')is not True or chart_report.get('coefficient_rank')!=780 or chart_report.get('free_count')!=444 or chart_report.get('chart_path')!=CHART or chart_review.get('all_passed')is not True or chart_review.get('chart_verified')is not True or chart_review.get('independent_affine_check',{}).get('normalized_chart_verified')is not True:raise ValueError('completed024 rank780 chart premise')
    return parent(),vector

def protocol():
    return dict(schema='primitive-state-fresh-identity-probe-run-v1',parent=parent(),inputs=INPUTS,input_caps=CAPS,cases=CASES,program=PROGRAM,prime=65537,baseline='all-zero including u_1',spec=P.SPEC,layout=P.LAYOUT,source_constructor=P.SOURCE_CONSTRUCTOR,domain_policy=P.DOMAIN_POLICY,limits=LIMITS,parallel=PARALLEL,tests=TESTS,producer_cases=2,worker_independent_checks=0,final_independent_audits=1,independent_case_budget_shared=True,sequential_row_reduction='case0 then case1 against licensed024 chart and any independent prior-case row; all pivots ascending',no_old_basis_replay=True,no_candidate_repair=True,no_solver=True,no_hashes=True,exact_rational_feedback_rows=True,**FLAGS)

def freeze(directory):
    require_verified_runtime();d=Path(directory).resolve()
    if d.exists():raise FileExistsError('fresh two-case destination')
    _,vector=load_parent();names=sources();value=protocol()
    if len(P.encoded(value))>65536 or len(P.encoded(vector))>1048576 or sum((ROOT/n).stat().st_size for n in names)>8388608:raise OverflowError('bounded freeze envelopes')
    for case in CASES:
        if len(P.encoded(P.preflight(vector,PROGRAM,X=case['X'],assignment=case['assignment'],case_index=case['index'])))>262144:raise OverflowError('bounded actual fixed case plan')
    for name,cap in CAPS.items():
        if(ROOT/name).stat().st_size>cap:raise OverflowError('fixed mathematical input bytes')
    d.mkdir();(d/'source_snapshot').mkdir()
    for name in names:(d/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(d/'protocol.json',value);write(d/'source_snapshot.json',names);write(d/'candidate.json',vector,1048576)

def validate(directory):
    d=Path(directory)
    if read(d/'protocol.json',65536)!=protocol():raise ValueError('literal fixed two-case mathematical protocol')
    vector=read(d/'candidate.json',1048576)
    if type(vector)is not list or len(vector)!=1957:raise ValueError('complete single fixed candidate')
    return vector

def ledger():return dict(max_work=450000000,allocations=dict(preparation=50000000,producer_cases={'case-00':100000000,'case-01':100000000},final_independent=200000000),total_work_reserve=450000000,remaining_work=0,precision='fixed reservations; no case sub-operation reset or unaudited refinement',final_independent_stages_reserved=True)

def process_case(vector,case,*,directory,deadline):
    d=Path(directory);d.mkdir(parents=True,exist_ok=True)
    out=dict(status='UNKNOWN',producer_complete=False,probe_complete=False,case_index=case['index'],nonconstant_formal_identity_refuted=False,artifacts={},ledger=ledger(),producer_case_reserve=100000000,**FLAGS)
    def progress(phase,detail=None):write(d/'progress.json',dict(phase=phase,case_index=case['index'],detail=detail,artifacts=out['artifacts'],ledger=out['ledger'],**FLAGS))
    def save(name,value,cap):write(d/(name+'.json'),value,cap);out['artifacts'][name]=name+'.json'
    try:
        progress('preflight_started');plan=P.preflight(vector,PROGRAM,X=case['X'],assignment=case['assignment'],case_index=case['index']);save('plan',plan,262144);progress('direct_evaluation_started')
        probe=P.probe(vector,plan,deadline=deadline,max_operations=100000000,max_cells=6000000,max_coefficient_bits=4096,max_receipt_bytes=1048576,checkpoint=lambda detail:progress(detail['phase'],detail));save('probe',probe,1048576)
        out.update(status='probe_complete'if probe['complete']else'UNKNOWN',producer_complete=probe['complete'],probe_complete=probe['complete'],producer_status=probe['status'],nonconstant_difference=probe.get('nonconstant_difference'),evaluation_counts=probe['counts']);progress('probe_returned')
        if not probe['complete']:out['reason']=probe.get('reason')
    except Exception as error:out.update(status='UNKNOWN',producer_complete=False,probe_complete=False,reason=str(error)or type(error).__name__,error_type=type(error).__name__,nonconstant_difference=None)
    try:progress('terminal_'+out['status'])
    except Exception as error:out.update(status='UNKNOWN',producer_complete=False,probe_complete=False,reason='terminal checkpoint: '+str(error),error_type=type(error).__name__)
    return out

def worker(job):
    require_verified_runtime();d=Path(job['directory']);index=job.get('index');start=time.monotonic();cpu=time.process_time();deadline=start+3600
    if job.get('phase')!='probe'or type(index)is not int or not 0<=index<2 or(d/'receipt.json').exists():raise ValueError('one of two fixed unsealed cases')
    subdir=d/'jobs'/('case-%02d'%index);out=dict(status='UNKNOWN',producer_complete=False,probe_complete=False,case_index=index,ledger=ledger(),nonconstant_formal_identity_refuted=False,**FLAGS)
    try:vector=validate(d);out.update(process_case(vector,CASES[index],directory=subdir,deadline=deadline));validate(d)
    except Exception as error:out.update(status='UNKNOWN',producer_complete=False,probe_complete=False,reason=str(error)or type(error).__name__,error_type=type(error).__name__)
    out['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),pid=os.getpid());out['deadline_exceeded']=time.monotonic()>deadline
    if out['deadline_exceeded']:out.update(status='UNKNOWN',producer_complete=False,probe_complete=False,reason='case cooperative deadline exceeded after validation')
    write(subdir/'probe-job.json',out);return dict(file='jobs/case-%02d/probe-job.json'%index,status=out['status'],case_index=index,cost=out['cost'],**FLAGS)

def run(directory):
    require_verified_runtime();d=Path(directory).resolve();validate(d)
    with(d/'run_started.json').open('x')as f:json.dump(dict(two_fixed_probes=True),f)
    tests=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=300);write(d/'tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr),1048576)
    if tests.returncode:raise ValueError('frozen fresh probe synthetic calibration failed')
    execution=run_jobs([dict(directory=str(d),phase='probe',index=i)for i in range(2)],worker='run_primitive_state_fresh_identity_probe:worker',**PARALLEL);write(d/'execution.json',execution,1048576);validate(d)
    write(d/'receipt.json',dict(files=['protocol.json','candidate.json','source_snapshot.json','tests.json','execution.json',*['jobs/case-%02d/%s.json'%(i,name)for i in range(2)for name in('plan','probe','probe-job','progress')]],two_fixed_probes=True,ledger=ledger(),**FLAGS))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory');args=parser.parse_args();(freeze if args.command=='freeze'else run)(args.directory)

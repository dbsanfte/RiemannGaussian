"""One frozen fresh-scale formal identity counterexample and necessary-row probe."""
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
import primitive_state_uniform_identity_probe as P

ROOT=Path(__file__).resolve().parent
PARENT='cancellation-arithmetic-results/primitive-state-balanced-cone-search-001'
PUBLICATION='cancellation-arithmetic-results/publication-021'
SCOPE='primitive_state_uniform_identity_probe_resource_scope.txt'
INPUTS=[PUBLICATION+'/report.json',*[PARENT+'/'+n for n in ['independent_verification.json','jobs/endpoint.json','jobs/check.json','jobs/search-job.json']],SCOPE,'primitive_state_uniform_identity_probe_design_v1.txt']
TESTS=['test_primitive_state_uniform_identity_probe','test_run_primitive_state_uniform_identity_probe','test_check_primitive_state_uniform_identity_probe','test_check_primitive_state_uniform_identity_probe_run','test_primitive_state_uniform_identity_probe_soundness','test_publish_cancellation_primitive_state_uniform_identity_probe']
LIMITS=dict(max_work=450000000,producer_source_line_events=150000000,independent_source_line_events=150000000,producer_evaluation_operations=50000000,independent_evaluation_operations=50000000,max_overhead_operations=50000000,cooperative_seconds=3600,independent_cooperative_seconds=3600,max_coefficient_bits=4096,max_temporary_bits=8193,max_source_cells=4000000,max_live_cells=6000000,max_polynomial_terms=100000,max_receipt_bytes=1048576,max_plan_bytes=262144,max_metadata_bytes=65536,max_protocol_bytes=65536,max_horizon=27,preparation_work_reserve=50000000,synthetic_test_work_reserve=20000000,max_source_snapshot_bytes=8388608,max_input_bytes=1048576,metadata_work_reserve=1048576)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=7200,max_jobs=1,max_result_bytes=65536)
PROGRAM=dict(target='mu',q=6,C='32',claim='critical')
FLAGS=P.FLAGS


def read(path,cap=1048576):
    path=Path(path)
    if path.stat().st_size>cap:raise OverflowError('bounded JSON input bytes')
    with path.open('rb')as f:data=f.read(cap+1)
    if len(data)>cap:raise OverflowError('bounded JSON read bytes')
    return json.loads(data)

def write(path,value,cap=65536):
    data=P.encoded(value)
    if len(data)>cap:raise OverflowError('bounded artifact bytes')
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);tmp=path.with_name(path.name+'.tmp')
    with tmp.open('wb')as f:f.write(data);f.flush();os.fsync(f.fileno())
    os.replace(tmp,path)


def sources():
    pending=['run_primitive_state_uniform_identity_probe','check_primitive_state_uniform_identity_probe_run',*TESTS];seen=set()
    while pending:
        name=pending.pop()
        if name in seen or not(ROOT/(name+'.py')).is_file():continue
        seen.add(name);tree=ast.parse((ROOT/(name+'.py')).read_text())
        for node in ast.walk(tree):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0]for a in node.names)
            elif isinstance(node,ast.ImportFrom)and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py'for n in seen)

def overhead_reserve():return LIMITS['preparation_work_reserve']


def load_parent():
    """Read fixed mathematical input once; no new hashes or integrity sweeps."""
    report=read(ROOT/(PUBLICATION+'/report.json'));review=read(ROOT/(PARENT+'/independent_verification.json'));endpoint=read(ROOT/(PARENT+'/jobs/endpoint.json'));check=read(ROOT/(PARENT+'/jobs/check.json'));job=read(ROOT/(PARENT+'/jobs/search-job.json'),65536)
    if report.get('schema')!=21 or review.get('all_passed')is not True or check!=review.get('search_check')or check.get('endpoint_verified')is not True or check.get('complete')is not True or job.get('status')!='endpoint_verified':raise ValueError('complete independently checked publication021 exact endpoint')
    vector=endpoint.get('candidate_original_vector')
    if endpoint.get('complete')is not True or type(vector)is not list or len(vector)!=1957:raise ValueError('full fixed original1957 exact candidate')
    return dict(publication=PUBLICATION,candidate_source=PARENT+'/jobs/endpoint.json',n_variables=1957,one_fixed_candidate=True),vector


def protocol(parent):
    value=dict(schema='primitive-state-uniform-identity-probe-run-v1',parent=parent,program=PROGRAM,spec=P.SPEC,layout=P.LAYOUT,semantic_keys=P.SEMANTIC_KEYS,native_constructor=P.NATIVE_CONSTRUCTOR,limits=LIMITS,parallel=PARALLEL,tests=TESTS,producer_source_builds=1,final_independent_source_builds=1,worker_independent_source_builds=0,joint450m=True,no_expanded_1957_columns=True,no_new_elimination_or_solver=True,no_actual_arithmetic_sign_assignment=True,exact_rational_feedback_row=True,modular_candidate_test=True,source_metric='global Python LINE_EVENTS, not arithmetic operations; every nested reset included',evaluation_metric='bounded rational/evaluation/serialization scalar work proxy',**FLAGS)
    if len(P.encoded(value))>65536:raise OverflowError('compact protocol byte cap')
    return value


def freeze(directory):
    require_verified_runtime();d=Path(directory).resolve()
    if d.exists():raise FileExistsError('fresh probe destination required')
    parent,vector=load_parent();names=sources()
    if sum((ROOT/n).stat().st_size for n in names)>LIMITS['max_source_snapshot_bytes']:raise OverflowError('one-time source snapshot byte cap')
    d.mkdir(parents=True);(d/'source_snapshot').mkdir()
    for name in names:(d/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(d/'protocol.json',protocol(parent));write(d/'source_snapshot.json',names);write(d/'candidate.json',vector,1048576)


def validate(directory):
    """Check actual mathematical protocol, not repeated code/archive snapshots."""
    d=Path(directory);value=read(d/'protocol.json',65536)
    parent=dict(publication=PUBLICATION,candidate_source=PARENT+'/jobs/endpoint.json',n_variables=1957,one_fixed_candidate=True)
    if value!=protocol(parent):raise ValueError('literal fixed mathematical protocol')
    vector=read(d/'candidate.json',1048576)
    if type(vector)is not list or len(vector)!=1957:raise ValueError('complete fixed original coordinate vector')
    return parent,vector


def process_probe(vector,*,directory,deadline,overhead_work_reserve):
    directory=Path(directory);directory.mkdir(parents=True,exist_ok=True)
    allocations=dict(preparation=overhead_work_reserve,producer_source=150000000,producer_evaluation=50000000,final_independent_source=150000000,final_independent_evaluation=50000000)
    if sum(allocations.values())>450000000:raise OverflowError('joint450m preflight')
    ledger=dict(max_work=450000000,allocations=allocations,total_work_reserve=sum(allocations.values()),remaining_work=450000000-sum(allocations.values()),precision='conservative fixed reserves; no producer count refinement',final_independent_stages_reserved=True)
    out=dict(status='UNKNOWN',probe_complete=False,nonconstant_formal_identity_refuted=False,artifacts={},ledger=ledger,**FLAGS)
    def progress(phase,detail=None):write(directory/'progress.json',dict(phase=phase,ledger=ledger,artifacts=out['artifacts'],detail=detail,**FLAGS))
    def save(name,value,cap):
        write(directory/(name+'.json'),value,cap);out['artifacts'][name]=name+'.json'
    try:
        progress('preflight_started');plan=P.preflight(vector,PROGRAM,X=7,prime=65537,deadline=deadline,limits=dict(max_operations=50000000));save('plan',plan,262144);progress('source_build_started')
        native=P.build_native_metered(PROGRAM,7,deadline=deadline,max_line_events=150000000,max_operations=50000000,max_source_cells=4000000,max_horizon=27,max_terms=100000,checkpoint=lambda detail:progress(detail['phase'],detail));out['source_meter']=native['probe_source_meter'];out['source_construction_counts']=native['probe_construction_counts'];progress('source_build_returned')
        result=P.probe_native(native,vector,plan,deadline=deadline,limits=dict(max_operations=50000000),checkpoint=lambda detail:progress(detail['phase'],detail));save('probe',result,1048576);out.update(status='probe_complete'if result['complete']else'UNKNOWN',producer_status=result['status'],probe_complete=result['complete'],nonconstant_difference=result.get('nonconstant_difference'),evaluation_counts=result['counts']);progress('probe_returned')
        if not result['complete']:out['reason']=result.get('reason')
    except Exception as error:out.update(status='UNKNOWN',probe_complete=False,reason=str(error)or type(error).__name__,error_type=type(error).__name__,nonconstant_difference=None)
    progress('terminal_'+out['status']);return out


def worker(job):
    require_verified_runtime();d=Path(job['directory']);start=time.monotonic();cpu=time.process_time();deadline=start+3600;out=dict(status='UNKNOWN',probe_complete=False,nonconstant_formal_identity_refuted=False,**FLAGS)
    if job.get('phase')!='probe'or job.get('index')!=0 or(d/'receipt.json').exists():raise ValueError('one fixed unsealed probe job')
    try:
        parent,vector=validate(d);out['parent']=parent;out.update(process_probe(vector,directory=d/'jobs',deadline=deadline,overhead_work_reserve=overhead_reserve()));validate(d)
    except Exception as error:out.update(status='UNKNOWN',probe_complete=False,reason=str(error)or type(error).__name__,error_type=type(error).__name__)
    out['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),pid=os.getpid());out['deadline_exceeded']=time.monotonic()>deadline
    if out['deadline_exceeded']:out.update(status='UNKNOWN',probe_complete=False,reason='cooperative probe deadline exceeded after final validation')
    write(d/'jobs/probe-job.json',out);return dict(file='jobs/probe-job.json',status=out['status'],cost=out['cost'],**FLAGS)


def run(directory):
    require_verified_runtime();d=Path(directory).resolve();validate(d)
    with(d/'run_started.json').open('x')as f:json.dump(dict(one_fixed_probe=True),f)
    tests=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=300);write(d/'tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr),1048576)
    if tests.returncode:raise ValueError('frozen exact probe synthetic calibration failed')
    execution=run_jobs([dict(directory=str(d),phase='probe',index=0)],worker='run_primitive_state_uniform_identity_probe:worker',**PARALLEL);write(d/'execution.json',execution,1048576);validate(d)
    write(d/'receipt.json',dict(files=['protocol.json','candidate.json','source_snapshot.json','tests.json','execution.json','jobs/probe-job.json','jobs/progress.json','jobs/plan.json','jobs/probe.json'],one_fixed_probe=True,**FLAGS))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory');a=parser.parse_args();(freeze if a.command=='freeze'else run)(a.directory)

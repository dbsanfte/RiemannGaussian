"""One hash-free exact feedback-row affine reduction and fixed-seed repair."""
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
import primitive_state_feedback_affine as P

ROOT=Path(__file__).resolve().parent
BASE='cancellation-arithmetic-results/'
CACHE=BASE+'primitive-state-cached-primal-variants-001/jobs/prepare/source-cache.json'
BASIS=BASE+'primitive-state-exact-row-basis-probe-002/jobs/basis.json'
PROJECTION=BASE+'primitive-state-exact-row-basis-probe-002/jobs/projection.json'
SEED=BASE+'primitive-state-balanced-cone-search-001/jobs/endpoint.json'
CONSTRAINT=BASE+'publication-023/constraint.json'
PUBLICATION=BASE+'publication-023'
SCOPE='primitive_state_feedback_affine_resource_scope.txt'
INPUTS=[CACHE,BASIS,PROJECTION,SEED,CONSTRAINT,PUBLICATION+'/report.json',SCOPE]
TESTS=['test_primitive_state_feedback_affine','test_run_primitive_state_feedback_affine','test_check_primitive_state_feedback_affine','test_check_primitive_state_feedback_affine_run','test_primitive_state_feedback_affine_soundness','test_publish_cancellation_primitive_state_feedback_affine']
LIMITS=dict(max_work=450000000,preparation_work_reserve=50000000,synthetic_test_work_reserve=20000000,
            producer_operations=150000000,independent_operations=250000000,
            cooperative_seconds=3600,independent_cooperative_seconds=3600,max_coefficient_bits=4096,
            max_temporary_bits=8193,max_cells=6000000,max_chart_bytes=33554432,max_receipt_bytes=8388608,
            max_metadata_bytes=65536,max_protocol_bytes=65536,max_source_snapshot_bytes=8388608,
            max_cache_bytes=33554432,max_basis_bytes=16777216,max_projection_bytes=65536,
            max_seed_bytes=1048576,max_constraint_bytes=131072,max_input_bytes=33554432)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=7200,max_jobs=1,max_result_bytes=65536)
FLAGS=P.FLAGS
CAPS={CACHE:33554432,BASIS:16777216,PROJECTION:65536,SEED:1048576,CONSTRAINT:131072,PUBLICATION+'/report.json':1048576}

def read(path,cap=1048576):
    if type(cap)is not int or not 0<cap<=33554432:raise ValueError('bounded JSON cap')
    with Path(path).open('rb')as f:data=f.read(cap+1)
    if len(data)>cap:raise OverflowError('bounded JSON bytes')
    return json.loads(data)

def write(path,value,cap=65536):
    data=P.encoded(value)
    if len(data)>cap:raise OverflowError('artifact byte cap')
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);tmp=path.with_name(path.name+'.tmp')
    with tmp.open('wb')as f:f.write(data);f.flush();os.fsync(f.fileno())
    os.replace(tmp,path)

def sources():
    pending=['run_primitive_state_feedback_affine','check_primitive_state_feedback_affine_run',*TESTS];seen=set()
    while pending:
        name=pending.pop();path=ROOT/(name+'.py')
        if name in seen or not path.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0]for a in node.names)
            elif isinstance(node,ast.ImportFrom)and node.module:pending.append(node.module.split('.')[0])
    return sorted(name+'.py'for name in seen)

def protocol():
    return dict(schema='primitive-state-feedback-affine-run-v1',inputs=INPUTS,input_caps=CAPS,limits=LIMITS,parallel=PARALLEL,tests=TESTS,
                original_rows=5641,original_variables=1957,projected_variables=1224,old_rank=779,old_free=445,
                source_program=dict(target='mu',q=6,C='32',claim='critical'),feedback_X=7,feedback_prime=65537,
                fixed_seed='exact publication021 original vector; no coordinate clipping',policy=P.POLICY,
                producer_count=1,worker_independent_replay_count=0,final_independent_replay_count=1,
                materialization='retained transcript exact normalized rows; no new elimination of the old system',
                independent_license='complete old transcript and actual column dependencies replayed by final checker',
                no_hashes=True,no_new_solver=True,no_cone_optimization=True,joint_work=450000000,**FLAGS)

def parent_metadata():
    """Metadata-only publication check; no source replay, reduction or scoring."""
    report=read(ROOT/(PUBLICATION+'/report.json'))
    if report.get('schema')!=23 or report.get('independent_audit_complete')is not True or report.get('feedback_constraint_available')is not True or report.get('feedback_constraint_file')!='constraint.json' or report.get('scale')!=7 or report.get('horizon')!=27:raise ValueError('publication023 complete necessary-row license')
    for name in ('RH_proved','global_bound_proved','universal_identity_proved','exact_admission'):
        if report.get(name)is not False:raise ValueError('finite row license does not admit '+name)
    return dict(publication=PUBLICATION,necessary_row=CONSTRAINT,seed_endpoint=SEED,source_cache=CACHE,old_basis=BASIS,old_projection=PROJECTION)

def freeze(directory):
    require_verified_runtime();d=Path(directory).resolve()
    if d.exists():raise FileExistsError('fresh feedback destination')
    parent_metadata();value=protocol();names=sources()
    if len(P.encoded(value))>65536 or sum((ROOT/n).stat().st_size for n in names)>8388608:raise OverflowError('protocol/source snapshot cap')
    for name,cap in CAPS.items():
        if (ROOT/name).stat().st_size>cap:raise OverflowError('fixed input byte cap')
    d.mkdir();(d/'source_snapshot').mkdir()
    for name in names:(d/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(d/'protocol.json',value);write(d/'source_snapshot.json',names);write(d/'parent.json',parent_metadata())

def validate(directory):
    if read(Path(directory)/'protocol.json',65536)!=protocol():raise ValueError('literal fixed affine protocol')
    if read(Path(directory)/'parent.json',65536)!=dict(publication=PUBLICATION,necessary_row=CONSTRAINT,seed_endpoint=SEED,source_cache=CACHE,old_basis=BASIS,old_projection=PROJECTION):raise ValueError('fixed mathematical input locations')

def load_inputs():
    parent_metadata()
    return tuple(read(ROOT/name,CAPS[name])for name in (CACHE,PROJECTION,BASIS,SEED,CONSTRAINT))

def ledger():
    return dict(max_work=450000000,allocations=dict(preparation=50000000,producer_affine=150000000,final_independent_affine=250000000),total_work_reserve=450000000,remaining_work=0,precision='fixed conservative allocations; diagnostic counts do not refine reservations',final_independent_stages_reserved=True)

def process_affine(inputs,*,directory,deadline):
    directory=Path(directory);directory.mkdir(parents=True,exist_ok=True)
    out=dict(status='UNKNOWN',producer_complete=False,classification=None,chart_available=False,artifacts={},ledger=ledger(),**FLAGS)
    def progress(phase,counts=None):write(directory/'progress.json',dict(phase=phase,counts=counts,artifacts=out['artifacts'],ledger=out['ledger'],**FLAGS))
    try:
        progress('affine_started')
        chart,receipt=P.build(*inputs,deadline=deadline,max_operations=150000000,max_cells=6000000,max_bits=4096,max_chart_bytes=33554432,max_receipt_bytes=8388608,checkpoint=progress)
        write(directory/'affine.json',receipt,8388608);out['artifacts']['affine']='affine.json'
        if chart is not None:
            write(directory/'chart.json',chart,33554432);out['artifacts']['chart']='chart.json'
        out.update(status='affine_complete'if receipt['complete']else'UNKNOWN',producer_complete=receipt['complete'],classification=receipt['classification'],chart_available=receipt['chart_available'],producer_counts=receipt['counts'],coefficient_rank=receipt.get('coefficient_rank'),augmented_rank=receipt.get('augmented_rank'),free_dimension=receipt.get('free_dimension'))
        if not receipt['complete']:out['reason']=receipt.get('reason')
    except Exception as error:out.update(status='UNKNOWN',producer_complete=False,chart_available=False,classification=None,reason=str(error)or type(error).__name__,error_type=type(error).__name__)
    try:progress('terminal_'+out['status'])
    except Exception as error:out.update(status='UNKNOWN',producer_complete=False,chart_available=False,reason='terminal checkpoint: '+str(error),error_type=type(error).__name__)
    return out

def worker(job):
    require_verified_runtime();d=Path(job['directory']);start=time.monotonic();cpu=time.process_time();deadline=start+3600
    out=dict(status='UNKNOWN',producer_complete=False,chart_available=False,classification=None,ledger=ledger(),**FLAGS)
    if job.get('phase')!='affine'or job.get('index')!=0 or(d/'receipt.json').exists():raise ValueError('single unsealed affine job')
    try:
        validate(d);out.update(process_affine(load_inputs(),directory=d/'jobs',deadline=deadline));validate(d)
    except Exception as error:out.update(status='UNKNOWN',producer_complete=False,chart_available=False,reason=str(error)or type(error).__name__,error_type=type(error).__name__)
    out['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),pid=os.getpid());out['deadline_exceeded']=time.monotonic()>deadline
    if out['deadline_exceeded']:out.update(status='UNKNOWN',producer_complete=False,chart_available=False,reason='cooperative affine deadline exceeded after final validation')
    write(d/'jobs/affine-job.json',out);return dict(file='jobs/affine-job.json',status=out['status'],cost=out['cost'],**FLAGS)

def run(directory):
    require_verified_runtime();d=Path(directory).resolve();validate(d)
    with(d/'run_started.json').open('x')as f:json.dump(dict(one_fixed_affine_job=True),f)
    tests=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=300);write(d/'tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr),1048576)
    if tests.returncode:raise ValueError('frozen affine synthetic calibration failed')
    execution=run_jobs([dict(directory=str(d),phase='affine',index=0)],worker='run_primitive_state_feedback_affine:worker',**PARALLEL);write(d/'execution.json',execution,1048576);validate(d)
    write(d/'receipt.json',dict(files=['protocol.json','parent.json','source_snapshot.json','tests.json','execution.json','jobs/affine-job.json','jobs/progress.json','jobs/affine.json','jobs/chart.json'],one_fixed_affine_job=True,**FLAGS))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory');args=parser.parse_args();(freeze if args.command=='freeze'else run)(args.directory)

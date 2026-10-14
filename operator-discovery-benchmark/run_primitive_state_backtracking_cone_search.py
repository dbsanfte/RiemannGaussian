"""One hash-free cached-chart cone proposal and final independent endpoint audit."""
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
import primitive_state_backtracking_cone_search as P

ROOT=Path(__file__).resolve().parent;BASE='cancellation-arithmetic-results/'
PARENT=BASE+'primitive-state-feedback-affine-002';PUBLICATION=BASE+'publication-024'
CHART=PARENT+'/jobs/chart.json';AFFINE=PARENT+'/jobs/affine.json';REVIEW=PARENT+'/independent_verification.json'
WARM=BASE+'primitive-state-feedback-cone-search-001';WARM_PUBLICATION=BASE+'publication-025'
MAP=WARM+'/jobs/map.json';PROPOSAL=WARM+'/jobs/proposal.json';ENDPOINT=WARM+'/jobs/endpoint.json';WARM_REVIEW=WARM+'/independent_verification.json'
CACHE=BASE+'primitive-state-cached-primal-variants-001/jobs/prepare/source-cache.json'
CONSTRAINT=BASE+'publication-023/constraint.json'
SCOPE='primitive_state_backtracking_cone_search_resource_scope.txt'
INPUTS=[PUBLICATION+'/report.json',CHART,AFFINE,REVIEW,WARM_PUBLICATION+'/report.json',MAP,PROPOSAL,ENDPOINT,WARM_REVIEW,CACHE,CONSTRAINT,SCOPE]
TESTS=['test_primitive_state_backtracking_cone_search','test_run_primitive_state_backtracking_cone_search','test_check_primitive_state_backtracking_cone_search','test_check_primitive_state_backtracking_cone_search_run','test_primitive_state_backtracking_cone_search_soundness','test_publish_cancellation_primitive_state_backtracking_cone_search']
LIMITS=dict(max_work=450000000,preparation_work_reserve=50000000,synthetic_test_work_reserve=20000000,map_setup_operations=5000000,proposal_operations=220000000,endpoint_operations=25000000,independent_operations=150000000,cooperative_seconds=3600,independent_cooperative_seconds=3600,max_coefficient_bits=4096,max_temporary_bits=8193,max_cells=6000000,max_map_bytes=8388608,max_trace_bytes=33554432,max_endpoint_bytes=2097152,max_check_bytes=65536,max_metadata_bytes=65536,max_protocol_bytes=65536,max_source_snapshot_bytes=8388608,max_cache_bytes=33554432,max_chart_bytes=8388608,max_affine_bytes=1048576,max_prior_proposal_bytes=16777216,max_constraint_bytes=131072,max_input_bytes=33554432)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=7200,max_jobs=1,max_result_bytes=65536)
CAPS={PUBLICATION+'/report.json':1048576,CHART:8388608,AFFINE:1048576,REVIEW:1048576,WARM_PUBLICATION+'/report.json':1048576,MAP:8388608,PROPOSAL:16777216,ENDPOINT:2097152,WARM_REVIEW:1048576,CACHE:33554432,CONSTRAINT:131072}
FLAGS=P.FLAGS

def read(path,cap=1048576):
    if type(cap)is not int or not 0<cap<=33554432:raise ValueError('bounded JSON input cap')
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
    pending=['run_primitive_state_backtracking_cone_search','check_primitive_state_backtracking_cone_search_run',*TESTS];seen=set()
    while pending:
        name=pending.pop();path=ROOT/(name+'.py')
        if name in seen or not path.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0]for a in node.names)
            elif isinstance(node,ast.ImportFrom)and node.module:pending.append(node.module.split('.')[0])
    return sorted(name+'.py'for name in seen)

def protocol():
    return dict(schema='primitive-state-backtracking-cone-search-run-v1',inputs=INPUTS,input_caps=CAPS,limits=LIMITS,parallel=PARALLEL,tests=TESTS,precision=P.PRECISION,search=P.SEARCH,model=P.MODEL,scaling=P.SCALING,seed_rule=P.SEED,original_rows=5641,original_variables=1957,projected_variables=1224,pivots=780,free_coordinates=444,producer_count=1,worker_independent_checks=0,final_independent_checks=1,centered_map='x_mp=rounded80digit x024+N(D*z); initial z is exact saved025 final z',exact_endpoint='free=exact x024_free+D*final269bit z; descending augmented backsub; canonical1957 lift',no_hashes=True,no_new_elimination=True,no_full_tape_replay=True,no_new_column_norms=True,no_new_power_pass=True,exact_original_and_feedback_equations_required=True,**FLAGS)

def load_parent_metadata():
    report=read(ROOT/(PUBLICATION+'/report.json'));review=read(ROOT/REVIEW)
    if report.get('schema')!=24 or report.get('chart_verified')is not True or report.get('candidate_equations_verified')is not True or report.get('independent_audit_complete')is not True or report.get('classification')!='independent'or report.get('coefficient_rank')!=780 or report.get('augmented_rank')!=780 or report.get('free_count')!=444 or report.get('chosen_pivot')!=148 or report.get('chart_path')!=CHART or report.get('affine_receipt_path')!=AFFINE:raise ValueError('complete verified publication024 chart and exact center')
    check=review.get('independent_affine_check',{})
    if review.get('all_passed')is not True or review.get('chart_verified')is not True or review.get('candidate_equations_verified')is not True or check.get('normalized_chart_verified')is not True or check.get('candidate_equations_verified')is not True or check.get('new_rank')!=780 or check.get('new_free_count')!=444:raise ValueError('actual mathematical chart license')
    warmreport=read(ROOT/(WARM_PUBLICATION+'/report.json'));warmreview=read(ROOT/WARM_REVIEW)
    if warmreport.get('schema')!=25 or warmreport.get('independent_audit_complete')is not True or warmreport.get('endpoint_verified')is not True or warmreport.get('candidate_equations_verified')is not True or warmreport.get('stop_reason')!='line_search_failed':raise ValueError('complete publication025 failed-three-trial endpoint')
    warmcheck=warmreview.get('independent_search_check',{})
    if warmreview.get('schema')!='primitive-state-feedback-cone-search-independent-review-v1'or warmreview.get('all_passed')is not True or warmreview.get('status')!='ENDPOINT_CHECKED'or warmreview.get('endpoint_verified')is not True or warmcheck.get('verified')is not True or warmcheck.get('endpoint_verified')is not True or warmreview.get('stop_reason')!='line_search_failed':raise ValueError('actual completed025 independent endpoint license')
    return parent()

def parent():return dict(publication=PUBLICATION,chart=CHART,center=AFFINE,review=REVIEW,warm_publication=WARM_PUBLICATION,warm_map=MAP,warm_proposal=PROPOSAL,warm_endpoint=ENDPOINT,warm_review=WARM_REVIEW,necessary_row=CONSTRAINT,original_source=CACHE)


def freeze(directory):
    require_verified_runtime();d=Path(directory).resolve()
    if d.exists():raise FileExistsError('fresh cone-search directory')
    parent=load_parent_metadata();value=protocol();names=sources()
    if len(P.encoded(value))>65536 or sum((ROOT/n).stat().st_size for n in names)>8388608:raise OverflowError('bounded protocol/source snapshot')
    for name,cap in CAPS.items():
        if(ROOT/name).stat().st_size>cap:raise OverflowError('fixed input bytes')
    d.mkdir();(d/'source_snapshot').mkdir()
    for name in names:(d/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(d/'protocol.json',value);write(d/'parent.json',parent);write(d/'source_snapshot.json',names)

def validate(directory):
    d=Path(directory)
    if read(d/'protocol.json',65536)!=protocol():raise ValueError('fixed literal cone-search protocol')
    expected=parent()
    if read(d/'parent.json',65536)!=expected:raise ValueError('fixed mathematical input locations')

def ledger():return dict(max_work=450000000,allocations=dict(preparation=50000000,map_setup=5000000,proposal=220000000,exact_endpoint=25000000,final_independent=150000000),total_work_reserve=450000000,remaining_work=0,precision='fixed conservative reservations; no unaudited producer refinement',final_independent_stages_reserved=True)

def load_inputs():
    load_parent_metadata();return tuple(read(ROOT/name,CAPS[name])for name in(CHART,AFFINE,MAP,PROPOSAL,ENDPOINT,CACHE,CONSTRAINT))

def process_search(inputs,*,directory,deadline):
    d=Path(directory);d.mkdir(parents=True,exist_ok=True);out=dict(status='UNKNOWN',producer_complete=False,endpoint_complete=False,artifacts={},stage_counts={},ledger=ledger(),**FLAGS)
    def progress(phase,counts=None):write(d/'progress.json',dict(phase=phase,counts=counts,artifacts=out['artifacts'],stage_counts=out['stage_counts'],ledger=out['ledger'],**FLAGS))
    def save(name,value,cap):write(d/(name+'.json'),value,cap);out['artifacts'][name]=name+'.json'
    try:
        chart,affine,oldmap,oldproposal,oldendpoint,cache,necessary=inputs;progress('map_setup_started')
        mapping,mapreceipt=P.setup(chart,affine,oldmap,oldproposal,oldendpoint,deadline=deadline,max_operations=5000000,max_cells=6000000,max_bits=4096,max_map_bytes=8388608);save('map',mapreceipt,8388608);out['stage_counts']['map_setup']=mapreceipt['counts'];progress('map_setup_complete')
        proposal=P.propose(mapping,deadline=deadline,max_operations=220000000,max_trace_bytes=33554432,checkpoint=lambda entry:progress(entry['phase'],entry['counts']));save('proposal',proposal,33554432);out['stage_counts']['proposal']=proposal['counts'];progress('proposal_returned')
        if not proposal['complete']:out['reason']=proposal.get('reason')
        else:
            out['producer_complete']=True;progress('exact_endpoint_started')
            endpoint=P.exact_endpoint(mapping,proposal,cache,necessary,deadline=deadline,max_operations=25000000,max_bits=4096,max_endpoint_bytes=2097152);save('endpoint',endpoint,2097152);out['stage_counts']['exact_endpoint']=endpoint['counts'];out.update(endpoint_complete=endpoint['complete'],status='endpoint_complete'if endpoint['complete']else'UNKNOWN',stop_reason=proposal.get('stop_reason'))
            if not endpoint['complete']:out['reason']=endpoint.get('reason')
    except Exception as error:out.update(status='UNKNOWN',endpoint_complete=False,reason=str(error)or type(error).__name__,error_type=type(error).__name__)
    try:progress('terminal_'+out['status'])
    except Exception as error:out.update(status='UNKNOWN',endpoint_complete=False,reason='terminal checkpoint: '+str(error),error_type=type(error).__name__)
    return out

def worker(job):
    require_verified_runtime();d=Path(job['directory']);start=time.monotonic();cpu=time.process_time();deadline=start+3600;out=dict(status='UNKNOWN',producer_complete=False,endpoint_complete=False,ledger=ledger(),**FLAGS)
    if job.get('phase')!='search'or job.get('index')!=0 or(d/'receipt.json').exists():raise ValueError('single unsealed cone-search job')
    try:validate(d);out.update(process_search(load_inputs(),directory=d/'jobs',deadline=deadline));validate(d)
    except Exception as error:out.update(status='UNKNOWN',producer_complete=False,endpoint_complete=False,reason=str(error)or type(error).__name__,error_type=type(error).__name__)
    out['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),pid=os.getpid());out['deadline_exceeded']=time.monotonic()>deadline
    if out['deadline_exceeded']:out.update(status='UNKNOWN',producer_complete=False,endpoint_complete=False,reason='cooperative cone-search deadline exceeded after validation')
    write(d/'jobs/search-job.json',out);return dict(file='jobs/search-job.json',status=out['status'],cost=out['cost'],**FLAGS)

def run(directory):
    require_verified_runtime();d=Path(directory).resolve();validate(d)
    with(d/'run_started.json').open('x')as f:json.dump(dict(one_fixed_search=True),f)
    tests=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=300);write(d/'tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr),1048576)
    if tests.returncode:raise ValueError('frozen cone-search synthetic calibration failed')
    execution=run_jobs([dict(directory=str(d),phase='search',index=0)],worker='run_primitive_state_backtracking_cone_search:worker',**PARALLEL);write(d/'execution.json',execution,1048576);validate(d)
    write(d/'receipt.json',dict(files=['protocol.json','parent.json','source_snapshot.json','tests.json','execution.json','jobs/search-job.json','jobs/progress.json','jobs/map.json','jobs/proposal.json','jobs/endpoint.json'],one_fixed_search=True,**FLAGS))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory');args=parser.parse_args();(freeze if args.command=='freeze'else run)(args.directory)

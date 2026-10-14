"""One fixed mixed-precision free-coordinate proposal with exact endpoint checks."""
import argparse
import ast
import importlib.metadata
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
import run_detector as R
from detector_parallel import run_jobs
from detector_workflow_guard import require_verified_runtime
import run_primitive_state_triangular_restoration as PREVIOUS
import primitive_state_balanced_cone_search as P
import check_primitive_state_balanced_cone_search as CHECK
import run_primitive_state_cone_jacobi_search as OLD

ROOT=Path(__file__).resolve().parent;BASE=ROOT/'cancellation-arithmetic-results';SOURCE=PREVIOUS.SOURCE
PARENT='cancellation-arithmetic-results/primitive-state-triangular-restoration-001';CACHE=PREVIOUS.CACHE;BASIS=PREVIOUS.BASIS;PROJECTION=PREVIOUS.PROJECTION
FLAGS=dict(P.FLAGS)
LIMITS=dict(cooperative_seconds=1800,max_work=450000000,worker_max_work=425000000,final_archive_audit_operations=25000000,materialization_operations=50000000,warm_setup_operations=5000000,proposal_operations=130000000,endpoint_operations=20000000,max_cache_bytes=134217728,max_tape_bytes=33554432,max_map_bytes=131072,max_warm_bytes=262144,max_trace_bytes=16777216,max_endpoint_bytes=1048576,max_check_bytes=65536,max_metadata_bytes=65536,max_protocol_bytes=65536,max_live_cells=4000000,max_fill_cells=20000000,max_audit_cells=60000000,max_coefficient_bits=4096,max_norm_bits=8192,max_temporary_bits=16385,max_scale_exponent=900,binding_byte_multiplier=4,source_byte_multiplier=12,metadata_work_reserve=1048576,synthetic_test_work_reserve=20000000)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=3600,max_jobs=1,max_result_bytes=65536)
TESTS=['test_primitive_state_balanced_cone_search','test_check_primitive_state_balanced_cone_search','test_run_primitive_state_balanced_cone_search','test_check_primitive_state_balanced_cone_search_run','test_primitive_state_balanced_cone_soundness']
SEED_PARENT='cancellation-arithmetic-results/primitive-state-cone-jacobi-search-001'
INPUTS=OLD.INPUTS+['cancellation-arithmetic-results/publication-020/manifest.json','cancellation-arithmetic-results/publication-020/report.json','primitive_state_balanced_cone_search_resource_scope.txt',*[SEED_PARENT+'/'+n for n in ['independent_verification.json','receipt.json','jobs/endpoint.json','jobs/check.json','jobs/search-job.json','jobs/map.json','jobs/norms.json','jobs/proposal.json']]]
ARTIFACT_CAPS=dict(map=131072,warm=262144,proposal=16777216,endpoint=1048576,check=65536)
read=PREVIOUS.read


def load_license():
    """Read/hash immutable parent envelopes; no new search or column response."""
    old=OLD.load_license();manifest=read(BASE/'publication-020/manifest.json');files=manifest['files']
    report=read(BASE/'publication-020/report.json');review=read(ROOT/(SEED_PARENT+'/independent_verification.json'));endpoint=read(ROOT/(SEED_PARENT+'/jobs/endpoint.json'));check=read(ROOT/(SEED_PARENT+'/jobs/check.json'));job=read(ROOT/(SEED_PARENT+'/jobs/search-job.json'),65536)
    if report.get('schema')!=20 or review.get('all_passed')is not True or check!=review.get('search_check') or check.get('endpoint_verified')is not True or check.get('complete')is not True or job.get('status')!='endpoint_verified' or job.get('endpoint_verified')is not True:raise ValueError('complete independently licensed publication020 warm endpoint')
    if report.get('independent_receipt_sha256')!=R.sha(ROOT/(SEED_PARENT+'/independent_verification.json')) or report.get('terminal_receipt_sha256')!=R.sha(ROOT/(SEED_PARENT+'/receipt.json')):raise ValueError('published warm review/terminal binding')
    if endpoint.get('complete')is not True or endpoint.get('normalized_basis_hash')!=old['normalized_basis_hash'] or len(endpoint.get('final_projected_vector',[]))!=1224 or len(endpoint.get('final_free_vector',[]))!=445:raise ValueError('same complete exact020 affine warm seed')
    names=[SEED_PARENT+'/'+n for n in ['independent_verification.json','receipt.json','jobs/endpoint.json','jobs/check.json','jobs/search-job.json','jobs/map.json','jobs/norms.json','jobs/proposal.json']]
    binding=dict(old['input_file_hashes'])
    for n in names:
        if n not in files:raise ValueError('published warm input '+n)
        binding[n]=files[n]
    binding.update({'cancellation-arithmetic-results/publication-020/'+n:R.sha(BASE/'publication-020'/n) for n in ['manifest.json','report.json']})
    return dict(old,publication='publication-020',archive_parent_publication='publication-020',publication_report_hash=R.sha(BASE/'publication-020/report.json'),base_endpoint_hash=old['seed_endpoint_hash'],warm_endpoint_hash=P.digest(endpoint),warm_candidate_hash=endpoint['candidate_hash'],warm_review_hash=files[SEED_PARENT+'/independent_verification.json'],warm_free_hash=P.digest(endpoint['final_free_vector']),warm_projected_hash=P.digest(endpoint['final_projected_vector']),input_file_hashes=binding)


def sources():
    pending=['run_primitive_state_balanced_cone_search','check_primitive_state_balanced_cone_search_run',*TESTS];seen=set()
    while pending:
        n=pending.pop();path=ROOT/(n+'.py')
        if n in seen or not path.is_file():continue
        seen.add(n)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def binding_work_reserve():return LIMITS['binding_byte_multiplier']*sum((ROOT/n).stat().st_size for n in INPUTS)+LIMITS['source_byte_multiplier']*sum((ROOT/n).stat().st_size for n in sources())+LIMITS['metadata_work_reserve']+LIMITS['synthetic_test_work_reserve']+1


def protocol(license):
    value=dict(schema='primitive-state-balanced-cone-search-run-v1',parent_license=license,limits=LIMITS,parallel=PARALLEL,tests=TESTS,precision=P.PRECISION,search=P.SEARCH,model=P.MODEL,scaling=P.SCALING,seed_rule=P.SEED,artifact_caps=ARTIFACT_CAPS,phases=['materialization','warm_setup','proposal','exact_endpoint'],joint_work_ceiling=True,versions={n:importlib.metadata.version(n) for n in ['mpmath','numpy']},one_fixed_seed=True,no_source_rebuild_or_new_elimination=True,no_precision_retry=True,original_objective_preserved=False,optimization_result=False,all_original_equalities_signs_and_PSD_required=True,endpoint_checker_full_elimination_replay=False,**FLAGS)
    if len(P.encoded(value))>LIMITS['max_protocol_bytes']:raise OverflowError('bounded free search protocol envelope')
    return value


def freeze(directory):
    require_verified_runtime();license=load_license();d=Path(directory).resolve();d.mkdir(exist_ok=False);(d/'jobs').mkdir();(d/'frozen_source').mkdir();source={}
    for n in sources():(d/'frozen_source'/n).write_bytes((ROOT/n).read_bytes());source[n]=R.sha(ROOT/n)
    SOURCE.bounded_write(d/'protocol.json',protocol(license),65536);SOURCE.bounded_write(d/'source_seal.json',source,65536);SOURCE.bounded_write(d/'input.json',dict(input_sha256={n:R.sha(ROOT/n) for n in INPUTS},binding_work_reserve=binding_work_reserve()),65536);SOURCE.bounded_write(d/'seal.json',{n+'_sha256':R.sha(d/(n+'.json')) for n in ['protocol','source_seal','input']},65536)


def validate(directory):
    d=Path(directory);seal=read(d/'seal.json',65536)
    for n in ['protocol','source_seal','input']:
        if seal[n+'_sha256']!=R.sha(d/(n+'.json')):raise ValueError('frozen free search seal '+n)
    source=read(d/'source_seal.json',65536)
    if set(source)!=set(sources()):raise ValueError('complete free search source closure')
    for n,h in source.items():
        if R.sha(ROOT/n)!=h or R.sha(d/'frozen_source'/n)!=h:raise ValueError('immutable free search source '+n)
    inputs=read(d/'input.json',65536)
    if set(inputs['input_sha256'])!=set(INPUTS) or inputs.get('binding_work_reserve')!=binding_work_reserve():raise ValueError('complete free search input/resource binding')
    for n,h in inputs['input_sha256'].items():
        if R.sha(ROOT/n)!=h:raise ValueError('immutable free search input '+n)
    license=load_license()
    if any(inputs['input_sha256'][n]!=h for n,h in license['input_file_hashes'].items()):raise ValueError('published chart/source license file binding')
    if read(d/'protocol.json',65536)!=protocol(license):raise ValueError('fixed scaled mixed-precision search protocol')
    return license,inputs['input_sha256']


def process_search(license,*,directory,deadline,input_work_reserve):
    directory=Path(directory);directory.mkdir(exist_ok=True);ledger=SOURCE.WorkLedger(450000000,input_work_reserve);ledger.allocate('final_archive_audit',25000000)
    out=dict(status='missing_resource',artifacts={},endpoint_verified=False,finite_candidate_feasible=None,**FLAGS)
    def progress(phase,detail=None):SOURCE.bounded_write(directory/'progress.json',dict(phase=phase,status=out['status'],artifacts=out['artifacts'],ledger=ledger.snapshot(),detail=detail,endpoint_verified=out['endpoint_verified'],finite_candidate_feasible=out['finite_candidate_feasible'],**FLAGS),65536)
    def save(n,value):
        path=directory/(n+'.json');SOURCE.bounded_write(path,value,ARTIFACT_CAPS[n]);out['artifacts'][n]=dict(file=path.name,sha256=R.sha(path))
    try:
        ledger.allocate('map_materialization',50000000);progress('map_materialization_started')
        mapping,map_receipt=P.materialize(license.cache,license.basis,license.projection,license.parent_restoration,license.parent_endpoint,license.warm_endpoint,deadline=deadline,max_operations=50000000,max_live_cells=4000000,max_fill_cells=20000000,max_bits=4096);save('map',map_receipt);progress('map_materialization_complete')
        ledger.allocate('warm_setup',5000000);progress('warm_setup_started')
        warm=P.warm_setup(mapping,license.norm_receipt,license.warm_proposal,license.warm_endpoint,deadline=deadline,max_operations=5000000,max_bits=4096);save('warm',warm);progress('warm_setup_complete')
        ledger.allocate('proposal_generator',130000000);ledger.allocate('exact_endpoint',20000000);progress('proposal_started')
        proposal=P.propose(mapping,deadline=deadline,max_operations=130000000,checkpoint=lambda detail:progress(detail['phase'],detail),max_trace_bytes=16777216);save('proposal',proposal);progress('proposal_returned');endpoint=None
        if proposal.get('complete')is True:
            try:endpoint=P.exact_endpoint(mapping,proposal,deadline=deadline,max_operations=20000000,max_bits=4096)
            except Exception as e:endpoint=dict(schema='primitive-state-balanced-cone-endpoint-v1',complete=False,candidate_original_vector=None,reason=str(e) or type(e).__name__,error_type=type(e).__name__,**FLAGS)
            save('endpoint',endpoint)
        progress('exact_endpoint_returned');allocation=ledger.remaining();source_cells=map_receipt['source_cells'];ops=allocation-sum(ARTIFACT_CAPS.values())-source_cells-1
        if ops<1:raise OverflowError('independent balanced audit allowance after exact artifact reserves')
        entry=ledger.allocate('search_checker',allocation);progress('search_check_started')
        check=CHECK.verify_search(license,map_receipt,warm,proposal,endpoint,deadline=deadline,max_operations=ops,max_cells=60000000,max_coefficient_bits=4096,max_map_bytes=131072,max_warm_bytes=262144,max_trace_bytes=16777216,max_endpoint_bytes=1048576);save('check',check)
        if check.get('verified')is not True:raise ValueError('independent balanced proposal/endpoint gate')
        ledger.precise(entry,check['independent_audit_work_reserve'],check['audit_operations'])
        out.update(status='endpoint_verified' if check.get('endpoint_verified')is True else 'unknown',endpoint_verified=check.get('endpoint_verified')is True,finite_candidate_feasible=check.get('finite_candidate_feasible'),proposal_stop_reason=proposal.get('stop_reason'),proposal_reason=proposal.get('reason'))
        progress(out['status'])
    except Exception as e:
        out.update(status='missing_resource' if isinstance(e,(OverflowError,TimeoutError,MemoryError,ImportError)) else 'rejected',reason=str(e) or type(e).__name__,endpoint_verified=False,finite_candidate_feasible=None)
        try:progress(out['status'])
        except Exception:pass
    return dict(out,ledger=ledger.snapshot())


def worker(job):
    require_verified_runtime();d=Path(job['directory']);start=time.monotonic();cpu=time.process_time();deadline=start+1800;out=dict(phase='search',index=0,endpoint_verified=False,finite_candidate_feasible=None,**FLAGS)
    if job.get('phase')!='search' or job.get('index')!=0 or (d/'receipt.json').exists():raise ValueError('one declared unsealed free search job')
    try:
        parent,bindings=validate(d);reserve=binding_work_reserve();out.update(parent_license=parent,input_work_reserve=reserve)
        license=CHECK.load_verified_license(ROOT,bindings,deadline=deadline,max_operations=min(50000000,reserve),max_cells=60000000,max_coefficient_bits=4096);out['license_loader_cost']=dict(audit_operations=license.summary['audit_operations'],audit_cells=license.summary['audit_cells'])
        if (license.summary['rank'],license.summary['free_count'],license.summary['original_variables'],license.summary['original_rows'])!=(779,445,1957,5641):raise ValueError('unchanged chart geometry/publication018 seed')
        out.update(process_search(license,directory=d/'jobs',deadline=deadline,input_work_reserve=reserve));validate(d)
    except Exception as e:out.update(status='missing_resource' if isinstance(e,(OverflowError,TimeoutError,MemoryError,ImportError)) else 'rejected',reason=str(e) or type(e).__name__,endpoint_verified=False,finite_candidate_feasible=None)
    out['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),pid=os.getpid());out['deadline_exceeded']=time.monotonic()>deadline
    if out['deadline_exceeded']:out.update(status='missing_resource',reason='cooperative free search deadline exceeded after final validation',endpoint_verified=False,finite_candidate_feasible=None)
    path=d/'jobs/search-job.json';SOURCE.bounded_write(path,out,65536)
    return dict(file=str(path.relative_to(d)),sha256=R.sha(path),status=out['status'],cost=out['cost'],**FLAGS)


def run(directory):
    require_verified_runtime();d=Path(directory).resolve();validate(d)
    with (d/'run_started.json').open('x') as f:json.dump(dict(protocol_sha256=R.sha(d/'protocol.json')),f)
    tests=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=300);R.write(d/'tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr))
    if tests.returncode:raise ValueError('prescore cone-Jacobi synthetic calibration failed')
    execution=run_jobs([dict(directory=str(d),phase='search',index=0)],worker='run_primitive_state_balanced_cone_search:worker',**PARALLEL);R.write(d/'execution.json',execution);validate(d)
    files={str(p.relative_to(d)):R.sha(p) for p in sorted(d.rglob('*')) if p.is_file() and 'frozen_source' not in p.parts};R.write(d/'receipt.json',dict(files_sha256=files,source_count=len(read(d/'source_seal.json',65536)),**FLAGS))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory');a=parser.parse_args();(freeze if a.command=='freeze' else run)(a.directory)

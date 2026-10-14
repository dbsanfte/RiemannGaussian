"""One fixed exact affine restoration, using immutable licensed source cache."""
import argparse
import ast
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
import run_primitive_state_cached_primal_variants as PREVIOUS
import primitive_state_triangular_restoration as P
import check_primitive_state_triangular_restoration as CHECK

ROOT=Path(__file__).resolve().parent;BASE=ROOT/'cancellation-arithmetic-results';SOURCE=PREVIOUS.SOURCE
PARENT='cancellation-arithmetic-results/primitive-state-cached-primal-variants-001';TAPE='cancellation-arithmetic-results/primitive-state-exact-row-basis-probe-002/jobs'
CACHE=PARENT+'/jobs/prepare/source-cache.json';TRACE=PARENT+'/jobs/faer_static_1e-6/trace.json';BASIS=TAPE+'/basis.json';PROJECTION=TAPE+'/projection.json'
FLAGS=dict(P.FLAGS)
LIMITS=dict(cooperative_seconds=900,max_work=450000000,producer_operations=125000000,max_cache_bytes=134217728,max_tape_bytes=33554432,max_receipt_bytes=8388608,max_metadata_bytes=65536,max_protocol_bytes=65536,max_live_cells=4000000,max_fill_cells=20000000,max_audit_cells=60000000,max_coefficient_bits=4096,binding_byte_multiplier=4,source_byte_multiplier=12,metadata_work_reserve=1048576)
PARALLEL=dict(workers=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,timeout_seconds=1800,max_jobs=1,max_result_bytes=65536)
TESTS=['test_primitive_state_triangular_restoration','test_check_primitive_state_triangular_restoration','test_run_primitive_state_triangular_restoration','test_check_primitive_state_triangular_restoration_run']
INPUTS=['cancellation-arithmetic-results/publication-015/manifest.json','cancellation-arithmetic-results/publication-015/report.json','cancellation-arithmetic-results/publication-016/manifest.json','cancellation-arithmetic-results/publication-016/report.json','primitive_state_triangular_restoration_resource_scope.txt','primitive_state_lossless_cone_quotient_analysis_v1.txt',PARENT+'/independent_verification_v2.json',PARENT+'/receipt.json',PARENT+'/seal.json',PARENT+'/jobs/prepare/job.json',PARENT+'/jobs/faer_static_1e-6/job.json',CACHE,TRACE,BASIS,PROJECTION]
read=PREVIOUS.read


def load_license():
    manifest=read(BASE/'publication-016/manifest.json');files=dict(manifest['files']);ancestor='cancellation-arithmetic-results/publication-015/manifest.json'
    if files.get(ancestor)!=R.sha(ROOT/ancestor):raise ValueError('bound publication015 tape ancestry')
    ancestor_files=read(ROOT/ancestor)['files']
    for n in [BASIS,PROJECTION]:
        if n not in ancestor_files:raise ValueError('complete ancestor exact tape binding')
        files[n]=ancestor_files[n]
    report=read(BASE/'publication-016/report.json');review=read(ROOT/(PARENT+'/independent_verification_v2.json'))
    if report.get('schema')!=16 or report.get('supplemental_audit')is not True or report.get('original_audit_contract_satisfied')is not False or review.get('schema')!='primitive-state-cached-primal-variants-independent-review-v2' or review.get('all_passed')is not True or review.get('original_audit_contract_satisfied')is not False:raise ValueError('completed supplemental publication016 license, original envelope remains failed')
    cache_check=review.get('cache_check',{})
    if cache_check.get('verified')is not True or cache_check.get('canonical_system_independently_rebuilt')is not True or review.get('parent_basis_replays')!=1 or review.get('geometry_rebuilds')!=1:raise ValueError('licensed exact source and parent basis replay')
    if report.get('independent_receipt_sha256')!=R.sha(ROOT/(PARENT+'/independent_verification_v2.json')) or report.get('terminal_receipt_sha256')!=R.sha(ROOT/(PARENT+'/receipt.json')):raise ValueError('publication016 review/terminal receipt binding')
    prep=read(ROOT/(PARENT+'/jobs/prepare/job.json'),65536);job=read(ROOT/(PARENT+'/jobs/faer_static_1e-6/job.json'),65536)
    if prep.get('status')!='cache_verified' or job.get('status')!='trace_verified' or job.get('termination_status')!='AlmostSolved':raise ValueError('fixed completed faer native seed')
    for n in [CACHE,TRACE,BASIS,PROJECTION,PARENT+'/independent_verification_v2.json',PARENT+'/receipt.json',PARENT+'/jobs/prepare/job.json',PARENT+'/jobs/faer_static_1e-6/job.json']:
        if n not in files:raise ValueError('complete publication016 input binding '+n)
    if prep['cache_binding']['cache_file_hash']!=files[CACHE] or cache_check.get('cache_compact_sha256')!=files[CACHE] or job['artifacts']['trace']['sha256']!=files[TRACE]:raise ValueError('licensed source-cache/native seed file bindings')
    variants=review.get('jobs',[]);faer=next((q for q in variants if q.get('variant')=='faer_static_1e-6'),None)
    if faer is None or faer.get('transport_status')!='available' or faer.get('worker_status')!='trace_verified':raise ValueError('independently available faer seed')
    return dict(parent_publication='publication-016',parent_review_hash=files[PARENT+'/independent_verification_v2.json'],publication_report_hash=R.sha(BASE/'publication-016/report.json'),input_file_hashes={n:files[n] for n in [CACHE,TRACE,BASIS,PROJECTION]},original_system_hash=cache_check['original_system_hash'],canonical_system_hash=cache_check['canonical_system_hash'],original_rows=5641,original_variables=1957,projected_variables=1224,rank=779,old_protocol_contract_satisfied=False)


def sources():
    pending=['run_primitive_state_triangular_restoration','check_primitive_state_triangular_restoration_run',*TESTS];seen=set()
    while pending:
        n=pending.pop();path=ROOT/(n+'.py')
        if n in seen or not path.is_file():continue
        seen.add(n)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def binding_work_reserve():
    return LIMITS['binding_byte_multiplier']*sum((ROOT/n).stat().st_size for n in INPUTS)+LIMITS['source_byte_multiplier']*sum((ROOT/n).stat().st_size for n in sources())+LIMITS['metadata_work_reserve']+1


def protocol(license):
    value=dict(schema='primitive-state-triangular-restoration-run-v1',parent_license=license,limits=LIMITS,parallel=PARALLEL,tests=TESTS,phases=['restore'],seed_variant='faer_static_1e-6',seed_rule=P.SEED_RULE,lift=P.LIFT,backsub_order='descending pivot column',original_objective_preserved=False,optimization_result=False,no_solver_or_new_elimination=True,one_fixed_seed=True,all_original_equalities_signs_and_PSD_required=True,parent_source_rebuild_required=False,**FLAGS)
    if len(P.encoded(value))>LIMITS['max_protocol_bytes']:raise OverflowError('bounded restoration protocol envelope')
    return value


def freeze(directory):
    require_verified_runtime();license=load_license();d=Path(directory).resolve();d.mkdir(exist_ok=False);(d/'jobs').mkdir();(d/'frozen_source').mkdir();source={}
    for n in sources():(d/'frozen_source'/n).write_bytes((ROOT/n).read_bytes());source[n]=R.sha(ROOT/n)
    SOURCE.bounded_write(d/'protocol.json',protocol(license),LIMITS['max_protocol_bytes']);SOURCE.bounded_write(d/'source_seal.json',source,65536);SOURCE.bounded_write(d/'input.json',dict(input_sha256={n:R.sha(ROOT/n) for n in INPUTS},binding_work_reserve=binding_work_reserve()),65536);SOURCE.bounded_write(d/'seal.json',{n+'_sha256':R.sha(d/(n+'.json')) for n in ['protocol','source_seal','input']},65536)


def validate(directory):
    d=Path(directory);seal=read(d/'seal.json',65536)
    for n in ['protocol','source_seal','input']:
        if seal[n+'_sha256']!=R.sha(d/(n+'.json')):raise ValueError('frozen exact restoration seal '+n)
    source=read(d/'source_seal.json',65536)
    if set(source)!=set(sources()):raise ValueError('complete restoration source closure')
    for n,h in source.items():
        if R.sha(ROOT/n)!=h or R.sha(d/'frozen_source'/n)!=h:raise ValueError('immutable restoration source '+n)
    inputs=read(d/'input.json',65536)
    if set(inputs['input_sha256'])!=set(INPUTS) or inputs.get('binding_work_reserve')!=binding_work_reserve():raise ValueError('complete restoration input/resource binding')
    for n,h in inputs['input_sha256'].items():
        if R.sha(ROOT/n)!=h:raise ValueError('immutable restoration input '+n)
    license=load_license()
    for n,h in license['input_file_hashes'].items():
        if inputs['input_sha256'][n]!=h:raise ValueError('immutable completed parent source/tape license '+n)
    if read(d/'protocol.json',LIMITS['max_protocol_bytes'])!=protocol(license):raise ValueError('exact fixed restoration protocol')
    return license


def process_restore(cache,trace,basis,projection,*,directory,deadline,input_work_reserve,expected_bindings=None):
    directory=Path(directory);directory.mkdir(exist_ok=True);ledger=SOURCE.WorkLedger(LIMITS['max_work'],input_work_reserve);out=dict(status='missing_resource',artifacts={},restoration_verified=False,finite_candidate_feasible=None,**FLAGS)
    def progress(phase,detail=None):SOURCE.bounded_write(directory/'progress.json',dict(phase=phase,status=out['status'],artifacts=out['artifacts'],ledger=ledger.snapshot(),detail=detail,restoration_verified=out['restoration_verified'],finite_candidate_feasible=out['finite_candidate_feasible'],**FLAGS),65536)
    def save(name,value):
        path=directory/(name+'.json');SOURCE.bounded_write(path,value,LIMITS['max_receipt_bytes']);out['artifacts'][name]=dict(file=path.name,sha256=R.sha(path))
    try:
        ledger.allocate('restoration_producer',LIMITS['producer_operations']);progress('restoration_started')
        receipt=P.restore(cache,trace,basis,projection,deadline=deadline,max_operations=LIMITS['producer_operations'],max_live_cells=LIMITS['max_live_cells'],max_fill_cells=LIMITS['max_fill_cells'],max_bits=LIMITS['max_coefficient_bits'],max_receipt_bytes=LIMITS['max_receipt_bytes'],checkpoint=lambda detail:progress(detail['phase'],detail))
        save('restoration',receipt);progress('restoration_returned')
        allocation=ledger.remaining();source_cells=sum(map(len,cache['original']['columns']))+len(cache['original']['rhs']);ops=allocation-LIMITS['max_receipt_bytes']-source_cells-1
        if ops<1:raise OverflowError('restoration independent audit allocation')
        entry=ledger.allocate('restoration_checker',allocation);progress('restoration_check_started')
        check=CHECK.verify_restoration(cache,trace,basis,projection,receipt,deadline=deadline,max_operations=ops,max_cells=LIMITS['max_audit_cells'],max_coefficient_bits=LIMITS['max_coefficient_bits'],max_receipt_bytes=LIMITS['max_receipt_bytes'],expected_bindings=expected_bindings)
        save('check',check)
        if check.get('verified')is not True:raise ValueError('independent restoration audit gate')
        ledger.precise(entry,check['independent_audit_work_reserve'],check['audit_operations'])
        if check.get('complete')is True and check.get('restoration_verified')is True:
            out.update(status='restoration_verified',restoration_verified=True,finite_candidate_feasible=check['finite_candidate_feasible'])
        else:out.update(status='unknown',reason=receipt.get('reason','incomplete exact restoration'),finite_candidate_feasible=None)
        progress(out['status'])
    except Exception as e:
        out.update(status='missing_resource' if isinstance(e,(TimeoutError,OverflowError,MemoryError,ImportError)) else 'rejected',reason=str(e) or type(e).__name__,restoration_verified=False,finite_candidate_feasible=None)
        try:progress(out['status'])
        except Exception:pass
    return dict(out,ledger=ledger.snapshot())


def worker(job):
    require_verified_runtime();d=Path(job['directory']);start=time.monotonic();cpu=time.process_time();deadline=start+LIMITS['cooperative_seconds'];out=dict(phase='restore',index=0,restoration_verified=False,finite_candidate_feasible=None,**FLAGS)
    if job.get('phase')!='restore' or job.get('index')!=0 or (d/'receipt.json').exists():raise ValueError('one declared unsealed exact restoration job')
    try:
        license=validate(d);reserve=binding_work_reserve();out.update(parent_license=license,input_work_reserve=reserve)
        cache=read(ROOT/CACHE,LIMITS['max_cache_bytes']);trace=read(ROOT/TRACE,LIMITS['max_receipt_bytes']);basis=read(ROOT/BASIS,LIMITS['max_tape_bytes']);projection=read(ROOT/PROJECTION,LIMITS['max_tape_bytes'])
        if (len(cache['original']['columns']),len(cache['original']['rhs']),basis.get('augmented_rank'),len(projection['retained_indices']))!=(1957,5641,779,1224):raise ValueError('unchanged licensed exact geometry')
        expected={name:P.digest(value) for name,value in [('cache',cache),('trace',trace),('basis',basis),('projection',projection)]}
        out.update(process_restore(cache,trace,basis,projection,directory=d/'jobs',deadline=deadline,input_work_reserve=reserve,expected_bindings=expected))
        validate(d)
    except Exception as e:out.update(status='missing_resource' if isinstance(e,(TimeoutError,OverflowError,MemoryError,ImportError)) else 'rejected',reason=str(e) or type(e).__name__,restoration_verified=False,finite_candidate_feasible=None)
    out['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),pid=os.getpid());out['deadline_exceeded']=time.monotonic()>deadline
    if out['deadline_exceeded']:
        out.update(status='missing_resource',reason='cooperative restoration deadline exceeded after final validation',restoration_verified=False,finite_candidate_feasible=None)
    path=d/'jobs/restoration-job.json'
    try:SOURCE.bounded_write(path,out,65536)
    except Exception:
        out.update(status='missing_resource',reason='bounded terminal serialization failure',restoration_verified=False,finite_candidate_feasible=None);SOURCE.bounded_write(path,out,65536)
    return dict(file=str(path.relative_to(d)),sha256=R.sha(path),status=out['status'],cost=out['cost'],**FLAGS)


def run(directory):
    require_verified_runtime();d=Path(directory).resolve();validate(d)
    with (d/'run_started.json').open('x') as f:json.dump(dict(protocol_sha256=R.sha(d/'protocol.json')),f)
    tests=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=180);R.write(d/'tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr))
    if tests.returncode:raise ValueError('prescore exact restoration calibration failed')
    execution=run_jobs([dict(directory=str(d),phase='restore',index=0)],worker='run_primitive_state_triangular_restoration:worker',**PARALLEL);R.write(d/'execution.json',execution);validate(d)
    files={str(p.relative_to(d)):R.sha(p) for p in sorted(d.rglob('*')) if p.is_file() and 'frozen_source' not in p.parts};R.write(d/'receipt.json',dict(files_sha256=files,source_count=len(read(d/'source_seal.json',65536)),**FLAGS))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory');a=parser.parse_args();(freeze if a.command=='freeze' else run)(a.directory)

"""One bounded source-cache preparation followed by two fixed native trials."""
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
import run_primitive_state_basis_primal as PREVIOUS
import primitive_state_cached_primal_variants as P
import check_primitive_state_cached_primal_variants as CHECK

ROOT=Path(__file__).resolve().parent;BASE=ROOT/'cancellation-arithmetic-results';SOURCE=PREVIOUS.SOURCE
PARENT_RUN='primitive-state-basis-primal-001';PARENT_PATH='cancellation-arithmetic-results/'+PARENT_RUN
PROGRAM=dict(PREVIOUS.PROGRAM);SCALES=list(PREVIOUS.SCALES);COMPILER_LIMITS=dict(PREVIOUS.COMPILER_LIMITS);FLAGS=dict(P.FLAGS)
LIMITS=dict(cooperative_seconds=900,max_work=450000000,producer_operations=50000000,max_cache_bytes=134217728,max_trace_bytes=8388608,max_log_bytes=1048576,max_metadata_bytes=65536,max_cells=4000000,max_audit_cells=60000000,max_coefficient_bits=4096)
PARALLEL=dict(workers=2,worker_memory_bytes=3*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=1800,max_jobs=2,max_result_bytes=65536)
PREP_PARALLEL=dict(PARALLEL,workers=1,memory_budget_bytes=3*1024**3,max_jobs=1)
TESTS=['test_primitive_state_cached_primal_variants','test_check_primitive_state_cached_primal_variants','test_run_primitive_state_cached_primal_variants','test_check_primitive_state_cached_primal_variants_run']
INPUTS=['cancellation-arithmetic-results/publication-015/manifest.json','cancellation-arithmetic-results/publication-015/report.json','primitive_state_cached_primal_variants_resource_scope.txt',*[PARENT_PATH+'/'+n for n in ['protocol.json','seal.json','source_seal.json','input.json','receipt.json','independent_verification.json','jobs/primal.json','jobs/primal-trace.json','jobs/primal-check.json']]]
read=PREVIOUS.read


def load_license():
    manifest=read(BASE/'publication-015/manifest.json')
    for n,h in manifest['files'].items():
        if R.sha(ROOT/n)!=h:raise ValueError('immutable publication015 '+n)
    d=BASE/PARENT_RUN;review=read(d/'independent_verification.json');record=read(d/'jobs/primal.json',65536);report=read(BASE/'publication-015/report.json');trace=read(d/'jobs/primal-trace.json')
    proof=review.get('basis_license_replay',{})
    if review.get('all_passed')is not True or record.get('status')!='trace_verified' or record.get('fresh_exact_basis_authorized')is not True or review.get('canonical_primal_matrix_independently_rebuilt')is not True:raise ValueError('completed parent exact basis/native assembly license')
    for n in ['projection','basis']:
        q=proof.get('replay_checks',{}).get(n,{})
        if q.get('verified')is not True or q.get('complete')is not True or q.get('projection_authorized' if n=='projection' else 'reduction_authorized')is not True:raise ValueError('completed parent independent exact '+n)
    if proof['replay_checks']['basis'].get('inconsistent_augmented_pivots')!=[]:raise ValueError('consistent parent augmented basis')
    indices=proof.get('indices')
    if indices!=record.get('selected_original_indices') or len(indices)!=779 or len(set(indices))!=779 or any(type(i)is not int or not 0<=i<5641 for i in indices):raise ValueError('licensed ORIGINAL row map')
    if report.get('independent_receipt_sha256')!=R.sha(d/'independent_verification.json') or report.get('terminal_receipt_sha256')!=R.sha(d/'receipt.json'):raise ValueError('publication015 exact license receipt bindings')
    return dict(selected_original_indices=indices,indices_hash=P.P.digest(indices),parent_assembly=trace['assembly'],parent_bindings=dict(publication_report_hash=R.sha(BASE/'publication-015/report.json'),parent_trace_hash=R.sha(d/'jobs/primal-trace.json'),parent_review_hash=R.sha(d/'independent_verification.json')))


def sources():
    pending=['run_primitive_state_cached_primal_variants','check_primitive_state_cached_primal_variants_run',*TESTS];seen=set()
    while pending:
        n=pending.pop();p=ROOT/(n+'.py')
        if n in seen or not p.is_file():continue
        seen.add(n)
        for node in ast.walk(ast.parse(p.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def solver_contract():
    contracts={}
    for v in P.VARIANTS:
        options=P.P.LOG.fields(P.settings(v['id'],900));options.pop('time_limit');contracts[v['id']]=dict(PREVIOUS.solver_contract(),fixed_options=options)
    return contracts


def protocol(license):
    return dict(schema='primitive-state-cached-primal-variants-run-v1',program=PROGRAM,scales=SCALES,language=SOURCE.P.SPEC,gram_specs=SOURCE.P.gram_specs(),compiler_limits=COMPILER_LIMITS,limits=LIMITS,parallel=PARALLEL,preparation_parallel=PREP_PARALLEL,tests=TESTS,variants=P.VARIANTS,phases=['prepare','variants'],parent_publication='publication-015',parent_run=PARENT_RUN,parent_license=license,solver_contracts=solver_contract(),shared_cache_schema=P.SCHEMA,expected_shape=dict(original_rows=5641,original_columns=1957,selected_rows=779,scalar_offset=1597),shared_preparation_count=1,exact_basis_replay_per_solver=False,exact_restore_all_original_rows_required=True,no_refit_or_source_selection=True,**FLAGS)


def freeze(directory):
    require_verified_runtime();license=load_license();d=Path(directory).resolve();d.mkdir(exist_ok=False);(d/'jobs').mkdir();(d/'frozen_source').mkdir();source={}
    for n in sources():(d/'frozen_source'/n).write_bytes((ROOT/n).read_bytes());source[n]=R.sha(ROOT/n)
    R.write(d/'protocol.json',protocol(license));R.write(d/'source_seal.json',source);R.write(d/'input.json',dict(input_sha256={n:R.sha(ROOT/n) for n in INPUTS}));R.write(d/'seal.json',{n+'_sha256':R.sha(d/(n+'.json')) for n in ['protocol','source_seal','input']})


def validate(directory):
    d=Path(directory);seal=read(d/'seal.json',65536)
    for n in ['protocol','source_seal','input']:
        if seal[n+'_sha256']!=R.sha(d/(n+'.json')):raise ValueError('frozen cache seal '+n)
    source=read(d/'source_seal.json',65536)
    if set(source)!=set(sources()):raise ValueError('complete cache source closure')
    for n,h in source.items():
        if R.sha(ROOT/n)!=h or R.sha(d/'frozen_source'/n)!=h:raise ValueError('immutable cache source '+n)
    inputs=read(d/'input.json',65536)['input_sha256']
    if set(inputs)!=set(INPUTS):raise ValueError('complete cache inputs')
    for n,h in inputs.items():
        if R.sha(ROOT/n)!=h:raise ValueError('immutable cache input '+n)
    license=load_license()
    if read(d/'protocol.json')!=protocol(license):raise ValueError('frozen cache protocol')
    return license


def binding(cache,path):
    return dict(cache_file_hash=R.sha(path),**{n:cache[n] for n in ['original_source_hash','canonical_cache_hash','assembly_hash']})


def process_prepare(columns,lhs,monomials,shape,offset,specs,selected,*,directory,deadline,compilation_work_reserve,parent_assembly,parent_bindings):
    directory=Path(directory);directory.mkdir(exist_ok=True);ledger=SOURCE.WorkLedger(LIMITS['max_work'],compilation_work_reserve);out=dict(status='missing_resource',artifacts={},**FLAGS)
    def save(n,value,cap):
        p=directory/(n+'.json');SOURCE.bounded_write(p,value,cap);out['artifacts'][n]=dict(file=p.name,sha256=R.sha(p))
    def progress(phase):SOURCE.bounded_write(directory/'progress.json',dict(phase=phase,status=out['status'],ledger=ledger.snapshot(),artifacts=out['artifacts'],**FLAGS),65536)
    try:
        ledger.allocate('cache_producer',LIMITS['max_cache_bytes']+LIMITS['producer_operations']);progress('cache_preparation_started')
        data,assembly=P.P.assemble(columns,lhs,monomials,list(shape),offset,specs,selected,deadline=deadline,max_operations=LIMITS['producer_operations'],max_cells=LIMITS['max_cells'],max_coefficient_bits=4096)
        if assembly!=parent_assembly:raise ValueError('parent original/canonical assembly equality')
        remaining=LIMITS['producer_operations']-assembly['counts']['operations']
        if remaining<1:raise OverflowError('shared assembly/encoding producer allowance')
        cache,counts=P.encode_cache(data,assembly,columns,lhs,monomials,shape,offset,specs,selected,parent_bindings,deadline=deadline,max_operations=remaining,max_cache_bytes=LIMITS['max_cache_bytes'])
        save('source-cache',cache,LIMITS['max_cache_bytes']);out['cache_binding']=binding(cache,directory/'source-cache.json');out['producer_counts']=counts;progress('cache_encoded')
        allocation=ledger.remaining();cells=assembly['counts']['source_cells'];ops=allocation-LIMITS['max_cache_bytes']-cells-1
        if ops<1:raise OverflowError('cache independent audit reserve')
        entry=ledger.allocate('cache_checker',allocation);progress('cache_check_started')
        check=CHECK.verify_cache(cache,expected_parent_assembly=parent_assembly,expected_source_hashes=P.source_hashes(),expected_parent_bindings=parent_bindings,deadline=deadline,max_operations=ops,max_cells=LIMITS['max_audit_cells'],max_cache_bytes=LIMITS['max_cache_bytes'])
        save('cache-check',check,LIMITS['max_trace_bytes'])
        if check.get('verified')is not True:raise ValueError('independent cache gate')
        ledger.precise(entry,check['independent_audit_work_reserve'],check['audit_operations']);out['status']='cache_verified';progress('cache_verified')
    except Exception as e:
        out.update(status='missing_resource' if isinstance(e,(TimeoutError,OverflowError,MemoryError,ImportError)) else 'rejected',reason=str(e) or type(e).__name__);progress(out['status'])
    return dict(out,ledger=ledger.snapshot())


def process_variant(cache,cache_binding,variant,*,directory,deadline):
    directory=Path(directory);directory.mkdir(exist_ok=True);ledger=SOURCE.WorkLedger(LIMITS['max_work'],1);out=dict(status='missing_resource',variant=variant,cache_binding=cache_binding,artifacts={},numerical_verification_pending=True,**FLAGS)
    def save(n,v):
        p=directory/(n+'.json');SOURCE.bounded_write(p,v,LIMITS['max_trace_bytes']);out['artifacts'][n]=dict(file=p.name,sha256=R.sha(p))
    def progress(phase):SOURCE.bounded_write(directory/'progress.json',dict(phase=phase,status=out['status'],ledger=ledger.snapshot(),artifacts=out['artifacts'],variant=variant,cache_binding=cache_binding,**FLAGS),65536)
    try:
        ledger.allocate('cache_decode',LIMITS['max_cache_bytes']+LIMITS['producer_operations']);progress('cache_decode_started')
        decoded,counts=P.decode_cache(cache,deadline=deadline);out['decode_counts']=counts
        ledger.allocate('native_producer',LIMITS['producer_operations']);progress('native_started')
        trace=P.solve_cached(decoded,cache,cache_binding,variant,deadline=deadline,log_path=str(directory/'native.log'),checkpoint_path=str(directory/'native-progress.json'));save('trace',trace);progress('native_returned')
        allocation=ledger.remaining();ops=allocation-LIMITS['max_cache_bytes']-LIMITS['max_trace_bytes']-decoded['assembly']['counts']['source_cells']-1
        if ops<1:raise OverflowError('variant independent audit reserve')
        entry=ledger.allocate('variant_checker',allocation);progress('variant_check_started')
        check=CHECK.verify_variant_trace(trace,cache,variant,expected_source_hashes=P.source_hashes(),expected_cache_file_hash=cache_binding['cache_file_hash'],deadline=deadline,max_operations=ops,max_cells=LIMITS['max_audit_cells'],max_cache_bytes=LIMITS['max_cache_bytes'],max_trace_bytes=LIMITS['max_trace_bytes'],max_log_bytes=LIMITS['max_log_bytes']);save('check',check)
        if check.get('verified')is not True:raise ValueError('independent variant gate')
        ledger.precise(entry,check['independent_audit_work_reserve'],check['audit_operations']);out.update(status='trace_verified',numerical_verification_pending=False,termination_status=trace['termination_status'],raw_vector_available=trace['original_vector']is not None);progress('trace_verified')
    except Exception as e:
        out.update(status='missing_resource' if isinstance(e,(TimeoutError,OverflowError,MemoryError,ImportError)) else 'rejected',reason=str(e) or type(e).__name__,numerical_verification_pending=True);progress(out['status'])
    return dict(out,ledger=ledger.snapshot())


def worker(job):
    require_verified_runtime();d=Path(job['directory']);license=validate(d);phase=job.get('phase');index=job.get('index');start=time.monotonic();cpu=time.process_time();deadline=start+900
    if (d/'receipt.json').exists() or (phase,index)not in [('prepare',0),('variant',0),('variant',1)]:raise ValueError('declared unsealed cache job')
    folder=d/'jobs'/('prepare' if phase=='prepare' else P.VARIANTS[index]['id']);folder.mkdir(exist_ok=True);out=dict(phase=phase,index=index,**FLAGS)
    try:
        if phase=='prepare':
            built=[SOURCE.P.build(PROGRAM,x) for x in SCALES];aux=SOURCE.P.auxiliary();instances=[b['instance'] for b in built]+[aux['instance']];blocks=[b['gram_blocks'] for b in built]+[aux['gram_blocks']];storage=[b['storage_blocks'] for b in built]+[aux['storage_blocks']]
            out.update(SOURCE.TRACE.metadata(built,instances,blocks,storage));columns,lhs,monomials,shape,offset,_,specs=SOURCE.S.prepare(instances,blocks,storage,gram_specs=SOURCE.P.gram_specs(),deadline=deadline,**COMPILER_LIMITS);charge=SOURCE.S.compilation_charge(instances,blocks,columns)
            if (len(columns),len(monomials),tuple(shape),offset)!=(1957,5641,(366,613),1597):raise ValueError('unchanged original source geometry')
            out.update(compilation_work_reserve=charge,complete_columns=len(columns),complete_monomials=len(monomials));out.update(process_prepare(columns,lhs,monomials,shape,offset,specs,license['selected_original_indices'],directory=folder,deadline=deadline,compilation_work_reserve=charge,parent_assembly=license['parent_assembly'],parent_bindings=license['parent_bindings']))
        else:
            prep=read(d/'jobs/prepare/job.json',65536)
            if prep.get('status')!='cache_verified':raise ValueError('completed shared cache gate')
            path=d/'jobs/prepare/source-cache.json';cache,b=P.read_cache(path,expected_sha256=prep['cache_binding']['cache_file_hash']);out.update(process_variant(cache,prep['cache_binding'],P.VARIANTS[index]['id'],directory=folder,deadline=deadline))
    except Exception as e:out.update(status='missing_resource' if isinstance(e,(TimeoutError,OverflowError,MemoryError,ImportError)) else 'rejected',reason=str(e) or type(e).__name__)
    out['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),pid=os.getpid());out['deadline_exceeded']=time.monotonic()>deadline
    validate(d);path=folder/'job.json';SOURCE.bounded_write(path,out,65536);return dict(file=str(path.relative_to(d)),sha256=R.sha(path),status=out['status'],cost=out['cost'],**FLAGS)


def preparation_ready(execution,record,path):
    results=execution.get('results',[])
    if len(results)!=1 or results[0].get('status')!='available' or record.get('status')!='cache_verified':return False
    return results[0].get('value')==dict(file='jobs/prepare/job.json',sha256=R.sha(path),status=record['status'],cost=record['cost'],**FLAGS)


def run(directory):
    require_verified_runtime();d=Path(directory).resolve();validate(d)
    with (d/'run_started.json').open('x') as f:json.dump(dict(protocol_sha256=R.sha(d/'protocol.json')),f)
    tests=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=180);R.write(d/'tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr))
    if tests.returncode:raise ValueError('prescore cached native calibration failed')
    preparation=run_jobs([dict(directory=str(d),phase='prepare',index=0)],worker='run_primitive_state_cached_primal_variants:worker',**PREP_PARALLEL);R.write(d/'preparation-execution.json',preparation)
    prep=read(d/'jobs/prepare/job.json',65536) if (d/'jobs/prepare/job.json').exists() else {}
    execution=run_jobs([dict(directory=str(d),phase='variant',index=i) for i in range(2)],worker='run_primitive_state_cached_primal_variants:worker',**PARALLEL) if preparation_ready(preparation,prep,d/'jobs/prepare/job.json') else dict(status='blocked',reason='shared cache gate',results=[])
    R.write(d/'execution.json',execution);validate(d);files={str(p.relative_to(d)):R.sha(p) for p in sorted(d.rglob('*')) if p.is_file() and 'frozen_source' not in p.parts};R.write(d/'receipt.json',dict(files_sha256=files,source_count=len(read(d/'source_seal.json')),**FLAGS))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory');a=parser.parse_args();(freeze if a.command=='freeze' else run)(a.directory)

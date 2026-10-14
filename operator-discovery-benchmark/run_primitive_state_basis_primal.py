"""One direct native SDP diagnostic on licensed exact ORIGINAL basis equations."""
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
import run_primitive_state_exact_row_basis_probe as SOURCE
import primitive_state_basis_primal as P
import check_primitive_state_basis_primal as CHECK

ROOT=Path(__file__).resolve().parent;BASE=ROOT/'cancellation-arithmetic-results'
BASIS_RUN='primitive-state-exact-row-basis-probe-002';BASIS_PATH='cancellation-arithmetic-results/'+BASIS_RUN
PROGRAM=dict(SOURCE.PROGRAM);SCALES=list(SOURCE.SCALES);COMPILER_LIMITS=dict(SOURCE.COMPILER_LIMITS)
FLAGS=dict(P.FLAGS)
LIMITS=dict(cooperative_seconds=900,max_work=450000000,producer_operations=50000000,
    max_cells=4000000,max_coefficient_bits=4096,max_trace_bytes=8388608,max_log_bytes=1048576,
    max_metadata_bytes=65536,max_audit_cells=60000000,exact_receipt_bytes=33554432,
    row_preparation_operations=20000000,projection_replay_operations=50000000,basis_replay_operations=125000000)
PARALLEL=dict(workers=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,timeout_seconds=1800,max_jobs=1,max_result_bytes=65536)
TESTS=['test_primitive_state_basis_primal','test_check_primitive_state_basis_primal',
    'test_run_primitive_state_basis_primal','test_check_primitive_state_basis_primal_run']
INPUTS=['cancellation-arithmetic-results/publication-014/manifest.json','cancellation-arithmetic-results/publication-014/report.json',
    'primitive_state_basis_primal_resource_scope.txt',*[BASIS_PATH+'/'+name for name in ['protocol.json','seal.json','receipt.json',
        'source_seal.json','input.json','independent_verification.json','jobs/progress.json','jobs/projection.json','jobs/basis.json','jobs/projection-check.json','jobs/basis-check.json']]]
SOURCE_BINDINGS=['ordinary_case_hashes','case_hashes','gram_block_hashes','storage_block_hashes','gram_archive_hashes','factor_archive_hashes',
    'divisor_archive_hashes','cell_archive_hashes','primitive_state_archive_hashes','primitive_source_hashes','multiplier_source_hashes',
    'dictionary_sha256','gram_specs','complete_columns','complete_monomials','exact_columns_hash','exact_target_hash','compilation_work_reserve']


def read(path,cap=8388608):
    path=Path(path)
    if path.stat().st_size>cap:raise OverflowError('bounded licensed-input bytes')
    with path.open('rb') as f:payload=f.read(cap+1)
    if len(payload)>cap:raise OverflowError('bounded licensed-input bytes')
    return json.loads(payload)


def validate_evidence(report,review,progress):
    """Old failed transport retains evidence; it supplies no equation admission."""
    if report.get('equation_reduction_verified')is not False or review.get('equation_reduction_verified')is not False:
        raise ValueError('publication014/oldrun must retain UNKNOWN equation admission')
    if review.get('all_passed')is not True or report.get('original_variables')!=1957 or report.get('original_finite_equations')!=5641:
        raise ValueError('independently archived unchanged original geometry')
    if report.get('full_optimization_variables_and_cones_unchanged')is not True or report.get('mathematical_cone_and_target_unchanged')is not True:
        raise ValueError('complete original cone/target binding')
    indices=progress.get('selected_original_row_indices')
    if progress.get('phase')!='basis_verified' or progress.get('status')!='basis_verified' or type(indices)is not list or len(indices)!=779 or len(set(indices))!=779 or any(type(i)is not int or not 0<=i<5641 for i in indices):
        raise ValueError('retained complete ORIGINAL basis checkpoint evidence')
    for value in (report,review,progress):
        for flag in FLAGS:
            if flag in value and value[flag]is not False:raise ValueError('saved evidence cannot claim cone certificate '+flag)
    return list(indices)


def load_license():
    # Name retained for protocol plumbing; authorization is explicitly pending
    # a NEW independent replay inside this numerical job.
    manifest=read(BASE/'publication-014/manifest.json')
    for name,h in manifest['files'].items():
        if R.sha(ROOT/name)!=h:raise ValueError('immutable publication014 '+name)
    d=BASE/BASIS_RUN;report=read(BASE/'publication-014/report.json');review=read(d/'independent_verification.json');progress=read(d/'jobs/progress.json',LIMITS['max_metadata_bytes'])
    indices=validate_evidence(report,review,progress)
    if report.get('independent_receipt_sha256')!=R.sha(d/'independent_verification.json') or report.get('terminal_receipt_sha256')!=R.sha(d/'receipt.json'):
        raise ValueError('publication014 binds failed oldrun review/terminal receipt')
    return dict(selected_original_indices=indices,indices_hash=P.digest(indices),authorization='requires fresh exact replay; oldrun UNKNOWN',
        publication_report_hash=R.sha(BASE/'publication-014/report.json'),basis_review_hash=R.sha(d/'independent_verification.json'),
        basis_terminal_hash=R.sha(d/'receipt.json'),basis_seal_hash=R.sha(d/'seal.json'),basis_progress_hash=R.sha(d/'jobs/progress.json'))



def sources():
    pending=['run_primitive_state_basis_primal','check_primitive_state_basis_primal_run',*TESTS];seen=set()
    while pending:
        name=pending.pop();path=ROOT/(name+'.py')
        if name in seen or not path.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def solver_contract():
    import clarabel
    settings=clarabel.DefaultSettings();settings.max_threads=1;settings.verbose=True;options=P.LOG.fields(settings);options.pop('time_limit')
    return dict(name='clarabel-native',versions={name:importlib.metadata.version(name) for name in ['clarabel','scipy','numpy']},fixed_options=options)


def protocol(license):
    return dict(schema='primitive-state-basis-primal-run-v1',program=PROGRAM,scales=SCALES,phases=['primal'],
        language=SOURCE.P.SPEC,gram_specs=SOURCE.P.gram_specs(),compiler_limits=COMPILER_LIMITS,limits=LIMITS,parallel=PARALLEL,tests=TESTS,
        expected_shape=dict(original_rows=5641,original_columns=1957,selected_rows=779,scalar_offset=1597),
        parent_publication='publication-014',basis_run=BASIS_RUN,basis_evidence=dict(license),fresh_exact_replay_required_before_solver=True,
        solver_contract=solver_contract(),strategy='fresh independently replayed saved exact tapes; one direct native primal solve on ORIGINAL equation rows; positive augmented infinity scaling; identity full coordinates',
        no_refit_or_source_selection=True,historical_development_scales=True,canonical_system_independently_rebuilt=True,exact_restore_all_original_rows_required=True,**FLAGS)


def freeze(directory):
    require_verified_runtime();license=load_license();d=Path(directory).resolve();d.mkdir(exist_ok=False);(d/'jobs').mkdir();(d/'frozen_source').mkdir();source={}
    for name in sources():
        (d/'frozen_source'/name).write_bytes((ROOT/name).read_bytes());source[name]=R.sha(ROOT/name)
    R.write(d/'protocol.json',protocol(license));R.write(d/'source_seal.json',source);R.write(d/'input.json',dict(input_sha256={name:R.sha(ROOT/name) for name in INPUTS}))
    R.write(d/'seal.json',{name+'_sha256':R.sha(d/(name+'.json')) for name in ['protocol','source_seal','input']})


def validate(directory):
    d=Path(directory);seal=read(d/'seal.json',LIMITS['max_metadata_bytes'])
    for name in ['protocol','source_seal','input']:
        if seal[name+'_sha256']!=R.sha(d/(name+'.json')):raise ValueError('frozen solver seal '+name)
    source=read(d/'source_seal.json',LIMITS['max_metadata_bytes'])
    if set(source)!=set(sources()):raise ValueError('complete solver source closure')
    for name,h in source.items():
        if R.sha(ROOT/name)!=h or R.sha(d/'frozen_source'/name)!=h:raise ValueError('immutable solver source '+name)
    inputs=read(d/'input.json',LIMITS['max_metadata_bytes'])['input_sha256']
    if set(inputs)!=set(INPUTS):raise ValueError('complete license/resource inputs')
    for name,h in inputs.items():
        if R.sha(ROOT/name)!=h:raise ValueError('bound exact license input '+name)
    license=load_license()
    if read(d/'protocol.json',LIMITS['max_metadata_bytes'])!=protocol(license):raise ValueError('exact frozen licensed primal protocol')
    return license


def fresh_basis_replay(columns,lhs,monomials,shape,offset,specs,selected_indices,*,directory,deadline,ledger):
    """New exact authorization from immutable saved tapes; no producer elimination."""
    from fractions import Fraction as F
    directory=Path(directory);directory.mkdir(exist_ok=True);artifacts={}
    def checkpoint(phase,authorized=False):
        SOURCE.bounded_write(directory/'progress.json',dict(phase=phase,status='missing_resource',fresh_exact_basis_authorized=authorized,
            ledger=ledger.snapshot(),artifacts={},exact_replay_artifacts=dict(artifacts),numerical_verification_pending=True,**FLAGS),LIMITS['max_metadata_bytes'])
    def save(name,value):
        path=directory/(name+'.json');SOURCE.bounded_write(path,value,LIMITS['max_trace_bytes']);artifacts[name]=dict(file=path.name,sha256=R.sha(path))
    checkpoint('exact_replay_started')
    prep=ledger.allocate('exact_row_preparation',LIMITS['row_preparation_operations'])
    retained,recipes=SOURCE.PROJECT_CHECK.full15_recipes(list(shape),offset,specs,len(columns))
    lookup={m:i for i,m in enumerate(monomials)};rows=[{} for _ in monomials];cells=0;work=len(monomials)+4*len(recipes)+1
    for new,j in enumerate(retained):
        for m,q in columns[j].items():
            work+=8
            if work>prep['allocation'] or cells+len(rows)>LIMITS['max_cells']:raise OverflowError('fresh exact row preparation cap')
            if time.monotonic()>deadline:raise TimeoutError('fresh exact row preparation deadline')
            if q:rows[lookup[m]][new]=F(q);cells+=1
    rhs=[lhs.get(m,F(0)) for m in monomials]
    projection=read(BASE/BASIS_RUN/'jobs/projection.json',LIMITS['exact_receipt_bytes']);basis=read(BASE/BASIS_RUN/'jobs/basis.json',LIMITS['exact_receipt_bytes'])
    if projection.get('complete')is not True or basis.get('complete')is not True or basis.get('coefficient_consistency')!='consistent' or basis.get('retained_indices')!=selected_indices or basis.get('augmented_rank')!=779:
        raise ValueError('saved complete consistent tape and ORIGINAL candidate indices')
    full_cells=sum(map(len,columns))+len(lhs);projected_nonzeros=sum(map(len,rows))
    allocation=LIMITS['projection_replay_operations']+LIMITS['exact_receipt_bytes']+full_cells+projected_nonzeros+1
    entry=ledger.allocate('projection_replay',allocation);checkpoint('projection_replay_started')
    project_limits=dict(max_operations=50000000,max_source_cells=4000000,max_live_cells=4000000,max_coefficient_bits=4096,max_receipt_bytes=33554432)
    project_check=SOURCE.PROJECT_CHECK.verify_projection(columns,lhs,monomials,retained,recipes,rows,rhs,projection,
        deadline=deadline,max_audit_operations=LIMITS['projection_replay_operations'],max_audit_cells=LIMITS['max_audit_cells'],
        max_coefficient_bits=LIMITS['max_coefficient_bits'],max_receipt_bytes=LIMITS['exact_receipt_bytes'],authorized_limits=project_limits)
    save('projection-replay',project_check)
    if project_check.get('verified')is not True or project_check.get('complete')is not True or project_check.get('projection_authorized')is not True:raise ValueError('fresh independent projection gate')
    ledger.precise(entry,project_check['independent_audit_work_reserve'],project_check['audit_operations']);checkpoint('projection_replay_verified')
    source_cells=projected_nonzeros+len(rhs);allocation=LIMITS['basis_replay_operations']+LIMITS['exact_receipt_bytes']+source_cells+1
    entry=ledger.allocate('basis_replay',allocation);checkpoint('basis_replay_started')
    basis_limits=dict(max_operations=175000000,max_source_cells=4000000,max_live_cells=4000000,max_fill_cells=20000000,max_coefficient_bits=4096,max_receipt_bytes=33554432)
    selected=[rows[i] for i in selected_indices];selected_rhs=[rhs[i] for i in selected_indices]
    basis_check=SOURCE.BASIS_CHECK.verify_rows(rows,rhs,len(retained),selected,selected_rhs,basis,deadline=deadline,
        max_audit_operations=LIMITS['basis_replay_operations'],max_audit_cells=LIMITS['max_audit_cells'],
        max_coefficient_bits=LIMITS['max_coefficient_bits'],max_receipt_bytes=LIMITS['exact_receipt_bytes'],authorized_limits=basis_limits)
    save('basis-replay',basis_check)
    if basis_check.get('verified')is not True or basis_check.get('complete')is not True or basis_check.get('reduction_authorized')is not True or basis_check.get('inconsistent_augmented_pivots')!=[]:
        raise ValueError('fresh independent complete consistent basis gate')
    if basis.get('source_hash')!=projection.get('projected_rows_hash'):raise ValueError('fresh exact projection/basis source binding')
    ledger.precise(entry,basis_check['independent_audit_work_reserve'],basis_check['audit_operations']);checkpoint('exact_basis_authorized',True)
    return dict(fresh_exact_basis_authorized=True,exact_replay_artifacts=artifacts,exact_row_preparation_work=work,selected_original_indices=list(selected_indices))


def process_primal(columns,lhs,monomials,shape,offset,specs,selected_indices,*,directory,deadline,compilation_work_reserve,ledger=None,exact_replay_artifacts=None):
    """Synthetic-testable bounded numerical stage; no arithmetic rebuild here."""
    directory=Path(directory);directory.mkdir(exist_ok=True)
    ledger=SOURCE.WorkLedger(LIMITS['max_work'],compilation_work_reserve) if ledger is None else ledger
    producer=ledger.allocate('native_producer',LIMITS['producer_operations'])
    out=dict(status='missing_resource',artifacts={},numerical_verification_pending=True,**FLAGS)
    def checkpoint(phase):
        SOURCE.bounded_write(directory/'progress.json',dict(phase=phase,ledger=ledger.snapshot(),status=out['status'],artifacts=out['artifacts'],numerical_verification_pending=out['numerical_verification_pending'],fresh_exact_basis_authorized=exact_replay_artifacts is not None,exact_replay_artifacts=exact_replay_artifacts,**FLAGS),LIMITS['max_metadata_bytes'])
    try:
        checkpoint('native_started')
        trace=P.solve_trace(columns,lhs,monomials,list(shape),offset,specs,selected_indices,deadline=deadline,
            max_operations=producer['allocation'],max_cells=LIMITS['max_cells'],max_coefficient_bits=LIMITS['max_coefficient_bits'],
            max_trace_bytes=LIMITS['max_trace_bytes'],max_log_bytes=LIMITS['max_log_bytes'],
            log_path=str(directory/'primal-native.log'),checkpoint_path=str(directory/'primal-progress.json'))
        path=directory/'primal-trace.json';SOURCE.bounded_write(path,trace,LIMITS['max_trace_bytes']);out['artifacts']['trace']=dict(file=path.name,sha256=R.sha(path));checkpoint('native_returned')
        allocation=ledger.remaining();source_cells=sum(map(len,columns))+len(lhs);audit_ops=allocation-LIMITS['max_trace_bytes']-source_cells-1
        if audit_ops<1:raise OverflowError('native independent audit reserve')
        check_entry=ledger.allocate('native_checker',allocation);checkpoint('native_check_started')
        check=CHECK.verify_trace(trace,columns,lhs,monomials,list(shape),offset,specs,selected_indices,
            expected_source_hashes={name:R.sha(ROOT/name) for name in ['primitive_state_basis_primal.py','primitive_state_solver_trace.py']},
            deadline=deadline,max_operations=audit_ops,max_cells=LIMITS['max_audit_cells'],max_coefficient_bits=LIMITS['max_coefficient_bits'],
            max_trace_bytes=LIMITS['max_trace_bytes'],max_log_bytes=LIMITS['max_log_bytes'])
        path=directory/'primal-check.json';SOURCE.bounded_write(path,check,LIMITS['max_trace_bytes']);out['artifacts']['check']=dict(file=path.name,sha256=R.sha(path))
        if check.get('verified')is not True:raise ValueError('independent native assembly/raw-coordinate audit gate')
        ledger.precise(check_entry,check['independent_audit_work_reserve'],check['audit_operations'])
        # The producer allocation stays conservative; its diagnostic counters are
        # archived but no reduction of the allocation relies on unverified counts.
        out.update(status='trace_verified',numerical_verification_pending=False,termination_status=trace['termination_status'],
            raw_vector_available=trace['original_vector']is not None,canonical_system_independently_rebuilt=True)
        checkpoint('trace_verified')
    except (OverflowError,TimeoutError,MemoryError,ImportError) as e:
        out.update(status='missing_resource',reason=str(e) or type(e).__name__,numerical_verification_pending=True);checkpoint('missing_resource')
    except (ValueError,TypeError,KeyError,RuntimeError,ZeroDivisionError) as e:
        out.update(status='rejected',reason=str(e) or type(e).__name__,numerical_verification_pending=True);checkpoint('rejected')
    return dict(out,ledger=ledger.snapshot())


def worker(job):
    require_verified_runtime();d=Path(job['directory']);license=validate(d)
    if job.get('phase')!='primal' or job.get('index')!=0 or (d/'receipt.json').exists():raise ValueError('one known unsealed native primal job')
    start=time.monotonic();cpu=time.process_time();deadline=start+LIMITS['cooperative_seconds'];out=dict(phase='primal',index=0,program=PROGRAM,scales=SCALES,basis_evidence=dict(license),fresh_exact_replay_required_before_solver=True,fresh_exact_basis_authorized=False,**FLAGS)
    try:
        built=[SOURCE.P.build(PROGRAM,X) for X in SCALES];aux=SOURCE.P.auxiliary();instances=[b['instance'] for b in built]+[aux['instance']]
        blocks=[b['gram_blocks'] for b in built]+[aux['gram_blocks']];storage=[b['storage_blocks'] for b in built]+[aux['storage_blocks']]
        out.update(SOURCE.TRACE.metadata(built,instances,blocks,storage))
        columns,lhs,monomials,shape,offset,_,specs=SOURCE.S.prepare(instances,blocks,storage,gram_specs=SOURCE.P.gram_specs(),deadline=deadline,**COMPILER_LIMITS)
        compilation=SOURCE.S.compilation_charge(instances,blocks,columns)
        out.update(complete_columns=len(columns),complete_monomials=len(monomials),compilation_work_reserve=compilation,
            exact_columns_hash=R.digest([[[list(m),str(q)] for m,q in sorted(p.items())] for p in columns]),exact_target_hash=R.digest([[list(m),str(q)] for m,q in sorted(lhs.items())]))
        if (len(columns),len(monomials),tuple(shape),offset)!=(1957,5641,(366,613),1597):raise ValueError('unchanged licensed original arithmetic geometry')
        ledger=SOURCE.WorkLedger(LIMITS['max_work'],compilation)
        replay=fresh_basis_replay(columns,lhs,monomials,shape,offset,specs,license['selected_original_indices'],directory=d/'jobs',deadline=deadline,ledger=ledger)
        out.update(replay)
        if replay.get('fresh_exact_basis_authorized')is not True:raise ValueError('fresh exact authorization before numerical solve')
        out.update(process_primal(columns,lhs,monomials,shape,offset,specs,license['selected_original_indices'],directory=d/'jobs',deadline=deadline,compilation_work_reserve=compilation,ledger=ledger,exact_replay_artifacts=replay['exact_replay_artifacts']))
    except (OverflowError,TimeoutError,MemoryError,ImportError) as e:out.update(status='missing_resource',reason=str(e) or type(e).__name__,numerical_verification_pending=True)
    except (ValueError,TypeError,KeyError,RuntimeError,ZeroDivisionError) as e:out.update(status='rejected',reason=str(e) or type(e).__name__,numerical_verification_pending=True)
    if 'ledger' in locals():out.setdefault('ledger',ledger.snapshot())
    out['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),pid=os.getpid());out['deadline_exceeded']=time.monotonic()>deadline
    validate(d);path=d/'jobs/primal.json';SOURCE.bounded_write(path,out,LIMITS['max_metadata_bytes'])
    return dict(file=str(path.relative_to(d)),sha256=R.sha(path),status=out['status'],cost=out['cost'],**FLAGS)


def run(directory):
    require_verified_runtime();d=Path(directory).resolve();validate(d)
    with (d/'run_started.json').open('x') as f:json.dump(dict(protocol_sha256=R.sha(d/'protocol.json')),f)
    tests=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=180)
    R.write(d/'tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr))
    if tests.returncode:raise ValueError('prescore direct-native calibration failed')
    execution=run_jobs([dict(directory=str(d),phase='primal',index=0)],worker='run_primitive_state_basis_primal:worker',**PARALLEL)
    R.write(d/'execution.json',execution);validate(d)
    files={str(p.relative_to(d)):R.sha(p) for p in sorted(d.rglob('*')) if p.is_file() and 'frozen_source' not in p.parts}
    R.write(d/'receipt.json',dict(files_sha256=files,source_count=len(read(d/'source_seal.json')),**FLAGS))
    print(dict(jobs=[r['status'] for r in execution['results']],**FLAGS))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory')
    args=parser.parse_args();(freeze if args.command=='freeze' else run)(args.directory)

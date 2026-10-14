"""Cap-only continuation of the frozen exact basis probe; no solver or admission."""
import argparse
import ast
import json
from pathlib import Path
import resource
import subprocess
import sys
import time
import run_primitive_state_exact_row_basis_probe as V1

ROOT=V1.ROOT;BASE=V1.BASE;R=V1.R
PROGRAM=dict(V1.PROGRAM);SCALES=list(V1.SCALES);COMPILER_LIMITS=dict(V1.COMPILER_LIMITS)
FLAGS=dict(V1.FLAGS);PARALLEL=dict(V1.PARALLEL)
LIMITS=dict(V1.LIMITS,max_receipt_bytes=32*1024**2)
TESTS=list(V1.TESTS)+['test_run_primitive_state_exact_row_basis_probe_v2','test_check_primitive_state_exact_row_basis_probe_v2']
PRIOR_RUN='primitive-state-exact-row-basis-probe-001'
PRIOR_PATH='cancellation-arithmetic-results/'+PRIOR_RUN
INPUTS=['cancellation-arithmetic-results/publication-013/manifest.json',
    'cancellation-arithmetic-results/publication-013/report.json','primitive_state_exact_basis_resource_scope_v2.txt',
    *[PRIOR_PATH+'/'+name for name in ['protocol.json','seal.json','receipt.json','independent_verification.json',
        'jobs/primal.json','jobs/projection.json','jobs/basis.json']]]
PROJECTION_BINDINGS=['full_columns_hash','monomial_domain_hash','target_hash','full_source_hash','projection_hash','projected_rows_hash']
PROJECT=V1.PROJECT;PROJECT_CHECK=V1.PROJECT_CHECK;BASIS_CHECK=V1.BASIS_CHECK;TRACE=V1.TRACE
SOURCE_BINDINGS=['ordinary_case_hashes','case_hashes','gram_block_hashes','storage_block_hashes','gram_archive_hashes',
    'factor_archive_hashes','divisor_archive_hashes','cell_archive_hashes','primitive_state_archive_hashes',
    'primitive_source_hashes','multiplier_source_hashes','dictionary_sha256','gram_specs',
    'complete_columns','complete_monomials','projected_columns','exact_columns_hash','exact_target_hash','compilation_work_reserve']


def validate_cap_only_limits(limits):
    V1.validate_limits(limits)
    if limits!=LIMITS or {k:v for k,v in limits.items() if k!='max_receipt_bytes'}!={k:v for k,v in V1.LIMITS.items() if k!='max_receipt_bytes'}:
        raise ValueError('only preregistered 32MiB receipt cap may differ')


def process_equations(*args,**kwargs):
    """Forward into the immutable v1 pipeline with explicit v2 resource limits."""
    supplied=kwargs.get('limits',LIMITS);validate_cap_only_limits(supplied)
    kwargs['limits']=supplied
    return V1.process_equations(*args,**kwargs)


def bounded_read(path,cap):
    path=Path(path)
    if path.stat().st_size>cap:raise OverflowError('bounded continuation input bytes')
    with path.open('rb') as stream:
        payload=stream.read(cap+1)
    if len(payload)>cap:raise OverflowError('bounded continuation input bytes')
    return json.loads(payload)


def sources():
    pending=['run_primitive_state_exact_row_basis_probe_v2','check_primitive_state_exact_row_basis_probe_v2',*TESTS];seen=set()
    while pending:
        name=pending.pop();path=ROOT/(name+'.py')
        if name in seen or not path.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def validate_prior():
    manifest=R.read(BASE/'publication-013/manifest.json')
    for name,h in manifest['files'].items():
        if R.sha(ROOT/name)!=h:raise ValueError('immutable publication013 '+name)
    prior=bounded_read(BASE/PRIOR_RUN/'protocol.json',LIMITS['max_metadata_bytes'])
    required=dict(schema='primitive-state-exact-row-basis-probe-v1',program=PROGRAM,scales=SCALES,
        phases=['primal_preprocessing'],language=V1.P.SPEC,gram_specs=V1.P.gram_specs(),compiler_limits=COMPILER_LIMITS,
        limits=V1.LIMITS,parallel=PARALLEL,tests=V1.TESTS,parent_publication='publication-012',
        expected_shape=dict(original_rows=5641,original_columns=1957,projected_columns=1224,omitted_columns=733),
        strategy='verify full15 column identities, exact augmented row basis, independent replay; no solver',
        solver_called=False,no_refit_or_source_selection=True,historical_development_scales=True,**FLAGS)
    if prior!=required:raise ValueError('exact prior frozen algorithm/resource contract')


def protocol(prior_hashes):
    if type(prior_hashes)is not dict or set(prior_hashes)!={'seal','receipt','review'} or any(type(h)is not str or len(h)!=64 or any(c not in '0123456789abcdef' for c in h) for h in prior_hashes.values()):
        raise ValueError('complete explicit prior-run hash bindings')
    return dict(schema='primitive-state-exact-row-basis-probe-v2',program=PROGRAM,scales=SCALES,
        phases=['primal_preprocessing'],language=V1.P.SPEC,gram_specs=V1.P.gram_specs(),compiler_limits=COMPILER_LIMITS,
        limits=LIMITS,parallel=PARALLEL,tests=TESTS,parent_publication='publication-013',
        expected_shape=dict(original_rows=5641,original_columns=1957,projected_columns=1224,omitted_columns=733),
        strategy='verify full15 column identities, exact augmented row basis, independent replay; no solver',
        solver_called=False,no_refit_or_source_selection=True,historical_development_scales=True,
        continuation=dict(prior_run=PRIOR_RUN,changed_limits=dict(max_receipt_bytes=dict(prior=V1.LIMITS['max_receipt_bytes'],current=LIMITS['max_receipt_bytes'])),
            algorithms_ordering_objective_cones_unchanged=True,comparison_location='independent whole-stage audit; worker pipeline unchanged',
            prior_run_seal_sha256=prior_hashes['seal'],
            prior_run_receipt_sha256=prior_hashes['receipt'],prior_run_review_sha256=prior_hashes['review']),**FLAGS)


def prior_hashes():
    d=BASE/PRIOR_RUN
    return dict(seal=R.sha(d/'seal.json'),receipt=R.sha(d/'receipt.json'),review=R.sha(d/'independent_verification.json'))


def freeze(directory):
    V1.require_verified_runtime();validate_cap_only_limits(LIMITS);validate_prior();d=Path(directory).resolve();d.mkdir(exist_ok=False)
    (d/'jobs').mkdir();(d/'frozen_source').mkdir();source={}
    for name in sources():
        (d/'frozen_source'/name).write_bytes((ROOT/name).read_bytes());source[name]=R.sha(ROOT/name)
    R.write(d/'protocol.json',protocol(prior_hashes()));R.write(d/'source_seal.json',source)
    R.write(d/'input.json',dict(input_sha256={n:R.sha(ROOT/n) for n in INPUTS}))
    R.write(d/'seal.json',{n+'_sha256':R.sha(d/(n+'.json')) for n in ['protocol','source_seal','input']})


def validate(directory):
    d=Path(directory);seal=R.read(d/'seal.json')
    for n in ['protocol','source_seal','input']:
        if seal[n+'_sha256']!=R.sha(d/(n+'.json')):raise ValueError('frozen seal '+n)
    if bounded_read(d/'protocol.json',LIMITS['max_metadata_bytes'])!=protocol(prior_hashes()):raise ValueError('exact cap-only frozen continuation')
    source=R.read(d/'source_seal.json')
    if set(source)!=set(sources()):raise ValueError('complete source closure')
    for n,h in source.items():
        if R.sha(ROOT/n)!=h or R.sha(d/'frozen_source'/n)!=h:raise ValueError('frozen source '+n)
    inputs=R.read(d/'input.json')['input_sha256']
    if set(inputs)!=set(INPUTS):raise ValueError('complete continuation/parent input set')
    for n,h in inputs.items():
        if R.sha(ROOT/n)!=h:raise ValueError('immutable continuation input '+n)
    validate_prior()


def compare_original_source(current,prior):
    matches={key:current.get(key)==prior.get(key) for key in SOURCE_BINDINGS}
    if not all(matches.values()) or any(key not in current or key not in prior for key in SOURCE_BINDINGS):
        raise ValueError('continuation original source/geometry mismatch')
    return matches


def compare_stage_receipts(current_projection,prior_projection,current_basis,prior_basis):
    comparison=dict(projection_intrinsic_hashes={k:current_projection.get(k)==prior_projection.get(k) for k in PROJECTION_BINDINGS},
        projection_retained_indices=current_projection.get('retained_indices')==prior_projection.get('retained_indices'),
        projection_recipes=current_projection.get('recipes')==prior_projection.get('recipes'),basis_receipt_available=current_basis is not None)
    if any(k not in current_projection or k not in prior_projection for k in PROJECTION_BINDINGS) or not all(comparison['projection_intrinsic_hashes'].values()) or not comparison['projection_retained_indices'] or not comparison['projection_recipes']:
        raise ValueError('continuation projection source/recipe mismatch')
    if current_basis is not None:
        comparison.update(basis_source_hash=current_basis.get('source_hash')==prior_basis.get('source_hash'),
            basis_ordering=current_basis.get('ordering')==prior_basis.get('ordering'),
            basis_row_order=current_basis.get('row_order')==prior_basis.get('row_order'))
        if not all(comparison[k] for k in ['basis_source_hash','basis_ordering','basis_row_order']):raise ValueError('continuation exact basis source/order mismatch')
    return comparison


def worker(job):
    V1.require_verified_runtime();d=Path(job['directory']);validate(d)
    if job.get('phase')!='primal_preprocessing' or job.get('index')!=0 or (d/'receipt.json').exists():raise ValueError('one known unsealed continuation job')
    start=time.monotonic();cpu=time.process_time();deadline=start+LIMITS['cooperative_seconds']
    out=dict(phase=job['phase'],index=0,program=PROGRAM,scales=SCALES,solver_called=False,equation_reduction_verified=False,selected_original_row_indices=None,**FLAGS)
    try:
        built=[V1.P.build(PROGRAM,X) for X in SCALES];aux=V1.P.auxiliary()
        instances=[b['instance'] for b in built]+[aux['instance']]
        blocks=[b['gram_blocks'] for b in built]+[aux['gram_blocks']]
        storage=[b['storage_blocks'] for b in built]+[aux['storage_blocks']]
        out.update(V1.TRACE.metadata(built,instances,blocks,storage))
        columns,lhs,monomials,shape,offset,_,specs=V1.S.prepare(instances,blocks,storage,gram_specs=V1.P.gram_specs(),deadline=deadline,**COMPILER_LIMITS)
        retained,recipes=V1.PROJECT.full15_recipes(shape,offset,specs,len(columns))
        if (len(columns),len(monomials),len(retained),len(recipes))!=(1957,5641,1224,733):raise ValueError('complete unchanged published primal geometry')
        compilation=V1.S.compilation_charge(instances,blocks,columns)
        out.update(complete_columns=len(columns),complete_monomials=len(monomials),projected_columns=len(retained),compilation_work_reserve=compilation,
            exact_columns_hash=R.digest([[[list(m),str(q)] for m,q in sorted(p.items())] for p in columns]),
            exact_target_hash=R.digest([[list(m),str(q)] for m,q in sorted(lhs.items())]))
        out.update(V1.process_equations(columns,lhs,monomials,retained,recipes,directory=d/'jobs',deadline=deadline,
            compilation_work_reserve=compilation,limits=LIMITS))
    except (OverflowError,TimeoutError,MemoryError,ImportError) as e:
        out.update(status='missing_resource',reason=str(e) or type(e).__name__,equation_reduction_verified=False,selected_original_row_indices=None)
    except (ValueError,TypeError,KeyError,RuntimeError,ZeroDivisionError) as e:
        out.update(status='rejected',reason=str(e) or type(e).__name__,equation_reduction_verified=False,selected_original_row_indices=None)
    out['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),pid=os.getpid())
    out['deadline_exceeded']=time.monotonic()>deadline
    validate(d);path=d/'jobs/primal.json';V1.bounded_write(path,out,LIMITS['max_metadata_bytes'])
    return dict(file=str(path.relative_to(d)),sha256=R.sha(path),status=out['status'],cost=out['cost'],**FLAGS)


def run(directory):
    V1.require_verified_runtime();d=Path(directory).resolve();validate(d)
    with (d/'run_started.json').open('x') as f:json.dump(dict(protocol_sha256=R.sha(d/'protocol.json')),f)
    tests=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=180)
    R.write(d/'tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr))
    if tests.returncode:raise ValueError('prescore cap-only continuation calibration failed')
    jobs=[dict(directory=str(d),phase='primal_preprocessing',index=0)]
    execution=V1.run_jobs(jobs,worker='run_primitive_state_exact_row_basis_probe_v2:worker',**PARALLEL)
    R.write(d/'execution.json',execution);validate(d)
    files={str(p.relative_to(d)):R.sha(p) for p in sorted(d.rglob('*')) if p.is_file() and 'frozen_source' not in p.parts}
    R.write(d/'receipt.json',dict(files_sha256=files,source_count=len(R.read(d/'source_seal.json')),solver_called=False,**FLAGS))
    print(dict(jobs=[r['status'] for r in execution['results']],**FLAGS))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory')
    args=parser.parse_args();(freeze if args.command=='freeze' else run)(args.directory)

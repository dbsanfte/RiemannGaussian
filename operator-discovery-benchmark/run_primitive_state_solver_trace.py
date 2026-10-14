"""Frozen parallel numerical diagnostics on the unchanged primitive-state cone."""
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
import cancellation_primitive_state_localizers as P
import cancellation_primitive_state_scaled_synthesis as S
import cancellation_primitive_state_scaled_dual as D
import primitive_state_solver_trace as T

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
PROGRAM=dict(target='mu',q=6,C=32,claim='critical',constraint='zero_cubic',dictionary_mode='extended',allow_constant_slack=True)
FLAGS=dict(certified=False,global_bound_proved=False,RH_proved=False,infeasibility_proved=False)
SCALES=[1,2,3,5]
COMPILER_LIMITS=dict(max_columns=2048,max_monomials=100000,max_operations=200000000,
    max_coefficient_bits=4096,max_horizon=80,max_degree=12)
TRACE_LIMITS=dict(cooperative_seconds=900,max_rows=2500,max_variables=60000,max_work=450000000,
    max_cells=4000000,max_coefficient_bits=4096,max_trace_bytes=8388608,max_log_bytes=1048576,max_metadata_bytes=65536)
PARALLEL=dict(workers=2,worker_memory_bytes=3*1024**3,memory_budget_bytes=6*1024**3,
    timeout_seconds=1800,max_jobs=2,max_result_bytes=65536)
TESTS=['test_primitive_state_solver_trace','test_check_primitive_state_solver_trace',
    'test_run_primitive_state_solver_trace','test_check_primitive_state_solver_trace_run']
INPUTS=['cancellation-arithmetic-results/publication-011/manifest.json',
    'cancellation-arithmetic-results/publication-011/report.json',
    'primitive_state_localizers_uniform_scope.txt','primitive_state_trace_resource_scope.txt']


def sources():
    pending=['run_primitive_state_solver_trace','check_primitive_state_solver_trace_run',*TESTS];seen=set()
    while pending:
        name=pending.pop();path=ROOT/(name+'.py')
        if name in seen or not path.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def validate_prior():
    for name,h in R.read(BASE/'publication-011/manifest.json')['files'].items():
        if R.sha(ROOT/name)!=h:raise ValueError('immutable publication011 '+name)


def solver_contract():
    import clarabel
    settings=clarabel.DefaultSettings();settings.max_threads=1;settings.verbose=True
    primal=T.fields(settings);primal.pop('time_limit')
    return dict(versions={n:importlib.metadata.version(n) for n in ['scipy','cvxpy','clarabel','numpy']},
        support_options=dict(threads=1,parallel=False,disp=True),primal_options=primal)


def freeze(directory):
    require_verified_runtime();validate_prior();d=Path(directory).resolve();d.mkdir(exist_ok=False)
    (d/'jobs').mkdir();(d/'frozen_source').mkdir();source={}
    for name in sources():
        (d/'frozen_source'/name).write_bytes((ROOT/name).read_bytes());source[name]=R.sha(ROOT/name)
    protocol=dict(schema='primitive-state-solver-trace-run-v1',program=PROGRAM,scales=SCALES,phases=['dual','primal'],
        language=P.SPEC,gram_specs=P.gram_specs(),compiler_limits=COMPILER_LIMITS,trace_limits=TRACE_LIMITS,
        parallel=PARALLEL,tests=TESTS,solver_contract=solver_contract(),
        strategy='two independent numerical traces on unchanged complete source equations; no exact admission',
        no_refit_or_source_selection=True,historical_development_scales=True,
        canonical_primal_matrix_independently_rebuilt=False,**FLAGS)
    R.write(d/'protocol.json',protocol);R.write(d/'source_seal.json',source)
    R.write(d/'input.json',dict(input_sha256={n:R.sha(ROOT/n) for n in INPUTS}))
    R.write(d/'seal.json',{n+'_sha256':R.sha(d/(n+'.json')) for n in ['protocol','source_seal','input']})


def validate(directory):
    d=Path(directory);seal=R.read(d/'seal.json')
    for n in ['protocol','source_seal','input']:
        if seal[n+'_sha256']!=R.sha(d/(n+'.json')):raise ValueError('frozen seal '+n)
    source=R.read(d/'source_seal.json')
    if set(source)!=set(sources()):raise ValueError('complete source closure')
    for n,h in source.items():
        if R.sha(ROOT/n)!=h or R.sha(d/'frozen_source'/n)!=h:raise ValueError('frozen source '+n)
    inputs=R.read(d/'input.json')['input_sha256']
    if set(inputs)!=set(INPUTS):raise ValueError('complete prior inputs')
    for n,h in inputs.items():
        if R.sha(ROOT/n)!=h:raise ValueError('bound input '+n)
    validate_prior()


def metadata(built,instances,blocks,storage):
    return dict(ordinary_case_hashes=[R.digest(b['instance']) for b in built],case_hashes=list(map(R.digest,instances)),
        gram_block_hashes=list(map(R.digest,blocks)),storage_block_hashes=list(map(R.digest,storage)),
        gram_archive_hashes=[R.digest(b['gram_archive']) for b in built],factor_archive_hashes=[R.digest(b['factor_archive']) for b in built],
        divisor_archive_hashes=[R.digest(b['divisor_archive']) for b in built],cell_archive_hashes=[R.digest(b['cell_archive']) for b in built],
        primitive_state_archive_hashes=[R.digest([{k:v for k,v in row.items() if k!='polynomial_sha256'} for row in b['primitive_state_archive']]) for b in built],
        primitive_source_hashes=[R.digest(b['primitive_sources']) for b in built],multiplier_source_hashes=[R.digest(b['multiplier_sources']) for b in built],
        dictionary_sha256=built[0]['dictionary_sha256'],gram_specs=P.gram_specs())


def bounded_write(path,value,cap):
    payload=json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()
    if len(payload)>cap:raise OverflowError('bounded diagnostic artifact bytes')
    temporary=Path(str(path)+'.tmp');temporary.write_bytes(payload);os.replace(temporary,path)


def worker(job):
    require_verified_runtime();d=Path(job['directory']);validate(d);phase=job['phase']
    if phase not in ['dual','primal'] or (d/'receipt.json').exists():raise ValueError('known unsealed trace job')
    start=time.monotonic();cpu=time.process_time();deadline=start+TRACE_LIMITS['cooperative_seconds']
    out=dict(phase=phase,index=job['index'],program=PROGRAM,scales=SCALES,**FLAGS)
    try:
        built=[P.build(PROGRAM,X) for X in SCALES];aux=P.auxiliary()
        instances=[b['instance'] for b in built]+[aux['instance']]
        blocks=[b['gram_blocks'] for b in built]+[aux['gram_blocks']]
        storage=[b['storage_blocks'] for b in built]+[aux['storage_blocks']]
        out.update(metadata(built,instances,blocks,storage))
        columns,lhs,monomials,shape,offset,_,specs=S.prepare(instances,blocks,storage,gram_specs=P.gram_specs(),deadline=deadline,**COMPILER_LIMITS)
        nn,rr,layout=D.classify(columns,shape,offset,specs)
        reduced,rnn,rrr,keep,redundancy=D.restricted_columns(columns,offset,nn,rr,layout)
        out.update(complete_monomials=len(monomials),complete_columns=len(columns),compilation_work_reserve=S.compilation_charge(instances,blocks,columns),
            exact_columns_hash=R.digest([[[list(m),str(q)] for m,q in sorted(p.items())] for p in columns]),
            exact_target_hash=R.digest([[list(m),str(q)] for m,q in sorted(lhs.items())]))
        path=d/f'jobs/{phase}-trace.json';log=d/f'jobs/{phase}-native.log';checkpoint=d/f'jobs/{phase}-progress.json'
        common=dict(deadline=deadline,max_cells=TRACE_LIMITS['max_cells'],max_coefficient_bits=4096,
            log_path=str(log),max_log_bytes=TRACE_LIMITS['max_log_bytes'],checkpoint_path=str(checkpoint))
        if phase=='dual':
            trace=T.trace_support(reduced,lhs,monomials,rnn,rrr,max_rows=2500,max_variables=60000,max_work=450000000,**common)
        else:
            trace=T.trace_primal(columns,lhs,monomials,shape,offset,specs,max_operations=200000000,**common)
        bounded_write(path,trace,TRACE_LIMITS['max_trace_bytes'])
        out.update(status='trace_available',trace_file=str(path.relative_to(d)),trace_sha256=R.sha(path))
    except (OverflowError,TimeoutError,MemoryError,ImportError) as e:
        out.update(status='missing_resource',reason=str(e) or type(e).__name__)
    except (ValueError,TypeError,KeyError,RuntimeError,ZeroDivisionError) as e:
        out.update(status='rejected',reason=str(e) or type(e).__name__)
    out['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),pid=os.getpid())
    validate(d);path=d/f'jobs/{phase}.json';bounded_write(path,out,TRACE_LIMITS['max_metadata_bytes'])
    return dict(file=str(path.relative_to(d)),sha256=R.sha(path),status=out['status'],cost=out['cost'],**FLAGS)


def run(directory):
    require_verified_runtime();d=Path(directory).resolve();validate(d)
    with (d/'run_started.json').open('x') as f:json.dump(dict(protocol_sha256=R.sha(d/'protocol.json')),f)
    tests=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=180)
    R.write(d/'tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr))
    if tests.returncode:raise ValueError('prescore calibration failed')
    jobs=[dict(directory=str(d),phase=p,index=i) for i,p in enumerate(['dual','primal'])]
    execution=run_jobs(jobs,worker='run_primitive_state_solver_trace:worker',**PARALLEL)
    R.write(d/'execution.json',execution);validate(d)
    files={str(p.relative_to(d)):R.sha(p) for p in sorted(d.rglob('*')) if p.is_file() and 'frozen_source' not in p.parts}
    R.write(d/'receipt.json',dict(files_sha256=files,source_count=len(R.read(d/'source_seal.json')),**FLAGS))
    print(dict(jobs=[r['status'] for r in execution['results']],**FLAGS))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory')
    args=parser.parse_args();(freeze if args.command=='freeze' else run)(args.directory)

"""Frozen multicore search adding complete divisor-cell/prefix interactions.
A finite LP certificate needs exact independent checking and unchanged final
transfer. Failure triggers one native full-Gram separator attempt, never an
infeasibility assertion from floating failure. No mathematical global promotion.
"""
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
import cancellation_divisor_cell_language as P

FLAGS=dict(global_bound_proved=False,RH_proved=False)
ROOT=Path(__file__).resolve().parent
TESTS=['test_cancellation_divisor_cells','test_check_cancellation_divisor_cells','test_cancellation_divisor_cell_language','test_cancellation_native_gram_dual','test_run_divisor_cell_search']
LIMITS=dict(R.DEFAULT_LIMITS,time_limit=180,max_columns=2048,max_monomials=100000)
DUAL_LIMITS=dict(time_limit=180,max_rows=2500,max_variables=60000,max_work=400000000,
                 max_cells=4000000,max_denominator=2**4096,max_coefficient_bits=4096,
                 max_columns=2048,max_monomials=100000,max_operations=200000000,max_horizon=80,max_degree=12)

def sources():
    pending=['run_divisor_cell_search','check_divisor_cell_search',*TESTS];seen=set()
    while pending:
        name=pending.pop();f=ROOT/(name+'.py')
        if name in seen or not f.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(f.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0]for a in node.names)
            elif isinstance(node,ast.ImportFrom)and node.module:pending.append(node.module.split('.')[0])
    return sorted(x+'.py'for x in seen)

def freeze(directory):
    require_verified_runtime();d=Path(directory).resolve()
    for name in ['check_divisor_cell_search.py','check_cancellation_divisor_cells.py','cancellation_native_gram_dual.py',*(t+'.py'for t in TESTS)]:
        if not (ROOT/name).is_file():raise FileNotFoundError(name)
    programs=R.read(ROOT/'detector_resource_search.json')['programs']
    spec=dict(schema=1,language=P.SPEC,dictionary=P.descriptors(),programs=programs,
        training_scales=[1,2,3,5],final_scales=[8,13],limits=LIMITS,dual_limits=DUAL_LIMITS,
        solver='structural LP with native exact reconstruction; Grams fixed zero',
        dual_rule='one native diagonal-moment search whose success separates the full five-atom Gram cone, if critical LP is not accepted',
        tests=TESTS,parallel=dict(workers=2,worker_memory_bytes=2*1024**3,memory_budget_bytes=4*1024**3,
            timeout_seconds=600,max_jobs=64,max_result_bytes=65536),
        audit_seconds=180,final_refit=False,no_actual_signed_response_inputs=True,
        conditioning='adaptive language after divisor-localizer exact obstruction; all 18 declared contexts retained without candidate scores',
        evaluation_scope='unchanged-weight transfer for this new language; scales reused from prior languages, not unseen arithmetic data',
        auxiliary='same necessary gamma=0 row; normalized new groups have fully charged O(X) formal scalars, not zero scalars',
        recovery='full original signed defect; every divisor source pair, cell complement, cross product and unit boundary retained',
        runtime=dict(python=sys.version,packages={n:importlib.metadata.version(n)for n in ('numpy','scipy','python-flint')}),
        **FLAGS)
    inputs={name:R.sha(ROOT/name)for name in ['cancellation-arithmetic-results/publication-003/manifest.json',
        'detector-performance-results/publication-001/manifest.json',
        'cancellation-arithmetic-results/divisor-coupling-calibration-001/root_verification.json',
        'cancellation-arithmetic-results/divisor-localizer-probe-001/independent_verification.json',
        'cancellation-arithmetic-results/divisor-localizer-scope-001/uniform_scope_independent_review.json',
        'cancellation_divisor_cell_language_scope.txt',
        'detector_resource_search.json']}
    # Published inputs are checked before building the new cone.
    for path in list(inputs)[:2]:
        for name,h in R.read(ROOT/path)['files'].items():
            if R.sha(ROOT/name)!=h:raise ValueError('earlier published file changed: '+name)
    d.mkdir(parents=True,exist_ok=False);(d/'frozen_source').mkdir();(d/'jobs').mkdir()
    hashes={}
    for name in sources():
        data=(ROOT/name).read_bytes();(d/'frozen_source'/name).write_bytes(data);hashes[name]=R.sha(ROOT/name)
    R.write(d/'protocol.json',spec);R.write(d/'input.json',dict(input_sha256=inputs));R.write(d/'source_seal.json',hashes)
    R.write(d/'seal.json',dict(protocol_sha256=R.sha(d/'protocol.json'),source_seal_sha256=R.sha(d/'source_seal.json'),input_sha256=R.sha(d/'input.json')))
    return d

def validate(d):
    R.validate_sources(d)
    for name,h in R.read(Path(d)/'input.json')['input_sha256'].items():
        if R.sha(ROOT/name)!=h:raise ValueError('bound input changed: '+name)

def worker(job):
    require_verified_runtime();d=Path(job['directory']);validate(d)
    if (d/'receipt.json').exists():raise FileExistsError('sealed run is immutable')
    spec=R.read(d/'protocol.json');phase=job['phase'];index=job['index']
    from check_cancellation_divisor_cells import build, auxiliary, descriptors
    import check_grouped_arithmetic_sparse as CHECK
    from cancellation_sparse_synthesis import synthesize
    from grouped_arithmetic_sparse import instantiate_details
    from cancellation_native_gram_dual import propose
    start=time.monotonic();cpu=time.process_time();out=dict(phase=phase,index=index,refitted=False,**FLAGS)
    try:
        if phase=='train':program=spec['programs'][index];scales=spec['training_scales']
        else:
            if R.sha(d/'candidate_seal.json')!=job['candidate_seal_sha256']:raise ValueError('candidate seal changed')
            plan=R.read(d/'candidate_seal.json')
            if R.sha(d/'training.json')!=plan['training_sha256']:raise ValueError('training changed')
            followup=plan['jobs'][index];program=followup['program'];scales=[followup['X']]if phase=='final'else spec['training_scales']
            if followup['phase']!=phase:raise ValueError('followup phase binding')
        built=[build(program,X)for X in scales];instances=[b['instance']for b in built]
        out.update(program=program,scales=scales,ordinary_case_hashes=list(map(R.digest,instances)),
            factor_archive_hashes=[R.digest(b['factor_archive'])for b in built],
            divisor_archive_hashes=[R.digest(b['divisor_archive'])for b in built],
            cell_archive_hashes=[R.digest(b['cell_archive'])for b in built],dictionary_sha256=R.digest(descriptors()))
        if phase in ('train','dual')and program['constraint']=='zero_cubic':instances.append(auxiliary()['instance'])
        out['case_hashes']=list(map(R.digest,instances))
        if phase=='train':
            result=synthesize(instances,allow_constant_slack=program['allow_constant_slack'],**spec['limits'])
            check=CHECK.verify_joint_result(instances,result,allow_constant_slack=program['allow_constant_slack'],expected_instance_sha256=out['case_hashes'],time_limit=spec['audit_seconds'])
        elif phase=='final':
            path=d/followup['attempt_file']
            if R.sha(path)!=followup['attempt_sha256']:raise ValueError('candidate attempt changed')
            attempt=R.read(path);weights=attempt['synthesis']['weights']
            details=instantiate_details(instances[0],weights,allow_constant_slack=program['allow_constant_slack'],**spec['limits'])
            result=dict(status='finite_certificate',weights=weights,certificates=[details['certificate']],
                constant_slacks=[details['constant_slack']]if program['allow_constant_slack']else [],**FLAGS)
            check=CHECK.verify_joint_result(instances,result,allow_constant_slack=program['allow_constant_slack'],expected_instance_sha256=out['case_hashes'],time_limit=spec['audit_seconds'])
            out.update(weights_sha256=R.digest(weights),instantiation=details['diagnostics'])
        else:
            result=propose(instances,scales,**spec['dual_limits'])
            check=result['independent_check']if result.get('certified')else dict(verified=False,status=result['status'],**FLAGS)
        out.update(status=result['status'],synthesis=result,independent_check=check)
        if phase!='train'and R.sha(d/'candidate_seal.json')!=job['candidate_seal_sha256']:raise ValueError('candidate seal changed during evaluation')
    except (OverflowError,TimeoutError,MemoryError,ImportError)as e:out.update(status='missing_resource',reason=str(e)or type(e).__name__)
    except (ValueError,TypeError,KeyError,ZeroDivisionError,RuntimeError)as e:out.update(status='rejected',reason=str(e)or type(e).__name__)
    out['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())),pid=os.getpid())
    validate(d);filename=f'jobs/{phase}-{index:03d}.json';R.write(d/filename,out)
    return dict(file=filename,sha256=R.sha(d/filename),status=out['status'],cost=out['cost'],**FLAGS)

def run(directory):
    require_verified_runtime()
    d=Path(directory).resolve();validate(d);spec=R.read(d/'protocol.json')
    if (d/'tests.json').exists():raise FileExistsError('run already started')
    test=subprocess.run([sys.executable,'-B','-m','unittest',*spec['tests']],cwd=ROOT,capture_output=True,text=True,timeout=120)
    R.write(d/'tests.json',dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr))
    if test.returncode:raise ValueError('calibration tests failed')
    train=run_jobs([dict(directory=str(d),phase='train',index=i)for i in range(len(spec['programs']))],worker='run_divisor_cell_search:worker',**spec['parallel'])
    R.write(d/'training.json',train);jobs=[]
    for i,receipt in enumerate(train['results']):
        if receipt['status']=='available'and receipt['value']['status']=='finite_certificate':
            val=receipt['value'];attempt=R.read(d/val['file'])
            if R.sha(d/val['file'])!=val['sha256']or not attempt['independent_check']['verified']:raise ValueError('training receipt binding')
            jobs.extend(dict(phase='final',program=spec['programs'][i],X=X,attempt_file=val['file'],attempt_sha256=val['sha256'])for X in spec['final_scales'])
        elif spec['programs'][i]['claim']=='critical':jobs.append(dict(phase='dual',program=spec['programs'][i]))
    R.write(d/'candidate_seal.json',dict(training_sha256=R.sha(d/'training.json'),jobs=jobs))
    seal_hash=R.sha(d/'candidate_seal.json')
    follow=run_jobs([dict(directory=str(d),phase=j['phase'],index=i,candidate_seal_sha256=seal_hash)for i,j in enumerate(jobs)],worker='run_divisor_cell_search:worker',**spec['parallel'])
    if R.sha(d/'candidate_seal.json')!=seal_hash:raise ValueError('candidate plan changed')
    R.write(d/'followup.json',follow);validate(d)
    files={str(p.relative_to(d)):R.sha(p)for p in sorted(d.rglob('*.json'))}
    R.write(d/'receipt.json',dict(files_sha256=files,source_count=len(R.read(d/'source_seal.json')),refitted=False,**FLAGS))
    print(json.dumps(dict(directory=str(d),training=[r.get('value',r).get('status')for r in train['results']],followup=[r.get('value',r).get('status')for r in follow['results']],**FLAGS),indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory');args=parser.parse_args()
    (freeze if args.command=='freeze'else run)(args.directory)

"""Preregister and run all primitive-family/state-pair witness diagnostics."""
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
import cancellation_primitive_state_localizers as L
import primitive_state_localizer_probe as P

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
PARENT=BASE/'affine-storage-search-001'
PUBLICATION=BASE/'publication-009'
FLAGS=dict(P.FLAGS)
TESTS=['test_cancellation_primitive_state_localizers','test_check_cancellation_primitive_state_localizers','test_primitive_state_localizer_probe']
PROGRAM=dict(target='mu',q=6,C=32,claim='critical',constraint='zero_cubic',dictionary_mode='extended',allow_constant_slack=True)
SCALES=[1,2,3,5]
LIMITS=dict(max_horizon=80,max_operations=200000000,max_terms=100000,max_coefficient_bits=4096)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=1200,max_jobs=1,max_result_bytes=65536)
PARENT_RESULT='jobs/dual-000.json'


def sources():
    pending=['run_primitive_state_localizer_probe','check_primitive_state_localizer_probe_run',*TESTS];seen=set()
    while pending:
        name=pending.pop();p=ROOT/(name+'.py')
        if name in seen or not p.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(p.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def bind(base,hashes):
    for n,h in hashes.items():
        if R.sha(base/n)!=h:raise ValueError('immutable primitive-state evidence '+str(base/n))


def input_names():
    paths=[PARENT/n for n in [PARENT_RESULT,'protocol.json','source_seal.json','receipt.json','independent_verification.json']]
    paths += [PUBLICATION/n for n in ['manifest.json','report.json']]
    paths += [ROOT/n for n in ['primitive_state_localizers_uniform_scope.txt','anchored_storage_resource_authorization.txt']]
    return sorted(str(p.relative_to(ROOT)) for p in paths)


def parent_bindings():
    bind(ROOT,R.read(PUBLICATION/'manifest.json')['files'])
    bind(PARENT,R.read(PARENT/'receipt.json')['files_sha256'])
    source=R.read(PARENT/'source_seal.json');bind(ROOT,source);bind(PARENT/'frozen_source',source)
    review=R.read(PARENT/'independent_verification.json');bind(PARENT,review['input_sha256'])
    checked={r['file']:r['proof'] for r in review['checks']}
    if review.get('all_passed')is not True or checked[PARENT_RESULT].get('verified')is not True or review['decision']['dual_status']!='exact_separator':
        raise ValueError('independently admitted complete affine separator')
    prior=R.read(PARENT/PARENT_RESULT)
    if prior['status']!='exact_separator' or prior['synthesis'].get('certified')is not True or prior['program']!=PROGRAM or prior['scales']!=SCALES:
        raise ValueError('fixed complete parent dual')
    return prior


def protocol():
    return dict(schema=1,grammar=L.SPEC,diagnostic=P.SPEC,program=PROGRAM,scales=SCALES,
                per_instance_build_limits=LIMITS,diagnostic_limits=LIMITS,parallel=PARALLEL,
                cooperative_seconds=360,source_json_bytes=67108864,result_json_bytes=8388608,
                tests=TESTS,descriptor_count=210,all_source_families=True,
                no_new_floating_search=True,no_actual_signed_response_inputs=True,
                decisions=dict(witness_invalid_for_localizer_cone='consider full augmented-cone search; target feasibility unproved',
                    witness_extends_to_localizer_cone='same exact witness excludes all declared additional relations on this grid',
                    unknown_missing_coordinates='a moment extension is needed; no zero imputation'),**FLAGS)


def freeze(directory):
    require_verified_runtime();parent_bindings()
    d=Path(directory).resolve();d.mkdir(parents=True,exist_ok=False);(d/'frozen_source').mkdir()
    hashes={}
    for n in sources():
        (d/'frozen_source'/n).write_bytes((ROOT/n).read_bytes());hashes[n]=R.sha(ROOT/n)
    test=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=180)
    R.write(d/'tests.json',dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr))
    if test.returncode:raise ValueError('complete primitive-state prescore calibration failed')
    R.write(d/'protocol.json',protocol());R.write(d/'source_seal.json',hashes)
    R.write(d/'input.json',dict(input_sha256={n:R.sha(ROOT/n) for n in input_names()}))
    R.write(d/'seal.json',{n+'_sha256':R.sha(d/(n+'.json')) for n in ['protocol','source_seal','input','tests']})
    return dict(directory=str(d),sources=len(hashes),scored=False)


def validate(directory):
    d=Path(directory);seal=R.read(d/'seal.json')
    for n in ['protocol','source_seal','input','tests']:
        if seal[n+'_sha256']!=R.sha(d/(n+'.json')):raise ValueError('sealed localizer preregistration '+n)
    source=R.read(d/'source_seal.json')
    if set(source)!=set(sources()):raise ValueError('complete source closure')
    bind(ROOT,source);bind(d/'frozen_source',source)
    inputs=R.read(d/'input.json')['input_sha256']
    if set(inputs)!=set(input_names()):raise ValueError('complete parent and scope inputs')
    bind(ROOT,inputs)
    if R.read(d/'protocol.json')!=protocol() or R.read(d/'tests.json')['returncode']!=0:raise ValueError('known frozen grammar and calibration')
    return parent_bindings()


def geometry(prior):
    cases=[];blocks=[];archives=[]
    for X in SCALES:
        base=L.BASE.build_blocks(X,**LIMITS)
        extra=L.build_additions(X,blocks=base['blocks'],**LIMITS)
        cases.append(dict(X=X,additions=extra));blocks.append(base['blocks']);archives.append(base['archive'])
    blocks.append(dict(full_child=[],full_parent=[]))
    metadata=dict(gram_block_hashes=list(map(R.digest,blocks)),gram_archive_hashes=list(map(R.digest,archives)))
    for key,value in metadata.items():
        if prior[key]!=value:raise ValueError('same complete original source '+key)
    horizons=[4*X-1 for X in SCALES]+[1]
    groups=[r['additions']['relation_groups'] for r in cases]+[[[] for _ in range(210)]]
    instances=[dict(target='mu',horizon=H,lhs=[],square_groups=[],relation_groups=rows) for H,rows in zip(horizons,groups)]
    source=dict(cases=cases,scales=SCALES,horizons=horizons,descriptor_sha256=R.digest(L.additions()['relation']),**metadata)
    return source,instances


def bounded_write(path,value,limit):
    if len(json.dumps(value,sort_keys=True,separators=(',',':')).encode())>limit:raise OverflowError('bounded diagnostic artifact '+path.name)
    temporary=path.with_suffix('.tmp');R.write(temporary,value);os.replace(temporary,path)


def worker(job):
    require_verified_runtime();d=Path(job['directory']);prior=validate(d)
    if (d/'result.json').exists() or (d/'source.json').exists():raise FileExistsError('exclusive localizer diagnostic')
    start=time.monotonic();cpu=time.process_time();source,instances=geometry(prior)
    bounded_write(d/'source.json',source,67108864)
    probe=P.probe(instances,L.additions()['relation'],prior['synthesis'],deadline=start+360,**LIMITS)
    if time.monotonic()-start>360:raise TimeoutError('primitive-state diagnostic cooperative deadline')
    result=dict(status=probe['status'],probe=probe,program=PROGRAM,scales=SCALES,
                grammar_sha256=R.digest(L.SPEC),source_sha256=R.sha(d/'source.json'),
                parent_result_sha256=R.sha(PARENT/PARENT_RESULT),no_new_floating_search=True,**FLAGS)
    result['cost']=dict(elapsed_seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,pid=os.getpid(),observed_threads_at_completion=len(list(Path('/proc/self/task').iterdir())))
    validate(d);bounded_write(d/'result.json',result,8388608)
    return dict(file='result.json',sha256=R.sha(d/'result.json'),status=result['status'],counts=probe['counts'],cost=result['cost'],**FLAGS)


def run(directory):
    require_verified_runtime();d=Path(directory).resolve();validate(d)
    with (d/'run_started.json').open('x') as stream:json.dump(dict(protocol_sha256=R.sha(d/'protocol.json')),stream)
    execution=run_jobs([dict(directory=str(d))],worker='run_primitive_state_localizer_probe:worker',**PARALLEL)
    R.write(d/'execution.json',execution);validate(d)
    R.write(d/'receipt.json',dict(files_sha256={str(p.relative_to(d)):R.sha(p) for p in sorted(d.rglob('*.json'))},source_count=len(R.read(d/'source_seal.json')),no_new_floating_search=True,**FLAGS))
    return dict(process_status=execution['results'][0]['status'],result=execution['results'][0].get('value'))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory');args=parser.parse_args()
    print(json.dumps((freeze if args.command=='freeze' else run)(args.directory)))

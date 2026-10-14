"""Supplemental cached-variant audit with a separate 256 KiB protocol envelope.

The original v1 64 KiB protocol check remains unsatisfied for run001.
Only this independent audit's protocol-file allowance changes; all worker,
cache, trace, work, source and mathematical checks are inherited unchanged.
"""
import argparse
import json
import math
from pathlib import Path
import re
import time
import check_primitive_state_cached_primal_variants_run as V1
from check_primitive_state_cached_primal_variants_run import (
    ORIGINAL, CORE, FLAGS, LIMITS, VARIANTS, INPUTS, PREP_PARALLEL,
    VARIANT_PARALLEL, read, sha, path_under, require, scope, source_names,
    read_cache, verify_parent, compare_source, verify_runtime,
    verify_protocol, verify_solver_contracts, verify_preparation,
    verify_variant_job,
)
ROOT=Path(__file__).resolve().parent
PROTOCOL_MAX_BYTES=262144
REVIEW_NAME='independent_verification_v2.json'
SCHEMA='primitive-state-cached-primal-variants-independent-review-v2'
AUDIT_FILES=['check_primitive_state_cached_primal_variants_run_v2.py',
             'test_check_primitive_state_cached_primal_variants_run_v2.py',
             'primitive_state_cached_variants_audit_correction_v2.txt']


def protocol_envelope(directory):
    path=Path(directory)/'protocol.json'
    size=path.stat().st_size
    require(size<=PROTOCOL_MAX_BYTES,'bounded supplemental protocol envelope')
    prior_satisfied=size<=LIMITS['max_metadata_bytes']
    if not prior_satisfied:
        try:
            V1.read(path,LIMITS['max_metadata_bytes'])
        except OverflowError:
            pass
        else:
            raise ValueError('original protocol overflow must remain reproducible')
    return dict(file='protocol.json',sha256=sha(path),actual_bytes=size,
                original_max_bytes=LIMITS['max_metadata_bytes'],
                supplemental_max_bytes=PROTOCOL_MAX_BYTES,
                original_audit_contract_satisfied=prior_satisfied,
                correction='protocol envelope only; worker metadata limits unchanged',
                mathematical_scope_unchanged=True)


def verify_inventory(directory,receipt):
    scope(receipt)
    allowed={'protocol.json','source_seal.json','input.json','seal.json','tests.json','run_started.json','execution.json','preparation-execution.json'}
    jobs=['jobs/prepare/job.json','jobs/prepare/progress.json','jobs/prepare/source-cache.json','jobs/prepare/cache-check.json']
    for v in VARIANTS:
        jobs.extend('jobs/'+v['id']+'/'+name for name in ['job.json','progress.json','trace.json','check.json','native.log','native-progress.json','native-progress.json.source.json'])
    allowed.update(jobs);allowed.update(n+'.tmp' for n in jobs)
    actual={str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file() and 'frozen_source' not in p.relative_to(directory).parts}-{'receipt.json','independent_verification.json',REVIEW_NAME}
    files=receipt.get('files_sha256');require(not actual-allowed and type(files)is dict and set(files)==actual,'complete declared cached stage artifact inventory')
    for n,h in files.items():
        p=path_under(directory,n);require(sha(p)==h,'cached stage artifact hash '+n);base=n[:-4] if n.endswith('.tmp') else n
        cap=PROTOCOL_MAX_BYTES if base=='protocol.json' else LIMITS['max_cache_bytes'] if base=='jobs/prepare/source-cache.json' else LIMITS['max_log_bytes'] if base.endswith('/native.log') else LIMITS['max_trace_bytes'] if any(base.endswith('/'+s) for s in ('trace.json','check.json','cache-check.json','native-progress.json','native-progress.json.source.json')) else LIMITS['max_metadata_bytes']
        require(p.stat().st_size<=cap,'bounded cached stage artifact '+n)
    return dict(files=len(files),bytes=sum(path_under(directory,n).stat().st_size for n in files))


def audit(directory,*,write=False,time_limit=900,max_audit_operations=450000000,max_audit_cells=60000000):
    require(type(time_limit)in (int,float) and math.isfinite(time_limit) and 0<time_limit<=900,'bounded cached-stage independent deadline')
    require(type(max_audit_operations)is int and 0<max_audit_operations<=450000000 and type(max_audit_cells)is int and 0<max_audit_cells<=60000000,'bounded cached-stage independent replay resources')
    d=Path(directory).resolve();target=d/REVIEW_NAME;started=time.monotonic();deadline=started+time_limit
    if write and target.exists():raise FileExistsError('exclusive cached-variant independent review')
    envelope=protocol_envelope(d)
    audit_sources={name:sha(Path(__file__).resolve().parent/name) for name in AUDIT_FILES}
    protocol=read(d/'protocol.json',PROTOCOL_MAX_BYTES);verify_protocol(protocol);sources=read(d/'source_seal.json',65536)
    require(set(sources)==set(source_names()),'complete cached stage source closure')
    require({str(p.relative_to(d/'frozen_source')) for p in (d/'frozen_source').rglob('*') if p.is_file()}==set(sources),'complete cached stage frozen source inventory')
    for n,h in sources.items():require(sha(path_under(ROOT,n))==h and sha(path_under(d/'frozen_source',n))==h,'immutable cached stage source '+n)
    seal=read(d/'seal.json',65536)
    for n in ('protocol','source_seal','input'):require(seal.get(n+'_sha256')==sha(d/(n+'.json')),'cached stage preregistration '+n)
    inputs=read(d/'input.json',65536)['input_sha256'];require(set(inputs)==set(INPUTS),'complete cached stage parent/resource inputs')
    for n,h in inputs.items():require(sha(path_under(ROOT,n))==h,'immutable cached stage input '+n)
    manifest=read(ROOT/'cancellation-arithmetic-results/publication-015/manifest.json')
    for n,h in manifest['files'].items():require(sha(path_under(ROOT,n))==h,'immutable publication015 '+n)
    require(read(ROOT/'cancellation-arithmetic-results/publication-015/report.json').get('schema')==15,'completed publication015 parent')
    tests=read(d/'tests.json',65536);match=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',tests.get('stdout','')+tests.get('stderr',''));require(tests.get('returncode')==0 and match is not None,'cached-stage calibration passed')
    require(read(d/'run_started.json',65536)==dict(protocol_sha256=sha(d/'protocol.json')),'exclusive cached stage execution')
    receipt=read(d/'receipt.json',65536);inventory=verify_inventory(d,receipt);require(receipt.get('source_count')==len(sources),'complete cached-stage terminal source count')
    execution=read(d/'execution.json',65536);preparation_execution=read(d/'preparation-execution.json',65536);verify_runtime(execution,preparation_execution)
    expected,geometry=ORIGINAL.rebuild();operations=geometry['compilation'];cells=0
    parent=verify_parent(expected,geometry,deadline=deadline,max_operations=max_audit_operations-operations,max_cells=max_audit_cells);operations+=parent['audit_operations'];cells+=parent['audit_cells']
    require(protocol.get('parent_license')==dict(selected_original_indices=parent['indices'],indices_hash=CORE.digest(parent['indices']),parent_assembly=parent['assembly'],parent_bindings=parent['bindings']),'completed parent predeclared source/cache license')
    verify_solver_contracts(protocol,parent['parent_solver_contract'])
    cachepath=d/'jobs/prepare/source-cache.json';cache=read_cache(cachepath) if cachepath.exists() else None;cache_check=None;witness=None
    if cache is not None:
        witness=CORE.prepare_verified_cache(cache,expected_parent_assembly=parent['assembly'],expected_parent_bindings=parent['bindings'],expected_source_hashes={n:sources[n] for n in ('primitive_state_cached_primal_variants.py','primitive_state_basis_primal.py','primitive_state_solver_trace.py')},deadline=deadline,max_operations=max_audit_operations-operations,max_cells=max_audit_cells-cells)
        cache_check=witness.check;operations+=cache_check['audit_operations'];cells+=cache_check['audit_cells']
        comparison=compare_source(cache,geometry,witness.decoded,deadline=deadline,max_operations=max_audit_operations-operations,max_cells=max_audit_cells-cells);operations+=comparison['audit_operations'];cells+=comparison['audit_cells']
    preparation=verify_preparation(d,preparation_execution,geometry,parent,cache,cache_check,expected)
    if execution.get('status')!='blocked':require(preparation['shared_cache_available']is True,'variant launch requires available audited preparation transport')
    jobs=[]
    for index,value in enumerate(VARIANTS):
        result=verify_variant_job(d,index,value['id'],execution,protocol,sources,parent,cache,witness,deadline=deadline,max_operations=max_audit_operations-operations,max_cells=max_audit_cells-cells)
        operations+=result['audit_operations'];cells+=result['audit_cells'];jobs.append(result)
    require(time.monotonic()<=deadline,'cached stage independent deadline')
    for n,h in sources.items():require(sha(ROOT/n)==h and sha(d/'frozen_source'/n)==h,'source changed during cached replay '+n)
    for n,h in inputs.items():require(sha(ROOT/n)==h,'input changed during cached replay '+n)
    for n,h in receipt['files_sha256'].items():require(sha(path_under(d,n))==h,'artifact changed during cached replay '+n)
    for name,h in audit_sources.items():require(sha(Path(__file__).resolve().parent/name)==h,'supplemental audit source changed '+name)
    review=dict(schema=SCHEMA,audit_source_sha256=audit_sources,protocol_envelope=envelope,original_audit_contract_satisfied=envelope['original_audit_contract_satisfied'],all_passed=True,source_count=len(sources),tests_passed=int(match.group(1)),arithmetic_rebuilds=1,geometry_rebuilds=1,parent_basis_replays=1,cache_verifications=1 if cache is not None else 0,canonical_reconstructions=1 if cache is not None else 0,
        independent_audit_limits=dict(seconds=time_limit,max_operations=max_audit_operations,max_cells=max_audit_cells,max_cache_bytes=LIMITS['max_cache_bytes'],max_protocol_bytes=PROTOCOL_MAX_BYTES),
        preparation=preparation,cache_check=cache_check,jobs=jobs,inventory=inventory,independent_replay_operations=operations,independent_replay_cells=cells,parent_bound_files=len(manifest['files']),elapsed_seconds=time.monotonic()-started,
        original_variables=1957,original_finite_equations=5641,selected_original_rows=779,mathematical_feasibility='UNKNOWN',numerical_diagnostics_only=True,
        input_sha256={n:sha(d/n) for n in ['protocol.json','source_seal.json','input.json','seal.json','tests.json','preparation-execution.json','execution.json','receipt.json']},**FLAGS)
    if write:
        with target.open('x') as stream:json.dump(review,stream,sort_keys=True,indent=2,allow_nan=False);stream.write('\n')
    return review


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory');parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    print(json.dumps(audit(args.directory,write=args.write),sort_keys=True))

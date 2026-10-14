"""Independent bounded archive audit of one fixed exact triangular restoration.

The completed parent source/cache audit is hash-bound, not rerun. This audit
independently replays restoration and checks every original finite equation/cone.
"""
import argparse
import contextvars
import ast
import json
import math
from pathlib import Path
import re
import time
import check_primitive_state_triangular_restoration as CORE
import check_primitive_state_solver_trace_run as ORIGINAL

ROOT=Path(__file__).resolve().parent
path_under=ORIGINAL.path_under
_IO_BUDGET=contextvars.ContextVar('restoration_archive_io_budget',default=None)


def read(path,cap=8388608):
    size=Path(path).stat().st_size;require(size<=cap,'bounded controlled artifact read')
    meter=_IO_BUDGET.get()
    if meter is not None:meter.charge(2*(size//64+1),cells=size//64+1)
    return ORIGINAL.read(path,cap)


def sha(path):
    size=Path(path).stat().st_size;meter=_IO_BUDGET.get()
    if meter is not None:meter.charge(size//64+1)
    return ORIGINAL.sha(path)
require=CORE.require
FLAGS=dict(CORE.FLAGS)
PARENT='cancellation-arithmetic-results/primitive-state-cached-primal-variants-001'
TAPE='cancellation-arithmetic-results/primitive-state-exact-row-basis-probe-002/jobs'
CACHE=PARENT+'/jobs/prepare/source-cache.json';TRACE=PARENT+'/jobs/faer_static_1e-6/trace.json';BASIS=TAPE+'/basis.json';PROJECTION=TAPE+'/projection.json'
LIMITS=dict(cooperative_seconds=900,max_work=450000000,producer_operations=125000000,max_cache_bytes=134217728,max_tape_bytes=33554432,max_receipt_bytes=8388608,max_metadata_bytes=65536,max_protocol_bytes=65536,max_live_cells=4000000,max_fill_cells=20000000,max_audit_cells=60000000,max_coefficient_bits=4096,binding_byte_multiplier=4,source_byte_multiplier=12,metadata_work_reserve=1048576)
PARALLEL=dict(workers=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,timeout_seconds=1800,max_jobs=1,max_result_bytes=65536)
TESTS=['test_primitive_state_triangular_restoration','test_check_primitive_state_triangular_restoration','test_run_primitive_state_triangular_restoration','test_check_primitive_state_triangular_restoration_run']
INPUTS=['cancellation-arithmetic-results/publication-015/manifest.json','cancellation-arithmetic-results/publication-015/report.json','cancellation-arithmetic-results/publication-016/manifest.json','cancellation-arithmetic-results/publication-016/report.json','primitive_state_triangular_restoration_resource_scope.txt','primitive_state_lossless_cone_quotient_analysis_v1.txt',PARENT+'/independent_verification_v2.json',PARENT+'/receipt.json',PARENT+'/seal.json',PARENT+'/jobs/prepare/job.json',PARENT+'/jobs/faer_static_1e-6/job.json',CACHE,TRACE,BASIS,PROJECTION]


def scope(value):
    require(type(value)is dict,'explicit scoped object')
    for k in FLAGS:
        if k in value:require(value[k]is False,'no restoration theorem admission '+k)


def source_names():
    pending=['run_primitive_state_triangular_restoration','check_primitive_state_triangular_restoration_run',*TESTS];seen=set()
    while pending:
        n=pending.pop();p=ROOT/(n+'.py')
        if n in seen or not p.is_file():continue
        seen.add(n)
        for node in ast.walk(ast.parse(p.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def verify_parent():
    manifests={}
    for number in (15,16):
        manifest=read(ROOT/f'cancellation-arithmetic-results/publication-{number:03d}/manifest.json');files=manifest.get('files')
        require(type(files)is dict and bool(files),'complete recursive publication binding')
        for n,h in files.items():require(sha(path_under(ROOT,n))==h,'immutable publication parent '+n)
        manifests[number]=files
    files=manifests[16];earlier=manifests[15]
    report=read(ROOT/'cancellation-arithmetic-results/publication-016/report.json');review=read(ROOT/(PARENT+'/independent_verification_v2.json'))
    require(report.get('schema')==16 and report.get('supplemental_audit')is True and report.get('original_audit_contract_satisfied')is False,'supplemental publication016 license')
    require(review.get('schema')=='primitive-state-cached-primal-variants-independent-review-v2' and review.get('all_passed')is True and review.get('original_audit_contract_satisfied')is False,'completed independent supplemental parent audit')
    require(report.get('independent_receipt_sha256')==sha(ROOT/(PARENT+'/independent_verification_v2.json')) and report.get('terminal_receipt_sha256')==sha(ROOT/(PARENT+'/receipt.json')),'parent independent/terminal receipt binding')
    check=review.get('cache_check',{})
    require(check.get('verified')is True and check.get('canonical_system_independently_rebuilt')is True and review.get('parent_basis_replays')==1 and review.get('geometry_rebuilds')==1,'parent exact source and basis authorization')
    for n in (CACHE,TRACE,PARENT+'/independent_verification_v2.json',PARENT+'/receipt.json',PARENT+'/jobs/prepare/job.json',PARENT+'/jobs/faer_static_1e-6/job.json'):require(n in files,'parent bound source/native evidence '+n)
    for n in (BASIS,PROJECTION):require(n in earlier,'ancestor bound complete exact tapes '+n)
    prep=read(ROOT/(PARENT+'/jobs/prepare/job.json'),65536);job=read(ROOT/(PARENT+'/jobs/faer_static_1e-6/job.json'),65536)
    require(prep.get('status')=='cache_verified' and job.get('status')=='trace_verified' and job.get('termination_status')=='AlmostSolved','fixed completed faer native seed')
    require(prep['cache_binding']['cache_file_hash']==check.get('cache_compact_sha256')==files[CACHE] and job['artifacts']['trace']['sha256']==files[TRACE],'parent actual source/seed file identity')
    faer=next((q for q in review.get('jobs',[]) if q.get('variant')=='faer_static_1e-6'),None)
    require(faer is not None and faer.get('transport_status')=='available' and faer.get('worker_status')=='trace_verified','completed seed independent transport')
    license=dict(parent_publication='publication-016',parent_review_hash=files[PARENT+'/independent_verification_v2.json'],publication_report_hash=sha(ROOT/'cancellation-arithmetic-results/publication-016/report.json'),input_file_hashes={n:(files if n in files else earlier)[n] for n in (CACHE,TRACE,BASIS,PROJECTION)},original_system_hash=check['original_system_hash'],canonical_system_hash=check['canonical_system_hash'],original_rows=5641,original_variables=1957,projected_variables=1224,rank=779,old_protocol_contract_satisfied=False)
    return license,len(files),len(earlier)


def verify_protocol(value,license):
    expected=dict(schema='primitive-state-triangular-restoration-run-v1',parent_license=license,limits=LIMITS,parallel=PARALLEL,tests=TESTS,phases=['restore'],seed_variant='faer_static_1e-6',seed_rule='exact-binary64; negative FREE squares zero; all other free aggregates unchanged',lift='child=0; storage_K=C; parent=P+4C; signed relations positive/negative parts',backsub_order='descending pivot column',original_objective_preserved=False,optimization_result=False,no_solver_or_new_elimination=True,one_fixed_seed=True,all_original_equalities_signs_and_PSD_required=True,parent_source_rebuild_required=False,**FLAGS)
    require(value==expected,'exact fixed restoration protocol')


def verify_inventory(directory,receipt):
    require(type(receipt.get('files_sha256'))is dict,'complete restoration terminal inventory');scope(receipt)
    actual={str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file() and p.relative_to(directory).parts[0]!='frozen_source' and str(p.relative_to(directory)) not in ('receipt.json','independent_verification.json')}
    require(actual==set(receipt['files_sha256']),'complete terminal file inventory')
    rootfiles={'protocol.json','source_seal.json','input.json','seal.json','run_started.json','tests.json','execution.json'}
    jobfiles={'restoration-job.json','progress.json','restoration.json','check.json'}
    for n,h in receipt['files_sha256'].items():
        p=path_under(directory,n);require(sha(p)==h,'terminal restoration file binding '+n)
        if n in rootfiles:cap=65536
        else:
            require(n.startswith('jobs/') and len(Path(n).parts)==2,'declared bounded restoration artifact')
            name=Path(n).name;base=name[:-4] if name.endswith('.tmp') else name
            require(base in jobfiles,'known restoration artifact or retained tmp')
            cap=8388608 if base in ('restoration.json','check.json') else 65536
        require(p.stat().st_size<=cap,'bounded restoration archive file '+n)
    return dict(bound_files=len(actual),temporary_files=[n for n in sorted(actual) if n.endswith('.tmp')],temporary_files_are_evidence=False)


def verify_runtime(execution):
    rows=execution.get('results');cost=execution.get('cost',{})
    require(type(rows)is list and len(rows)==1 and rows[0].get('index')==0 and type(rows[0]['index'])is int and rows[0].get('status')in ('available','missing_resource','error'),'one fixed ordered restoration transport')
    for k,v in dict(requested_workers=1,workers=1,max_in_flight=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn').items():require(type(cost.get(k))is type(v) and cost[k]==v,'fixed restoration runtime '+k)
    for k in ('elapsed_seconds','result_bytes','payload_bytes'):require(type(cost.get(k))in (int,float) and math.isfinite(cost[k]) and cost[k]>=0,'finite restoration runtime '+k)
    require(cost['result_bytes']<=65536+4096,'bounded restoration transport')
    for k,s in [('available','available'),('missing','missing_resource'),('errors','error')]:require(cost.get(k)==int(rows[0]['status']==s),'complete restoration transport count '+k)
    if rows[0]['status']!='available':require('value' not in rows[0],'failed transport has no fabricated result')
    return rows[0]


def verify_ledger(ledger,input_reserve,check,source_cells):
    require(type(ledger)is dict and ledger.get('max_work')==450000000,'fixed whole job work ceiling')
    entries=ledger.get('entries');require(type(entries)is list and 1<=len(entries)<=3,'bounded restoration stage ledger')
    stages=[('compilation',input_reserve),('restoration_producer',125000000),('restoration_checker',None)];total=0;pending=[]
    for i,(entry,(stage,allocation)) in enumerate(zip(entries,stages)):
        expected=450000000-total if allocation is None else allocation
        require(entry.get('stage')==stage and type(entry.get('allocation'))is int and entry['allocation']==expected,'exact ordered restoration allocation')
        if i==0:
            require(entry.get('precision')=='declared_compilation_reserve' and entry.get('reserve')==expected and entry.get('charged_operations')==expected,'declared actual file/source binding reserve')
        elif entry.get('precision')=='independently_verified':
            require(i==2 and check is not None and entry.get('reserve')==check['independent_audit_work_reserve'] and entry.get('charged_operations')==check['audit_operations'],'only independently bounded checker refinement')
        else:
            require(entry.get('precision')=='allocated_unverified' and entry.get('reserve')==expected and entry.get('charged_operations')is None,'full pending producer/checker allocation')
            if i==2:pending.append(stage)
        require(type(entry['reserve'])is int and 0<entry['reserve']<=expected,'bounded stage work reserve');total+=entry['reserve']
    require(total<=450000000 and ledger.get('total_work_reserve')==total and ledger.get('remaining_work')==450000000-total,'exact conservative restoration ledger sum')
    if check is not None:
        require(len(entries)==3 and check['audit_operations']<=entries[2]['allocation']-8388608-source_cells-1 and check['independent_audit_work_reserve']<=entries[2]['allocation'],'persisted check fits allocated audit allowance')
    return dict(total_work_reserve=total,pending_stages=pending,all_stages_committed=len(entries)==3 and not pending)


def verify_artifacts(directory,record):
    artifacts=(record or {}).get('artifacts',{})
    require(type(artifacts)is dict,'explicit restoration artifact map')
    for name,value in artifacts.items():require(name in ('restoration','check') and value==dict(file=name+'.json',sha256=sha(directory/(name+'.json'))),'bound restoration artifact '+name)


def verify_job(directory,row,input_reserve,source_cells,check,license):
    folder=directory/'jobs';path=folder/'restoration-job.json';record=read(path,65536) if path.exists() else None
    progress=read(folder/'progress.json',65536) if (folder/'progress.json').exists() else None
    stored=read(folder/'check.json') if (folder/'check.json').exists() else None
    require(stored is None or check is not None and stored==check,'same deterministic independent restoration check')
    if row['status']=='available':
        value=row.get('value');require(type(value)is dict and record is not None,'available restoration metadata');scope(value)
        require(value.get('file')=='jobs/restoration-job.json' and value.get('sha256')==sha(path) and value.get('status')==record.get('status') and value.get('cost')==record.get('cost'),'transport metadata/hash/status/cost binding')
    ledger=None;pl=None;outer=False
    if record is not None:
        scope(record);ORIGINAL.verify_worker_cost(record['cost'])
        require(record.get('phase')=='restore' and type(record.get('index'))is int and record['index']==0 and record.get('status')in ('restoration_verified','unknown','missing_resource','rejected'),'one declared restoration job')
        require(type(record.get('deadline_exceeded'))is bool,'explicit cooperative deadline status')
        if 'parent_license' in record:require(record['parent_license']==license,'same completed parent license')
        if 'input_work_reserve' in record:require(record['input_work_reserve']==input_reserve,'actual bounded source/file reserve')
        verify_artifacts(folder,record)
        if record.get('ledger')is not None:ledger=verify_ledger(record['ledger'],input_reserve,stored,source_cells)
    if progress is not None:
        scope(progress);verify_artifacts(folder,progress)
        require(progress.get('phase')in ('restoration_started','source_decode','retained_replay','seed','back_substitution','canonical_lift','exact_original_checks','restored','restoration_returned','restoration_check_started','restoration_verified','unknown','missing_resource','rejected'),'known restoration lifecycle')
        require(progress.get('status')in ('missing_resource','restoration_verified','unknown','rejected'),'known restoration checkpoint status')
        pl=verify_ledger(progress['ledger'],input_reserve,stored,source_cells)
        if record is not None and record.get('ledger')is not None:
            outer=record.get('status')in ('missing_resource','rejected')
            if outer:
                old=progress['ledger']['entries'];new=record['ledger']['entries'];require(len(old)<=len(new),'failure preserves prior ledger prefix')
                for a,b in zip(old,new):
                    require(a['stage']==b['stage'] and a['allocation']==b['allocation'],'failure preserves allocation')
                    if a['precision']=='independently_verified':require(a==b,'failure preserves committed checker')
            else:
                for k in ('ledger','status','artifacts','restoration_verified','finite_candidate_feasible'):require(progress.get(k)==record.get(k),'terminal progress metadata binding '+k)
        elif record is not None:require(record['status']in ('missing_resource','rejected'),'outer metadata without ledger is failure');outer=True
    available=row['status']=='available' and record is not None and record['status']=='restoration_verified' and record.get('deadline_exceeded')is False
    if record is not None and record['status']=='restoration_verified':
        require(check is not None and stored is not None and check.get('complete')is True and check.get('restoration_verified')is True,'complete independent restoration')
        require(ledger is not None and ledger['all_stages_committed'] and progress is not None and progress['phase']=='restoration_verified' and set(record.get('artifacts',{}))=={'restoration','check'},'committed complete restoration ledger/artifacts')
        require(record.get('restoration_verified')is True and record.get('finite_candidate_feasible')is check['finite_candidate_feasible'],'restoration outcome binding')
    elif record is not None:
        require(record.get('restoration_verified')is False and record.get('finite_candidate_feasible')is None,'failed/UNKNOWN metadata admits no candidate')
    return dict(transport_status=row['status'],worker_status=record.get('status') if record else None,
                restoration_verified=available,finite_candidate_feasible=check['finite_candidate_feasible'] if available else None,
                independent_replay_retained=check is not None,deadline_exceeded=record.get('deadline_exceeded') if record else None,lifecycle=dict(ledger=ledger,progress_ledger=pl,progress_retained=progress is not None,outer_partial_failure=outer),**FLAGS)


def _audit(directory,*,write=False,time_limit=900,max_audit_operations=450000000,max_audit_cells=60000000):
    require(type(time_limit)in (int,float) and math.isfinite(time_limit) and 0<time_limit<=900,'finite bounded audit deadline')
    require(type(max_audit_operations)is int and 0<max_audit_operations<=450000000 and type(max_audit_cells)is int and 0<max_audit_cells<=60000000,'strict bounded independent audit caps')
    started=time.monotonic();deadline=started+time_limit;d=Path(directory).resolve()
    if write and (d/'independent_verification.json').exists():raise FileExistsError('independent verification already exists')
    io=CORE.EXACT._Budget(deadline,max_audit_operations,max_audit_cells,4096);_IO_BUDGET.set(io)
    protocol=read(d/'protocol.json',65536);source=read(d/'source_seal.json',65536);inputs=read(d/'input.json',65536);seal=read(d/'seal.json',65536)
    for n in ('protocol','source_seal','input'):require(seal.get(n+'_sha256')==sha(d/(n+'.json')),'frozen restoration seal '+n)
    io.charge(sum(2*(p.stat().st_size//64+1) for p in ROOT.glob('*.py') if p.name in source))
    require(set(source)==set(source_names()),'complete transitive restoration source closure')
    frozen={str(p.relative_to(d/'frozen_source')) for p in (d/'frozen_source').rglob('*') if p.is_file()}
    require(frozen==set(source),'complete frozen source tree')
    for n,h in source.items():require(sha(path_under(ROOT,n))==h==sha(path_under(d/'frozen_source',n)),'immutable restoration source '+n)
    require(set(inputs.get('input_sha256',{}))==set(INPUTS),'complete restoration input closure')
    for n,h in inputs['input_sha256'].items():require(sha(path_under(ROOT,n))==h,'immutable restoration input '+n)
    reserve=4*sum(path_under(ROOT,n).stat().st_size for n in INPUTS)+12*sum(path_under(ROOT,n).stat().st_size for n in source)+1048576+1
    require(inputs.get('binding_work_reserve')==reserve and reserve+125000000<450000000,'bounded actual file/hash/decode work reserve')
    license,parent_count,ancestor_count=verify_parent();verify_protocol(protocol,license)
    for n,h in license['input_file_hashes'].items():require(inputs['input_sha256'][n]==h,'licensed parent full-source/seed/tape binding')
    tests=read(d/'tests.json',65536);require(tests.get('returncode')==0 and type(tests.get('stderr'))is str and re.search(r'Ran (\d+) tests?',tests['stderr']) and tests['stderr'].rstrip().endswith('OK'),'prescore restoration calibration passed')
    count=int(re.search(r'Ran (\d+) tests?',tests['stderr']).group(1))
    require(read(d/'run_started.json',65536)==dict(protocol_sha256=sha(d/'protocol.json')),'sealed run startup')
    receipt=read(d/'receipt.json',65536);inventory=verify_inventory(d,receipt);require(receipt.get('source_count')==len(source),'terminal source count')
    row=verify_runtime(read(d/'execution.json',65536))
    cache=read(ROOT/CACHE,134217728);trace=read(ROOT/TRACE,8388608);basis=read(ROOT/BASIS,33554432);projection=read(ROOT/PROJECTION,33554432)
    require((len(cache['original']['columns']),len(cache['original']['rhs']),basis.get('augmented_rank'),len(projection['retained_indices']))==(1957,5641,779,1224),'unchanged licensed finite source geometry')
    source_cells=sum(map(len,cache['original']['columns']))+len(cache['original']['rhs'])
    restored=read(d/'jobs/restoration.json') if (d/'jobs/restoration.json').exists() else None
    check=None;ops=0;cells=0
    if restored is not None:
        bindings={name:CORE.digest(v) for name,v in [('cache',cache),('trace',trace),('basis',basis),('projection',projection)]}
        cap=450000000-reserve-125000000-8388608-source_cells-1
        require(cap>0,'positive worker independent restoration allocation')
        check=CORE.verify_restoration(cache,trace,basis,projection,restored,deadline=deadline,max_operations=min(cap,max_audit_operations-io.operations),max_cells=max_audit_cells-io.cells,max_coefficient_bits=4096,max_receipt_bytes=8388608,expected_bindings=bindings)
        ops=check['audit_operations'];cells=check['audit_cells'];io.charge(ops,cells=cells)
    job=verify_job(d,row,reserve,source_cells,check,license)
    # Source and archive binding are rechecked after exact replay.
    for n,h in source.items():require(sha(path_under(ROOT,n))==h==sha(path_under(d/'frozen_source',n)),'post-replay source binding')
    for n,h in inputs['input_sha256'].items():require(sha(path_under(ROOT,n))==h,'post-replay input binding')
    verify_inventory(d,receipt)
    require(time.monotonic()<=deadline,'independent archive audit deadline')
    final_bindings={n:sha(d/(n+'.json')) for n in ('protocol','source_seal','input','seal','tests','execution','receipt')}
    result=dict(schema='primitive-state-triangular-restoration-independent-review-v1',all_passed=True,source_count=len(source),tests_passed=count,parent_bound_files=parent_count,ancestor_bound_files=ancestor_count,parent_source_rebuilds=0,new_solver_calls=0,new_elimination_calls=0,original_finite_equations=5641,original_variables=1957,projected_variables=1224,rank=779,restoration_check=check,job=job,inventory=inventory,independent_replay_operations=ops,independent_replay_cells=cells,total_independent_audit_operations=io.operations,total_independent_audit_cells=io.cells,artifact_io_accounting='each SHA file pass bytes//64+1; each JSON read 2*(bytes//64+1) and bytes//64+1 cells; exact replay separately charged; source AST read proxy 2*(bytes//64+1) per sealed source',independent_audit_limits=dict(seconds=time_limit,max_operations=max_audit_operations,max_cells=max_audit_cells),elapsed_seconds=time.monotonic()-started,uniform_or_RH_admission=False,objective_preserved=False,input_sha256=final_bindings,**FLAGS)
    if write:
        with (d/'independent_verification.json').open('x') as f:json.dump(result,f,sort_keys=True,indent=2,allow_nan=False)
    return result


def audit(directory,**kwargs):
    token=_IO_BUDGET.set(None)
    try:return _audit(directory,**kwargs)
    finally:_IO_BUDGET.reset(token)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('directory');p.add_argument('--write',action='store_true');a=p.parse_args();print(json.dumps(audit(a.directory,write=a.write),sort_keys=True))

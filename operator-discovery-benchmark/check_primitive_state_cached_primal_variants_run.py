"""Independent shared-cache preparation and two fixed native variant archive audit."""
import argparse
import ast
import json
import math
from pathlib import Path
import re
import time
import check_primitive_state_basis_primal_run as PARENT
import check_primitive_state_cached_primal_variants as CORE

ROOT=Path(__file__).resolve().parent
ORIGINAL=PARENT.ORIGINAL
FLAGS=dict(CORE.FLAGS)
PROGRAM=dict(PARENT.PROGRAM)
COMPILER_LIMITS=dict(PARENT.COMPILER_LIMITS)
VARIANTS=[dict(id='qdldl_default',options=dict(direct_solve_method='qdldl')),dict(id='faer_static_1e-6',options=dict(direct_solve_method='faer',static_regularization_constant=1e-6))]
TESTS=['test_primitive_state_cached_primal_variants','test_check_primitive_state_cached_primal_variants','test_run_primitive_state_cached_primal_variants','test_check_primitive_state_cached_primal_variants_run']
LIMITS=dict(cooperative_seconds=900,max_work=450000000,max_cache_bytes=134217728,max_trace_bytes=8388608,max_log_bytes=1048576,max_metadata_bytes=65536,max_cells=4000000,max_coefficient_bits=4096,max_audit_cells=60000000,producer_operations=50000000)
PREP_PARALLEL=dict(workers=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,timeout_seconds=1800,max_jobs=1,max_result_bytes=65536)
VARIANT_PARALLEL=dict(workers=2,worker_memory_bytes=3*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=1800,max_jobs=2,max_result_bytes=65536)
PARENT_RUN='cancellation-arithmetic-results/primitive-state-basis-primal-001'
INPUTS=['cancellation-arithmetic-results/publication-015/manifest.json','cancellation-arithmetic-results/publication-015/report.json','primitive_state_cached_primal_variants_resource_scope.txt',
    *[PARENT_RUN+'/'+n for n in ['protocol.json','seal.json','source_seal.json','input.json','receipt.json','independent_verification.json','jobs/primal.json','jobs/primal-trace.json','jobs/primal-check.json']]]
read,sha,path_under=ORIGINAL.read,ORIGINAL.sha,ORIGINAL.path_under
require=CORE.require
scope=PARENT.scope


def read_cache(path):return ORIGINAL.read(path,LIMITS['max_cache_bytes'])


def source_names():
    pending=['run_primitive_state_cached_primal_variants','check_primitive_state_cached_primal_variants_run',*TESTS];seen=set()
    while pending:
        name=pending.pop();p=ROOT/(name+'.py')
        if name in seen or not p.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(p.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def verify_parent(expected,geometry,*,deadline,max_operations,max_cells):
    d=ROOT/PARENT_RUN
    protocol=read(d/'protocol.json',65536);PARENT.verify_protocol(protocol)
    seal=read(d/'seal.json',65536)
    for n in ('protocol','source_seal','input'):require(seal.get(n+'_sha256')==sha(d/(n+'.json')),'completed parent preregistration '+n)
    terminal=read(d/'receipt.json',65536);PARENT.verify_inventory(d,terminal)
    sources=read(d/'source_seal.json',65536);require(set(sources)==set(PARENT.source_names()),'complete parent trial source closure')
    for n,h in sources.items():require(sha(path_under(ROOT,n))==h and sha(path_under(d/'frozen_source',n))==h,'immutable completed parent source '+n)
    review=read(d/'independent_verification.json');scope(review)
    require(review.get('schema')=='primitive-state-basis-primal-independent-review-v1' and review.get('all_passed')is True and review.get('trial',{}).get('terminal_numerical_diagnostics_available')is True,'completed fresh-basis parent audit')
    require(set(review.get('input_sha256',{}))=={'protocol.json','source_seal.json','input.json','seal.json','tests.json','execution.json','receipt.json'},'complete parent independent review input bindings')
    for n,h in review['input_sha256'].items():require(sha(path_under(d,n))==h,'completed parent audit input '+n)
    record=read(d/'jobs/primal.json',65536);scope(record);ORIGINAL.verify_compilation(record,geometry)
    require(record.get('status')=='trace_verified' and record.get('fresh_exact_basis_authorized')is True,'completed parent fresh exact authorization')
    for k,v in expected.items():require(record.get(k)==v,'same complete parent arithmetic source '+k)
    license=PARENT.verify_license(expected,geometry,deadline=deadline,max_operations=max_operations,max_cells=max_cells)
    require(record.get('selected_original_indices')==license['indices'] and protocol.get('basis_evidence')==license['evidence'],'independently replayed completed parent row-span license')
    for which in ('projection','basis'):
        require(read(d/'jobs'/f'{which}-replay.json')==license['replay_checks'][which],'same saved parent fresh replay '+which)
    trace=read(d/'jobs/primal-trace.json');check=read(d/'jobs/primal-check.json')
    require(check==review['trial']['trace_check'] and check.get('verified')is True and check.get('canonical_system_independently_rebuilt')is True,'completed parent canonical matrix independent check')
    require(record.get('artifacts',{}).get('trace')==dict(file='primal-trace.json',sha256=sha(d/'jobs/primal-trace.json')),'completed parent native trace hash')
    bindings=dict(publication_report_hash=sha(ROOT/'cancellation-arithmetic-results/publication-015/report.json'),parent_trace_hash=sha(d/'jobs/primal-trace.json'),parent_review_hash=sha(d/'independent_verification.json'))
    return dict(assembly=trace['assembly'],bindings=bindings,indices=license['indices'],audit_operations=license['audit_operations'],audit_cells=license['audit_cells'],independent_audit_work_reserve=license['independent_audit_work_reserve'],parent_solver_contract=protocol['solver_contract'])


def compare_source(cache,geometry,decoded=None,*,deadline=None,max_operations=450000000,max_cells=60000000):
    budget=CORE.EXACT._Budget(deadline,max_operations,max_cells,4096)
    if decoded is None:decoded=CORE.decode_original(cache,budget)
    budget.charge(2*decoded['source_cells']+len(decoded['monomials'])+len(decoded['columns']))
    for key,target in [('columns','columns'),('lhs','lhs'),('monomials','domain'),('shape','shape'),('offset','offset')]:require(decoded[key]==geometry[target],'shared cache exact full source '+key)
    require(decoded['specs']==ORIGINAL.B.gram_specs(),'unchanged shared original PSD blocks')
    return dict(audit_operations=budget.operations,audit_cells=budget.cells)


def verify_inventory(directory,receipt):
    scope(receipt)
    allowed={'protocol.json','source_seal.json','input.json','seal.json','tests.json','run_started.json','execution.json','preparation-execution.json'}
    jobs=['jobs/prepare/job.json','jobs/prepare/progress.json','jobs/prepare/source-cache.json','jobs/prepare/cache-check.json']
    for v in VARIANTS:
        jobs.extend('jobs/'+v['id']+'/'+name for name in ['job.json','progress.json','trace.json','check.json','native.log','native-progress.json','native-progress.json.source.json'])
    allowed.update(jobs);allowed.update(n+'.tmp' for n in jobs)
    actual={str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file() and 'frozen_source' not in p.relative_to(directory).parts}-{'receipt.json','independent_verification.json'}
    files=receipt.get('files_sha256');require(not actual-allowed and type(files)is dict and set(files)==actual,'complete declared cached stage artifact inventory')
    for n,h in files.items():
        p=path_under(directory,n);require(sha(p)==h,'cached stage artifact hash '+n);base=n[:-4] if n.endswith('.tmp') else n
        cap=LIMITS['max_cache_bytes'] if base=='jobs/prepare/source-cache.json' else LIMITS['max_log_bytes'] if base.endswith('/native.log') else LIMITS['max_trace_bytes'] if any(base.endswith('/'+s) for s in ('trace.json','check.json','cache-check.json','native-progress.json','native-progress.json.source.json')) else LIMITS['max_metadata_bytes']
        require(p.stat().st_size<=cap,'bounded cached stage artifact '+n)
    return dict(files=len(files),bytes=sum(path_under(directory,n).stat().st_size for n in files))


def verify_runtime(execution,preparation):
    PARENT.BASIS.verify_runtime(preparation)
    if execution.get('status')=='blocked':
        require(execution==dict(status='blocked',reason='shared cache gate',results=[]),'explicit blocked solver stage');return
    require(type(execution.get('results'))is list and len(execution['results'])==2,'two fixed variant transports')
    cost=execution.get('cost',{})
    for key,value in dict(requested_workers=2,worker_memory_bytes=3*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn').items():require(type(cost.get(key))is type(value) and cost[key]==value,'fixed parallel solver resources '+key)
    require(type(cost.get('workers'))is int and 1<=cost['workers']<=2 and type(cost.get('max_in_flight'))is int and 1<=cost['max_in_flight']<=2,'bounded parallel solver workers')
    for i,row in enumerate(execution['results']):
        require(type(row)is dict and type(row.get('index'))is int and row['index']==i and row.get('status')in ('available','missing_resource','error'),'ordered fixed variant transport')
        if row['status']!='available':require('value' not in row,'failed variant transport cannot invent metadata')
    for key in ('elapsed_seconds','result_bytes','payload_bytes'):require(type(cost.get(key))in (int,float) and math.isfinite(cost[key]) and cost[key]>=0,'finite parallel runtime '+key)
    require(cost['result_bytes']<=2*(65536+4096),'bounded variant transport bytes')
    for key,status in [('available','available'),('missing','missing_resource'),('errors','error')]:require(cost.get(key)==sum(row['status']==status for row in execution['results']),'complete variant transport count '+key)

def verify_protocol(protocol):
    expected=dict(schema='primitive-state-cached-primal-variants-run-v1',program=PROGRAM,scales=[1,2,3,5],language=ORIGINAL.B.SPEC,gram_specs=ORIGINAL.B.gram_specs(),compiler_limits=COMPILER_LIMITS,limits=LIMITS,tests=TESTS,parent_publication='publication-015',variants=VARIANTS,parallel=VARIANT_PARALLEL,preparation_parallel=PREP_PARALLEL,phases=['prepare','variants'],parent_run='primitive-state-basis-primal-001',shared_cache_schema='primitive-state-cached-primal-v1',expected_shape=dict(original_rows=5641,original_columns=1957,selected_rows=779,scalar_offset=1597),shared_preparation_count=1,exact_basis_replay_per_solver=False,exact_restore_all_original_rows_required=True,no_refit_or_source_selection=True)
    for k,v in expected.items():require(protocol.get(k)==v,'fixed shared-cache protocol '+k)
    scope(protocol)



def verify_solver_contracts(protocol,parent_contract):
    contracts=protocol.get('solver_contracts');require(type(contracts)is dict and set(contracts)=={v['id'] for v in VARIANTS},'both fixed solver contracts')
    for variant in VARIANTS:
        fixed=dict(parent_contract['fixed_options']);fixed.update(variant['options'])
        require(contracts[variant['id']]==dict(parent_contract,fixed_options=fixed),'only predeclared solver settings change '+variant['id'])


def verify_solver(solver,contract):
    require(type(solver)is dict and solver.get('name')=='clarabel-native' and solver.get('versions')==contract['versions'],'frozen native solver versions')
    options=solver.get('options');require(type(options)is dict and type(options.get('time_limit'))in (int,float) and math.isfinite(options['time_limit']) and 0<=options['time_limit']<=900,'bounded actual solver time allowance')
    require({k:v for k,v in options.items() if k!='time_limit'}==contract['fixed_options'],'all frozen native variant settings')
    require(solver.get('options_hash')==CORE.digest(options) and solver.get('versions_hash')==CORE.digest(contract['versions']),'native settings/version fingerprints')


def verify_ledger(ledger,compilation,check,*,variant=False,source_cells=0):
    stages=['compilation','cache_decode','native_producer','variant_checker'] if variant else ['compilation','cache_producer','cache_checker']
    require(type(ledger)is dict and set(ledger)=={'max_work','total_work_reserve','remaining_work','entries'} and type(ledger.get('entries'))is list and 1<=len(ledger['entries'])<=len(stages),'complete bounded cache work ledger')
    entries=ledger['entries'];require([e.get('stage') for e in entries]==stages[:len(entries)],'ordered unique cache/variant stages');total=0;pending=[]
    for e in entries:
        require(set(e)=={'stage','allocation','reserve','charged_operations','precision'},'complete cache stage allocation')
        stage=e['stage'];allocation=compilation if stage=='compilation' else LIMITS['max_cache_bytes']+LIMITS['producer_operations'] if stage in ('cache_producer','cache_decode') else LIMITS['producer_operations'] if stage=='native_producer' else LIMITS['max_work']-total
        require(type(e['allocation'])is int and e['allocation']==allocation and allocation>0 and allocation<=LIMITS['max_work']-total,'bounded declared cache stage allocation '+stage)
        if stage=='compilation':reserve=allocation;require(e['precision']=='declared_compilation_reserve' and e['charged_operations']==allocation,'shared compilation/cache-reference reserve')
        elif stage in ('cache_producer','cache_decode','native_producer'):reserve=allocation;require(e['precision']=='allocated_unverified' and e['charged_operations']is None,'conservative cache/native reservation '+stage)
        elif e['precision']=='independently_verified':
            require(check is not None and check.get('verified')is True,'checker precision requires persisted independent result');reserve=check['independent_audit_work_reserve']
            require(type(e['charged_operations'])is int and e['charged_operations']==check['audit_operations'],'cache/native checker exact work binding')
        else:reserve=allocation;require(e['precision']=='allocated_unverified' and e['charged_operations']is None,'pending checker reserves full allocation');pending.append(stage)
        require(type(e['reserve'])is int and e['reserve']==reserve and 0<=reserve<=allocation,'bounded cache/native stage reserve');total+=reserve
    require(type(ledger['max_work'])is int and ledger['max_work']==LIMITS['max_work'] and type(ledger['total_work_reserve'])is int and ledger['total_work_reserve']==total and type(ledger['remaining_work'])is int and ledger['remaining_work']==LIMITS['max_work']-total,'complete cumulative cache/native reservation')
    if check is not None:
        require(entries[-1]['stage']==stages[-1],'written check requires prior checker allocation')
        allowed=entries[-1]['allocation']-LIMITS['max_cache_bytes']-(LIMITS['max_trace_bytes'] if variant else 0)-source_cells-1
        require(check['audit_operations']<=allowed and check['independent_audit_work_reserve']<=entries[-1]['allocation'],'written independent check fits recorded bounded allowance')
    return dict(total_work_reserve=total,pending_stages=pending,all_stages_committed=len(entries)==len(stages) and not pending)


def verify_transport(directory,folder,row):
    path=directory/folder/'job.json';record=read(path,65536) if path.exists() else None
    if row.get('status')=='available':
        value=row.get('value');require(type(value)is dict and record is not None,'available cache metadata required');scope(value)
        require(value.get('file')==str(path.relative_to(directory)) and value.get('sha256')==sha(path) and value.get('status')==record.get('status') and value.get('cost')==record.get('cost'),'transported cache/native status/file/cost binding')
    if record is not None:
        scope(record);ORIGINAL.verify_worker_cost(record['cost']);require(type(record.get('deadline_exceeded'))is bool,'explicit cache/native deadline state')
    return record


def verify_lifecycle(directory,record,check,compilation,*,variant=False,source_cells=0):
    progress_path=directory/'progress.json';progress=read(progress_path,65536) if progress_path.exists() else None
    ledger=verify_ledger(record['ledger'],compilation,check,variant=variant,source_cells=source_cells) if record is not None and record.get('ledger')is not None else None
    older_failure=False;progress_ledger=None
    if progress is not None:
        scope(progress)
        phases=['cache_decode_started','native_started','native_returned','variant_check_started','trace_verified','missing_resource','rejected'] if variant else ['cache_preparation_started','cache_encoded','cache_check_started','cache_verified','missing_resource','rejected']
        statuses=('trace_verified','missing_resource','rejected') if variant else ('cache_verified','missing_resource','rejected')
        require(progress.get('phase')in phases and progress.get('status')in statuses,'known cached lifecycle checkpoint')
        verify_artifacts(directory,progress)
        progress_ledger=verify_ledger(progress['ledger'],compilation,check,variant=variant,source_cells=source_cells)
        if record is not None and record.get('ledger')is not None:
            older_failure=record.get('status')in ('missing_resource','rejected')
            if older_failure:
                old=progress['ledger']['entries'];new=record['ledger']['entries'];require(len(old)<=len(new),'failure preserves prior ledger prefix')
                for a,b in zip(old,new):
                    require(a['stage']==b['stage'] and a['allocation']==b['allocation'],'failure preserves prior allocation')
                    if a['precision']=='independently_verified':require(a==b,'failure keeps committed checker precision')
            else:
                for key in ('ledger','status','artifacts'):require(progress.get(key)==record.get(key),'complete lifecycle/metadata binding '+key)
        elif record is not None:require(record.get('status')in ('missing_resource','rejected'),'outer failure cannot imply cache/native completion');older_failure=True
    return dict(ledger=ledger,progress_ledger=progress_ledger,progress_retained=progress is not None,progress_phase=progress.get('phase') if progress else None,outer_partial_failure=older_failure)


def verify_artifacts(folder,record):
    for name,value in (record or {}).get('artifacts',{}).items():
        require(name in ('source-cache','cache-check','trace','check') and value==dict(file=name+'.json',sha256=sha(folder/(name+'.json'))),'bound complete cache/native artifact '+name)


def verify_preparation(directory,execution,geometry,parent,cache,cache_check,expected):
    row=execution['results'][0];folder=directory/'jobs/prepare';record=verify_transport(directory,Path('jobs/prepare'),row)
    stored=read(folder/'cache-check.json') if (folder/'cache-check.json').exists() else None
    require(stored is None or cache_check is not None and stored==cache_check,'same deterministic shared-cache independent check')
    if record is not None:
        require(record.get('phase')=='prepare' and type(record.get('index'))is int and record['index']==0 and record.get('status')in ('cache_verified','missing_resource','rejected'),'declared shared preparation outcome')
        if 'case_hashes' in record:
            for key,value in expected.items():require(record.get(key)==value,'same complete prepared arithmetic source '+key)
        if 'complete_columns' in record:require(record['complete_columns']==len(geometry['columns']) and record.get('complete_monomials')==len(geometry['domain']) and record.get('compilation_work_reserve')==geometry['compilation'],'complete prepared full source geometry')
        verify_artifacts(folder,record)
        if cache is not None and 'cache_binding' in record:require(record['cache_binding']==dict(cache_file_hash=sha(folder/'source-cache.json'),**{n:cache[n] for n in ('original_source_hash','canonical_cache_hash','assembly_hash')}),'preparation actual full cache byte binding')
    lifecycle=verify_lifecycle(folder,record,stored,geometry['compilation'],source_cells=cache['assembly']['counts']['source_cells'] if cache else 0)
    available=row['status']=='available' and record is not None and record['status']=='cache_verified'
    if available:require(cache_check is not None and stored is not None and lifecycle['ledger']is not None and lifecycle['ledger']['all_stages_committed'] and lifecycle['progress_phase']=='cache_verified' and set(record.get('artifacts',{}))=={'source-cache','cache-check'},'complete independently audited shared preparation gate')
    return dict(transport_status=row['status'],worker_status=record.get('status') if record else None,shared_cache_available=available,cache_retained=cache is not None,lifecycle=lifecycle,**FLAGS)


def verify_variant_job(directory,index,variant,execution,protocol,sources,parent,cache,witness,*,deadline,max_operations,max_cells):
    row=execution['results'][index] if execution.get('status')!='blocked' else dict(status='blocked')
    folder=directory/'jobs'/variant;record=verify_transport(directory,Path('jobs')/variant,row)
    trace=read(folder/'trace.json') if (folder/'trace.json').exists() else None;stored=read(folder/'check.json') if (folder/'check.json').exists() else None
    progress=read(folder/'native-progress.json') if (folder/'native-progress.json').exists() else None;startup=read(folder/'native-progress.json.source.json') if (folder/'native-progress.json.source.json').exists() else None
    if execution.get('status')=='blocked':require(record is None and trace is None and startup is None and stored is None,'blocked preparation cannot invent launched variant evidence')
    if cache is None:require(trace is None and startup is None and stored is None,'no numerical solve without shared source cache')
    binding=dict(cache_file_hash=sha(directory/'jobs/prepare/source-cache.json'),**{n:cache[n] for n in ('original_source_hash','canonical_cache_hash','assembly_hash')}) if cache is not None else None
    if record is not None:
        require(record.get('phase')=='variant' and type(record.get('index'))is int and record['index']==index and record.get('status')in ('trace_verified','missing_resource','rejected'),'declared fixed variant metadata')
        if 'variant' in record:require(record['variant']==variant and record.get('cache_binding')==binding,'fixed worker variant and actual shared cache')
        verify_artifacts(folder,record)
    final=trace;origin='trace' if trace else None
    if final is None and progress is not None and progress.get('phase')=='native_returned':final=progress;origin='completed_checkpoint_without_final_transport'
    check=None;operations=cells=0
    if final is not None:
        require(witness is not None,'independently verified shared cache before native audit');verify_solver(final['solver'],protocol['solver_contracts'][variant])
        check,cost=CORE.verify_variant_against_cache(final,witness,variant,expected_source_hashes={n:sources[n] for n in ('primitive_state_cached_primal_variants.py','primitive_state_basis_primal.py','primitive_state_solver_trace.py')},expected_options=final['solver']['options'],expected_versions=protocol['solver_contracts'][variant]['versions'],expected_cache_file_hash=binding['cache_file_hash'],deadline=deadline,max_operations=max_operations,max_cells=max_cells)
        operations=cost['audit_operations'];cells=cost['audit_cells']
        if stored is not None:require(trace is not None and stored==check,'same deterministic persisted variant check')
        if trace is not None and progress is not None:require(progress==dict(trace,phase='native_returned'),'same completed native progress/trace')
        if (folder/'native.log').exists():require((folder/'native.log').read_bytes()==final['retained_log']['text'].encode(),'retained native log disk/text bytes')
    else:require(stored is None,'no saved native check without completed trace')
    if startup is not None:
        scope(startup);verify_solver(startup['solver'],protocol['solver_contracts'][variant])
        require(startup.get('schema')=='primitive-state-basis-primal-v1' and startup.get('vector_role')=='unavailable' and startup.get('source_hashes')=={n:sources[n] for n in ('primitive_state_cached_primal_variants.py','primitive_state_basis_primal.py','primitive_state_solver_trace.py')},'explicit cached native startup schema/source/unavailability')
        require(startup.get('phase')=='cached_assembled' and startup.get('assembly')==cache['assembly'] and startup.get('variant')==variant and startup.get('cache_binding')==binding and startup.get('original_vector')is None,'explicit immutable cached source startup')
        if progress is not None and progress.get('phase')=='native_started':require(progress.get('assembly_hash')==cache['assembly_hash'] and progress.get('variant')==variant and progress.get('cache_binding')==binding and progress.get('solver')==startup['solver'] and progress.get('original_vector')is None,'native iteration binds full cached assembly')
    elif progress is not None and progress.get('phase')=='native_started':raise ValueError('native iteration lacks source checkpoint')
    lifecycle=verify_lifecycle(folder,record,stored,1,variant=True,source_cells=cache['assembly']['counts']['source_cells'] if cache else 0)
    available=row['status']=='available' and record is not None and record['status']=='trace_verified'
    if available:require(trace is not None and stored is not None and lifecycle['ledger']is not None and lifecycle['ledger']['all_stages_committed'] and lifecycle['progress_phase']=='trace_verified' and record.get('numerical_verification_pending')is False and set(record.get('artifacts',{}))=={'trace','check'} and record.get('termination_status')==trace['termination_status'] and record.get('raw_vector_available')==(trace['original_vector']is not None),'complete diagnostic-only fixed variant outcome')
    return dict(variant=variant,transport_status=row['status'],worker_status=record.get('status') if record else None,trace_origin=origin,trace_check=check,numerical_diagnostics_available=available,startup_retained=startup is not None,native_progress_retained=progress is not None,lifecycle=lifecycle,
        cache_verification_reused=witness is not None,audit_operations=operations,audit_cells=cells,mathematical_feasibility='UNKNOWN',accepted_proposal=False,**FLAGS)

def audit(directory,*,write=False,time_limit=900,max_audit_operations=450000000,max_audit_cells=60000000):
    require(type(time_limit)in (int,float) and math.isfinite(time_limit) and 0<time_limit<=900,'bounded cached-stage independent deadline')
    require(type(max_audit_operations)is int and 0<max_audit_operations<=450000000 and type(max_audit_cells)is int and 0<max_audit_cells<=60000000,'bounded cached-stage independent replay resources')
    d=Path(directory).resolve();target=d/'independent_verification.json';started=time.monotonic();deadline=started+time_limit
    if write and target.exists():raise FileExistsError('exclusive cached-variant independent review')
    protocol=read(d/'protocol.json',65536);verify_protocol(protocol);sources=read(d/'source_seal.json',65536)
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
    review=dict(schema='primitive-state-cached-primal-variants-independent-review-v1',all_passed=True,source_count=len(sources),tests_passed=int(match.group(1)),arithmetic_rebuilds=1,geometry_rebuilds=1,parent_basis_replays=1,cache_verifications=1 if cache is not None else 0,canonical_reconstructions=1 if cache is not None else 0,
        independent_audit_limits=dict(seconds=time_limit,max_operations=max_audit_operations,max_cells=max_audit_cells,max_cache_bytes=LIMITS['max_cache_bytes']),
        preparation=preparation,cache_check=cache_check,jobs=jobs,inventory=inventory,independent_replay_operations=operations,independent_replay_cells=cells,parent_bound_files=len(manifest['files']),elapsed_seconds=time.monotonic()-started,
        original_variables=1957,original_finite_equations=5641,selected_original_rows=779,mathematical_feasibility='UNKNOWN',numerical_diagnostics_only=True,
        input_sha256={n:sha(d/n) for n in ['protocol.json','source_seal.json','input.json','seal.json','tests.json','preparation-execution.json','execution.json','receipt.json']},**FLAGS)
    if write:
        with target.open('x') as stream:json.dump(review,stream,sort_keys=True,indent=2,allow_nan=False);stream.write('\n')
    return review


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('directory');parser.add_argument('--write',action='store_true');args=parser.parse_args();print(json.dumps(audit(args.directory,write=args.write),sort_keys=True))

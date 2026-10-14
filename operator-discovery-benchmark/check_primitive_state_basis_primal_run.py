"""Independent licensed-basis native primal archive audit; no new runner imports."""
import argparse
import ast
import json
import math
from pathlib import Path
import re
import time
import check_primitive_state_solver_trace_run as ORIGINAL
import check_primitive_state_exact_row_basis_probe_v2 as BASIS
import check_primitive_state_basis_primal as CORE

ROOT=Path(__file__).resolve().parent
FLAGS=dict(CORE.FLAGS)
PROGRAM=dict(ORIGINAL.PROGRAM)
COMPILER_LIMITS=dict(ORIGINAL.COMPILER_LIMITS)
LIMITS=dict(cooperative_seconds=900,max_work=450000000,producer_operations=50000000,max_cells=4000000,max_coefficient_bits=4096,max_trace_bytes=8388608,max_log_bytes=1048576,max_metadata_bytes=65536,max_audit_cells=60000000,exact_receipt_bytes=33554432,row_preparation_operations=20000000,projection_replay_operations=50000000,basis_replay_operations=125000000)
PARALLEL=dict(workers=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,timeout_seconds=1800,max_jobs=1,max_result_bytes=65536)
TESTS=['test_primitive_state_basis_primal','test_check_primitive_state_basis_primal','test_run_primitive_state_basis_primal','test_check_primitive_state_basis_primal_run']
PRIOR='cancellation-arithmetic-results/primitive-state-exact-row-basis-probe-002'
INPUTS=['cancellation-arithmetic-results/publication-014/manifest.json','cancellation-arithmetic-results/publication-014/report.json',
    'primitive_state_basis_primal_resource_scope.txt',*[PRIOR+'/'+n for n in ['protocol.json','seal.json','receipt.json','source_seal.json','input.json','independent_verification.json','jobs/progress.json','jobs/projection.json','jobs/basis.json','jobs/projection-check.json','jobs/basis-check.json']]]
SOURCE_FIELDS=['ordinary_case_hashes','case_hashes','gram_block_hashes','storage_block_hashes','gram_archive_hashes','factor_archive_hashes','divisor_archive_hashes','cell_archive_hashes','dictionary_sha256','gram_specs','primitive_state_archive_hashes','primitive_source_hashes','multiplier_source_hashes']
read,sha,path_under=ORIGINAL.read,ORIGINAL.sha,ORIGINAL.path_under
require=CORE.require


def scope(value):
    ORIGINAL.scope(value,required=True)
    if 'exact_admission' in value:require(value['exact_admission']is False,'no numerical exact admission')


def source_names():
    pending=['run_primitive_state_basis_primal','check_primitive_state_basis_primal_run',*TESTS];seen=set()
    while pending:
        name=pending.pop();p=ROOT/(name+'.py')
        if name in seen or not p.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(p.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def verify_inventory(directory,receipt):
    scope(receipt)
    allowed={'protocol.json','source_seal.json','input.json','seal.json','run_started.json','tests.json','execution.json'}
    jobs=['jobs/progress.json','jobs/projection-replay.json','jobs/basis-replay.json','jobs/primal.json','jobs/primal-trace.json','jobs/primal-check.json','jobs/primal-progress.json','jobs/primal-progress.json.source.json','jobs/primal-native.log']
    allowed.update(jobs);allowed.update(n+'.tmp' for n in jobs)
    actual={str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file() and 'frozen_source' not in p.relative_to(directory).parts}-{'receipt.json','independent_verification.json'}
    require(not actual-allowed,'declared native primal archive artifacts')
    files=receipt.get('files_sha256');require(type(files)is dict and set(files)==actual,'complete terminal artifact inventory')
    for name,h in files.items():
        p=path_under(directory,name);require(sha(p)==h,'terminal artifact hash '+name)
        base=name[:-4] if name.endswith('.tmp') else name
        cap=LIMITS['max_log_bytes'] if base.endswith('.log') else LIMITS['max_trace_bytes'] if base in {'jobs/primal-trace.json','jobs/primal-check.json','jobs/primal-progress.json','jobs/primal-progress.json.source.json','jobs/projection-replay.json','jobs/basis-replay.json'} else LIMITS['max_metadata_bytes']
        require(p.stat().st_size<=cap,'bounded native primal artifact '+name)
    return dict(files=len(files),bytes=sum(path_under(directory,n).stat().st_size for n in files))


def verify_runtime(execution):
    BASIS.verify_runtime(execution)
    require(len(execution['results'])==1,'one native primal trial')


def verify_license(expected,geometry,*,deadline,max_operations,max_cells):
    d=ROOT/PRIOR
    protocol=BASIS.read(d/'protocol.json',65536);BASIS.verify_protocol(protocol)
    seal=BASIS.read(d/'seal.json',65536)
    for n in ('protocol','source_seal','input'):require(seal.get(n+'_sha256')==sha(d/(n+'.json')),'bound frozen basis license '+n)
    receipt=BASIS.read(d/'receipt.json',65536);BASIS.verify_inventory(d,receipt)
    source=BASIS.read(d/'source_seal.json',65536);require(set(source)==set(BASIS.source_names()),'complete licensed basis source closure')
    for n,h in source.items():require(sha(path_under(ROOT,n))==h and sha(path_under(d/'frozen_source',n))==h,'immutable basis license source '+n)
    review=BASIS.read(d/'independent_verification.json')
    require(review.get('schema')=='primitive-state-exact-row-basis-probe-independent-review-v2' and review.get('all_passed')is True and review.get('equation_reduction_verified')is False,'completed independently licensed basis')
    scope(review)
    require(set(review.get('input_sha256',{}))=={'protocol.json','source_seal.json','input.json','seal.json','tests.json','execution.json','receipt.json'},'complete failed-run review input binding')
    for n,h in review['input_sha256'].items():require(sha(path_under(d,n))==h,'basis license independent input '+n)
    artifacts=BASIS.verify_stage_artifacts(d,geometry,deadline=deadline,max_audit_operations=max_operations,max_audit_cells=max_cells)
    execution=BASIS.read(d/'execution.json',65536);BASIS.verify_runtime(execution)
    require(execution['results'][0]['status']!='available','frozen failed transport retained without promotion')
    basis=artifacts['values']['basis'];indices=basis['retained_indices']
    require(artifacts['checks']['projection']['audit_operations']<=LIMITS['projection_replay_operations'] and artifacts['checks']['basis']['audit_operations']<=LIMITS['basis_replay_operations'],'bounded fresh independent exact replay operations')
    projected_cells=sum(map(len,artifacts['projected_rows']));require(projected_cells+len(artifacts['projected_rows'])<=LIMITS['max_cells'],'bounded exact row preparation cells')
    require(artifacts['checks']['projection'].get('projection_authorized')is True and artifacts['checks']['basis'].get('reduction_authorized')is True and basis['coefficient_consistency']=='consistent','fresh complete consistent original-equation row-span authorization')
    require(len(indices)==779 and len(geometry['columns'])==1957 and len(geometry['domain'])==5641,'published licensed full system dimensions')
    progress=BASIS.read(d/'jobs/progress.json',65536);require(progress.get('phase')=='basis_verified' and progress.get('status')=='basis_verified' and progress.get('selected_original_row_indices')==indices,'retained old complete checkpoint candidate rows')
    evidence=dict(selected_original_indices=indices,indices_hash=CORE.digest(indices),authorization='requires fresh exact replay; oldrun UNKNOWN',publication_report_hash=sha(ROOT/'cancellation-arithmetic-results/publication-014/report.json'),basis_review_hash=sha(d/'independent_verification.json'),basis_terminal_hash=sha(d/'receipt.json'),basis_seal_hash=sha(d/'seal.json'),basis_progress_hash=sha(d/'jobs/progress.json'))
    return dict(evidence=evidence,indices=indices,projected_nonzeros=projected_cells,projected_source_cells=projected_cells+len(artifacts['projected_rhs']),full_source_cells=sum(map(len,geometry['columns']))+len(geometry['lhs']),assembly_basis_source_hash=basis['source_hash'],prior_transport_status=execution['results'][0]['status'],prior_equation_admission=False,fresh_equation_authorization=True,replay_checks=artifacts['checks'],audit_operations=artifacts['audit_operations'],audit_cells=artifacts['audit_cells'],independent_audit_work_reserve=artifacts['independent_audit_work_reserve'])


def verify_ledger(ledger,geometry,license,stored_replays,check,bindings):
    require(type(ledger)is dict and set(ledger)=={'max_work','total_work_reserve','remaining_work','entries'},'explicit complete numerical trial work ledger')
    entries=ledger.get('entries');stages=['compilation','exact_row_preparation','projection_replay','basis_replay','native_producer','native_checker']
    require(type(entries)is list and 1<=len(entries)<=6 and [e.get('stage') for e in entries]==stages[:len(entries)],'ordered unique native/fresh replay stages')
    total=0;prior={};pending=[]
    for entry in entries:
        stage=entry['stage'];require(set(entry)=={'stage','allocation','reserve','charged_operations','precision'},'complete stage ledger fields')
        if stage=='compilation':allocation=geometry['compilation']
        elif stage=='exact_row_preparation':allocation=LIMITS['row_preparation_operations']
        elif stage=='projection_replay':allocation=LIMITS['projection_replay_operations']+LIMITS['exact_receipt_bytes']+license['full_source_cells']+license['projected_nonzeros']+1
        elif stage=='basis_replay':allocation=LIMITS['basis_replay_operations']+LIMITS['exact_receipt_bytes']+license['projected_source_cells']+1
        elif stage=='native_producer':allocation=LIMITS['producer_operations']
        else:allocation=LIMITS['max_work']-total
        require(type(entry['allocation'])is int and entry['allocation']==allocation and allocation>0 and allocation<=LIMITS['max_work']-total,'known bounded stage allocation '+stage)
        if stage=='compilation':
            reserve=allocation;require(entry['charged_operations']==allocation and entry['precision']=='declared_compilation_reserve','independent compilation reserve')
        elif stage in ('exact_row_preparation','native_producer'):
            reserve=allocation;require(entry['charged_operations']is None and entry['precision']=='allocated_unverified','conservative reserved computation '+stage)
        elif entry['precision']=='independently_verified':
            which='projection' if stage=='projection_replay' else 'basis' if stage=='basis_replay' else None
            value=stored_replays.get(which) if which else check
            require(value is not None and value.get('verified')is True and stage in bindings,'refinement requires bound saved independent check '+stage)
            if which:require(value==license['replay_checks'][which] and value.get('complete')is True,'fresh complete exact replay precision '+stage)
            reserve=value['independent_audit_work_reserve'];require(type(entry['charged_operations'])is int and entry['charged_operations']==value['audit_operations'],'independent stage operation binding '+stage)
        else:
            reserve=allocation;require(entry['precision']=='allocated_unverified' and entry['charged_operations']is None,'pending replay/check full allocation');pending.append(stage)
        if stage in ('basis_replay','native_producer','native_checker'):
            needed=['projection_replay'] if stage=='basis_replay' else ['projection_replay','basis_replay']
            require(all(prior[k]['precision']=='independently_verified' for k in needed),'native execution follows fresh committed exact replay')
        require(type(entry['reserve'])is int and entry['reserve']==reserve and 0<=reserve<=allocation,'bounded native stage reserve '+stage)
        total+=reserve;prior[stage]=entry
    require(type(ledger['max_work'])is int and ledger['max_work']==LIMITS['max_work'] and type(ledger['total_work_reserve'])is int and ledger['total_work_reserve']==total and type(ledger['remaining_work'])is int and ledger['remaining_work']==LIMITS['max_work']-total,'complete native cumulative work reservation')
    # A check file may be committed before its ledger checkpoint; it still must
    # fit the recorded conservative allocation, without later admission.
    for stage,value in [('projection_replay',stored_replays.get('projection')),('basis_replay',stored_replays.get('basis')),('native_checker',check)]:
        if value is not None:
            require(stage in prior and value['independent_audit_work_reserve']<=prior[stage]['allocation'],'written check fits its pending allocation')
    return dict(total_work_reserve=total,pending_stages=pending,all_stages_committed=len(entries)==6 and not pending)


def verify_solver(solver,protocol):
    contract=protocol['solver_contract'];require(type(solver)is dict and solver.get('name')=='clarabel-native','direct native primal solver')
    options=solver.get('options');versions=solver.get('versions');require(type(options)is dict,'complete frozen solver settings')
    require(options.get('max_threads')==1 and type(options.get('time_limit'))in (int,float) and math.isfinite(options['time_limit']) and 0<=options['time_limit']<=900,'bounded native solver time/threads')
    require({k:v for k,v in options.items() if k!='time_limit'}==contract['fixed_options'],'exact default native solver protocol')
    require(versions==contract['versions'] and solver.get('versions_hash')==CORE.digest(versions) and solver.get('options_hash')==CORE.digest(options),'native version/options bindings')


def verify_job(directory,transport,protocol,source,expected,geometry,license,*,deadline,max_operations,max_cells):
    p=directory/'jobs/primal.json';record=read(p,65536) if p.exists() else None
    tracepath=directory/'jobs/primal-trace.json';trace=read(tracepath) if tracepath.exists() else None
    checkpath=directory/'jobs/primal-check.json';stored=read(checkpath) if checkpath.exists() else None
    progresspath=directory/'jobs/primal-progress.json';progress=read(progresspath) if progresspath.exists() else None
    startpath=directory/'jobs/primal-progress.json.source.json';startup=read(startpath) if startpath.exists() else None
    stored_replays={which:read(directory/'jobs'/f'{which}-replay.json') for which in ('projection','basis') if (directory/'jobs'/f'{which}-replay.json').exists()}
    for which,value in stored_replays.items():require(value==license['replay_checks'][which],'same freshly persisted exact '+which+' replay')
    ledger_bindings={which+'_replay' for which in stored_replays}
    if stored is not None:ledger_bindings.add('native_checker')
    if trace is not None or startup is not None:require(set(stored_replays)=={'projection','basis'},'native solve only after fresh saved exact authorization')
    if transport['status']=='available':
        value=transport.get('value');require(type(value)is dict and record is not None,'available native metadata required');scope(value)
        require(value.get('file')=='jobs/primal.json' and value.get('sha256')==sha(p) and value.get('status')==record.get('status') and value.get('cost')==record.get('cost'),'native transported file/status/cost')
    if record is not None:
        scope(record);require(record.get('phase')=='primal' and type(record.get('index'))is int and record['index']==0 and record.get('program')==PROGRAM and record.get('scales')==[1,2,3,5],'same historic native primal target')
        ORIGINAL.verify_worker_cost(record['cost']);ORIGINAL.verify_compilation(record,geometry)
        if 'deadline_exceeded' in record:require(type(record['deadline_exceeded'])is bool,'explicit cooperative deadline state')
        if 'case_hashes' in record:
            for k,v in expected.items():require(record.get(k)==v,'unchanged complete arithmetic source '+k)
        require(record.get('status')in ('trace_verified','missing_resource','rejected'),'diagnostic native worker outcome')
        for key,value in record.get('exact_replay_artifacts',{}).items():require(key in ('projection-replay','basis-replay') and value==dict(file=key+'.json',sha256=sha(directory/'jobs'/(key+'.json'))),'worker exact replay artifact hash')
        for key,value in record.get('artifacts',{}).items():
            name={'trace':'primal-trace.json','check':'primal-check.json'}.get(key);require(name is not None and value==dict(file=name,sha256=sha(directory/'jobs'/name)),'worker numerical artifact hash')
        if record['status']=='trace_verified':require(set(record.get('artifacts',{}))=={'trace','check'} and record.get('fresh_exact_basis_authorized')is True and record.get('selected_original_indices')==license['indices'] and set(record.get('exact_replay_artifacts',{}))=={'projection-replay','basis-replay'},'fresh original-row authorization before solver')
    trusted_sources={n:source[n] for n in ('primitive_state_basis_primal.py','primitive_state_solver_trace.py')}
    result=None;origin=None;operations=cells=0
    final=trace
    if final is None and progress is not None and progress.get('phase')=='native_returned':final=progress;origin='completed_checkpoint_without_transport_trace'
    elif final is not None:origin='final_trace'
    if final is not None:
        verify_solver(final['solver'],protocol)
        result=CORE.verify_trace(final,geometry['columns'],geometry['lhs'],geometry['domain'],geometry['shape'],geometry['offset'],ORIGINAL.B.gram_specs(),license['indices'],expected_source_hashes=trusted_sources,expected_versions=protocol['solver_contract']['versions'],deadline=deadline,max_operations=max_operations,max_cells=max_cells)
        operations=result['audit_operations'];cells=result['audit_cells']
        require(final['assembly']['limits']==dict(max_operations=LIMITS['producer_operations'],max_cells=LIMITS['max_cells'],max_coefficient_bits=LIMITS['max_coefficient_bits']),'frozen producer assembly allowance')
        if stored is not None:require(trace is not None and stored==result,'same persisted deterministic native checker')
        if trace is not None and progress is not None:require(progress==dict(trace,phase='native_returned'),'same final native progress and trace')
        logpath=directory/'jobs/primal-native.log'
        if logpath.exists():require(logpath.read_bytes()==final['retained_log']['text'].encode(),'retained native disk/text bytes')
        if record is not None and record['status']=='trace_verified':
            require(record.get('termination_status')==final['termination_status'] and record.get('raw_vector_available')==(final['original_vector']is not None) and record.get('canonical_system_independently_rebuilt')is True,'terminal native status/vector diagnostic binding')
            require(trace is not None and record.get('artifacts',{}).get('trace')==dict(file='primal-trace.json',sha256=sha(tracepath)),'completed native trace transport')
    else:
        require(stored is None,'no independent native check without final trace')
        if record is not None:require(record['status']!='trace_verified','no fabricated completed numerical trace')
    if startup is not None:
        require(startup.get('schema')=='primitive-state-basis-primal-v1' and startup.get('phase')=='assembled' and startup.get('original_vector')is None,'durable source checkpoint before native solve')
        scope(startup);verify_solver(startup['solver'],protocol)
        if final is not None:require(startup['assembly']==final['assembly'] and startup['source_hashes']==final['source_hashes'],'unchanged startup/final canonical assembly')
        else:
            rebuilt=CORE.reconstruct(geometry['columns'],geometry['lhs'],geometry['domain'],geometry['shape'],geometry['offset'],ORIGINAL.B.gram_specs(),license['indices'],deadline=deadline,max_operations=max_operations-operations,max_cells=max_cells-cells)
            for k,v in rebuilt['receipt'].items():require(startup.get('assembly',{}).get(k)==v,'independently rebuilt startup canonical '+k)
            require(startup.get('source_hashes')==trusted_sources,'startup source closure')
            operations+=rebuilt['audit_operations'];cells+=rebuilt['audit_cells']
        if progress is not None and progress.get('phase')=='native_started':
            require(progress.get('schema')==startup['schema'] and progress.get('assembly_hash')==CORE.digest(startup['assembly']) and progress.get('solver')==startup['solver'] and progress.get('original_vector')is None,'native iteration/source binding')
            scope(progress)
    elif progress is not None and progress.get('phase')=='native_started':raise ValueError('native progress requires retained source checkpoint')
    ledger=None
    if record is not None and record.get('ledger')is not None:ledger=verify_ledger(record['ledger'],geometry,license,stored_replays,stored,ledger_bindings)
    stagepath=directory/'jobs/progress.json';stageprogress=read(stagepath,65536) if stagepath.exists() else None
    progress_ledger=None;outer_partial_failure=False
    if stageprogress is not None:
        scope(stageprogress)
        for key,value in stageprogress.get('exact_replay_artifacts',{}).items():require(key in ('projection-replay','basis-replay') and value==dict(file=key+'.json',sha256=sha(directory/'jobs'/(key+'.json'))),'durable exact replay artifact binding')
        for key,value in stageprogress.get('artifacts',{}).items():
            name={'trace':'primal-trace.json','check':'primal-check.json'}.get(key);require(name is not None and value==dict(file=name,sha256=sha(directory/'jobs'/name)),'durable native artifact binding')
        progress_ledger=verify_ledger(stageprogress['ledger'],geometry,license,stored_replays,stored,ledger_bindings)
        if record is not None and record.get('ledger')is not None:
            outer_partial_failure=record['status']in ('missing_resource','rejected') and record.get('numerical_verification_pending')is True
            if outer_partial_failure:
                old=stageprogress['ledger']['entries'];new=record['ledger']['entries']
                require(len(old)<=len(new),'failure checkpoint precedes terminal ledger')
                for left,right in zip(old,new):
                    require(left['stage']==right['stage'] and left['allocation']==right['allocation'],'failure ledger keeps prior allocations')
                    if left['precision']in ('independently_verified','declared_compilation_reserve'):require(left==right,'failure keeps committed stage precision')
                    else:require(right['reserve']<=left['allocation'],'failure pending stage stays bounded')
            else:
                for key in ('ledger','status','artifacts','numerical_verification_pending'):
                    require(stageprogress.get(key)==record.get(key),'durable lifecycle/terminal metadata '+key)
        elif record is not None:
            require(record['status']in ('missing_resource','rejected'),'missing lifecycle metadata cannot imply numerical completion');outer_partial_failure=True
    available=transport['status']=='available' and record is not None and record['status']=='trace_verified'
    if available:require(result is not None and stored is not None and ledger is not None and ledger['all_stages_committed'] and stageprogress is not None and stageprogress.get('phase')=='trace_verified','complete independently checked numerical diagnostics')
    return dict(transport_status=transport['status'],worker_status=record.get('status') if record else None,trace_origin=origin,trace_check=result,
        canonical_matrix_rebuilt=result is not None or startup is not None,terminal_numerical_diagnostics_available=available,ledger=ledger,
        startup_retained=startup is not None,progress_retained=progress is not None,lifecycle_progress_retained=stageprogress is not None,progress_ledger=progress_ledger,outer_partial_failure=outer_partial_failure,audit_operations=operations,audit_cells=cells,
        mathematical_feasibility='UNKNOWN',accepted_proposal=False,**FLAGS)

def verify_protocol(protocol):
    # Literal runner contract is fixed before freeze; no numerical library import.
    expected=dict(schema='primitive-state-basis-primal-run-v1',program=PROGRAM,scales=[1,2,3,5],phases=['primal'],language=ORIGINAL.B.SPEC,gram_specs=ORIGINAL.B.gram_specs(),compiler_limits=COMPILER_LIMITS,limits=LIMITS,parallel=PARALLEL,tests=TESTS,parent_publication='publication-014',basis_run='primitive-state-exact-row-basis-probe-002',expected_shape=dict(original_rows=5641,original_columns=1957,selected_rows=779,scalar_offset=1597),fresh_exact_replay_required_before_solver=True,strategy='fresh independently replayed saved exact tapes; one direct native primal solve on ORIGINAL equation rows; positive augmented infinity scaling; identity full coordinates',no_refit_or_source_selection=True,historical_development_scales=True,canonical_system_independently_rebuilt=True,exact_restore_all_original_rows_required=True)
    for k,v in expected.items():require(protocol.get(k)==v,'known native primal protocol '+k)
    scope(protocol)
    require(type(protocol.get('solver_contract'))is dict,'frozen native solver contract')


def audit(directory,*,write=False,time_limit=900,max_audit_operations=450000000,max_audit_cells=60000000):
    require(type(time_limit)in (int,float) and math.isfinite(time_limit) and 0<time_limit<=900,'bounded whole-audit deadline')
    require(type(max_audit_operations)is int and 0<max_audit_operations<=450000000 and type(max_audit_cells)is int and 0<max_audit_cells<=60000000,'bounded cumulative whole-audit resources')
    d=Path(directory).resolve();target=d/'independent_verification.json';started=time.monotonic();deadline=started+time_limit
    if write and target.exists():raise FileExistsError('exclusive native primal independent review')
    protocol=read(d/'protocol.json',65536);verify_protocol(protocol)
    source=read(d/'source_seal.json',65536);require(set(source)==set(source_names()),'complete native primal source closure')
    frozen={str(p.relative_to(d/'frozen_source')) for p in (d/'frozen_source').rglob('*') if p.is_file()};require(frozen==set(source),'complete native primal frozen source inventory')
    for n,h in source.items():require(sha(path_under(ROOT,n))==h and sha(path_under(d/'frozen_source',n))==h,'immutable native primal source '+n)
    seal=read(d/'seal.json',65536)
    for n in ('protocol','source_seal','input'):require(seal.get(n+'_sha256')==sha(d/(n+'.json')),'native primal preregistration '+n)
    inputs=read(d/'input.json',65536)['input_sha256'];require(set(inputs)==set(INPUTS),'complete parent and equation license bindings')
    for n,h in inputs.items():require(sha(path_under(ROOT,n))==h,'immutable native primal input '+n)
    parent=read(ROOT/'cancellation-arithmetic-results/publication-014/manifest.json')
    for n,h in parent['files'].items():require(sha(path_under(ROOT,n))==h,'immutable publication014 '+n)
    require(read(ROOT/'cancellation-arithmetic-results/publication-014/report.json').get('schema')==14,'publication014 license parent')
    tests=read(d/'tests.json',65536);match=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',tests.get('stdout','')+tests.get('stderr',''))
    require(tests.get('returncode')==0 and match is not None,'native primal calibration passed')
    require(read(d/'run_started.json',65536)==dict(protocol_sha256=sha(d/'protocol.json')),'exclusive native primal execution')
    receipt=read(d/'receipt.json',65536);inventory=verify_inventory(d,receipt);require(receipt.get('source_count')==len(source),'native terminal source count')
    execution=read(d/'execution.json',65536);verify_runtime(execution)
    expected,geometry=ORIGINAL.rebuild();require(time.monotonic()<=deadline,'shared arithmetic geometry audit deadline')
    license=verify_license(expected,geometry,deadline=deadline,max_operations=max_audit_operations-geometry['compilation'],max_cells=max_audit_cells)
    require(protocol.get('basis_evidence')==license['evidence'],'predeclared failed-run evidence and candidate rows')
    operations=geometry['compilation']+license['audit_operations'];cells=license['audit_cells']
    trial=verify_job(d,execution['results'][0],protocol,source,expected,geometry,license,deadline=deadline,max_operations=max_audit_operations-operations,max_cells=max_audit_cells-cells)
    operations+=trial['audit_operations'];cells+=trial['audit_cells']
    for n,h in source.items():require(sha(ROOT/n)==h and sha(d/'frozen_source'/n)==h,'source changed during native replay '+n)
    for n,h in inputs.items():require(sha(ROOT/n)==h,'input changed during native replay '+n)
    for n,h in receipt['files_sha256'].items():require(sha(path_under(d,n))==h,'artifact changed during native replay '+n)
    review=dict(schema='primitive-state-basis-primal-independent-review-v1',all_passed=True,source_count=len(source),tests_passed=int(match.group(1)),arithmetic_rebuilds=1,geometry_rebuilds=1,
        original_rows=5641,original_variables=1957,licensed_selected_rows=len(license['indices']),basis_license_replay=license,trial=trial,inventory=inventory,parent_bound_files=len(parent['files']),
        independent_replay_operations=operations,independent_replay_cells=cells,elapsed_seconds=time.monotonic()-started,mathematical_feasibility='UNKNOWN',
        numerical_diagnostics_only=True,canonical_primal_matrix_independently_rebuilt=trial['canonical_matrix_rebuilt'],
        input_sha256={n:sha(d/n) for n in ['protocol.json','source_seal.json','input.json','seal.json','tests.json','execution.json','receipt.json']},**FLAGS)
    if write:
        with target.open('x') as stream:json.dump(review,stream,sort_keys=True,indent=2,allow_nan=False);stream.write('\n')
    return review


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('directory');parser.add_argument('--write',action='store_true');args=parser.parse_args()
    print(json.dumps(audit(args.directory,write=args.write),sort_keys=True))

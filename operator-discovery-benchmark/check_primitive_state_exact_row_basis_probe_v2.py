"""Independent whole archive audit of exact row-span preprocessing only.

One arithmetic/geometry rebuild feeds exact column-identity and row-basis
replays. Worker UNKNOWN or failed transport never becomes reduction admission.
Imports neither this stage's runner/producer nor a numerical solver.
"""
import argparse
import ast
import json
import math
from pathlib import Path
import re
import time
import check_primitive_state_solver_trace_run as ORIGINAL
import check_primitive_state_equation_projection as PROJECT
import check_primitive_state_exact_row_basis as BASIS

ROOT=Path(__file__).resolve().parent
PROGRAM=dict(ORIGINAL.PROGRAM)
COMPILER_LIMITS=dict(ORIGINAL.COMPILER_LIMITS)
FLAGS=dict(BASIS.FLAGS)
LIMITS=dict(cooperative_seconds=900,max_work=450000000,projection_operations=50000000,
    basis_operations=175000000,max_source_cells=4000000,max_live_cells=4000000,
    max_fill_cells=20000000,max_coefficient_bits=4096,max_receipt_bytes=33554432,
    max_metadata_bytes=65536,max_audit_cells=60000000)
PARALLEL=dict(workers=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,
    timeout_seconds=1800,max_jobs=1,max_result_bytes=65536)
TESTS=['test_primitive_state_equation_projection','test_check_primitive_state_equation_projection',
    'test_primitive_state_exact_row_basis','test_check_primitive_state_exact_row_basis',
    'test_run_primitive_state_exact_row_basis_probe','test_check_primitive_state_exact_row_basis_probe',
    'test_run_primitive_state_exact_row_basis_probe_v2','test_check_primitive_state_exact_row_basis_probe_v2']
INPUTS=['cancellation-arithmetic-results/publication-013/manifest.json',
    'cancellation-arithmetic-results/publication-013/report.json','primitive_state_exact_basis_resource_scope_v2.txt',
    *['cancellation-arithmetic-results/primitive-state-exact-row-basis-probe-001/'+n for n in
      ['protocol.json','seal.json','receipt.json','independent_verification.json','jobs/primal.json','jobs/projection.json','jobs/basis.json']]]
EXPECTED_SHAPE=dict(original_rows=5641,original_columns=1957,projected_columns=1224,omitted_columns=733)
ARTIFACTS=['projection','projection-check','basis','basis-check']
STAGES=['compilation','projection_producer','projection_checker','basis_producer','basis_checker']
PHASES=['prepared_source','projection_started','projection_returned','projection_check_started','projection_unknown',
    'projection_verified','basis_started','basis_returned','basis_check_started','basis_unknown','basis_verified','missing_resource','rejected']
sha,path_under=ORIGINAL.sha,ORIGINAL.path_under


def read(path,max_bytes=33554432):
    return ORIGINAL.read(path,max_bytes)


def require(condition,message):
    if not condition:raise ValueError(message)


def scope(record):
    ORIGINAL.scope(record,required=True)
    if 'exact_admission' in record:require(record['exact_admission']is False,'no exact admission in preprocessing')
    if 'solver_called' in record:require(record['solver_called']is False,'preprocessing calls no numerical solver')


def source_names():
    pending=['run_primitive_state_exact_row_basis_probe_v2','check_primitive_state_exact_row_basis_probe_v2',*TESTS];seen=set()
    while pending:
        name=pending.pop();p=ROOT/(name+'.py')
        if name in seen or not p.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(p.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def verify_protocol(protocol):
    expected=dict(schema='primitive-state-exact-row-basis-probe-v2',program=PROGRAM,scales=[1,2,3,5],
        phases=['primal_preprocessing'],language=ORIGINAL.B.SPEC,gram_specs=ORIGINAL.B.gram_specs(),compiler_limits=COMPILER_LIMITS,
        limits=LIMITS,parallel=PARALLEL,tests=TESTS,parent_publication='publication-013',expected_shape=EXPECTED_SHAPE,
        strategy='verify full15 column identities, exact augmented row basis, independent replay; no solver',
        solver_called=False,no_refit_or_source_selection=True,historical_development_scales=True)
    for key,value in expected.items():require(protocol.get(key)==value,'known exact preprocessing protocol '+key)
    scope(protocol);return True



def verify_continuation(protocol):
    prior=ROOT/'cancellation-arithmetic-results/primitive-state-exact-row-basis-probe-001'
    expected=dict(prior_run=prior.name,changed_limits=dict(max_receipt_bytes=dict(prior=8388608,current=33554432)),
        algorithms_ordering_objective_cones_unchanged=True,comparison_location='independent whole-stage audit; worker pipeline unchanged',prior_run_seal_sha256=sha(prior/'seal.json'),
        prior_run_receipt_sha256=sha(prior/'receipt.json'),prior_run_review_sha256=sha(prior/'independent_verification.json'))
    require(protocol.get('continuation')==expected and json.dumps(protocol.get('continuation'),sort_keys=True)==json.dumps(expected,sort_keys=True),'bound receipt-cap-only continuation')
    previous=read(prior/'protocol.json',65536)
    import check_primitive_state_exact_row_basis_probe as V1
    V1.verify_protocol(previous)
    old_limits=dict(previous['limits']);old_limits['max_receipt_bytes']=33554432
    require(old_limits==LIMITS,'only receipt byte limit changes')
    seal=read(prior/'seal.json',65536)
    for name in ('protocol','source_seal','input'):
        require(seal.get(name+'_sha256')==sha(prior/(name+'.json')),'previous frozen seal '+name)
    terminal=read(prior/'receipt.json',65536);V1.verify_inventory(prior,terminal)
    review=read(prior/'independent_verification.json')
    require(review.get('all_passed')is True and review.get('schema')=='primitive-state-exact-row-basis-probe-independent-review-v1'
        and review.get('equation_reduction_verified')is False,'independently audited previous UNKNOWN stage')
    scope(review)
    names={'protocol.json','source_seal.json','input.json','seal.json','tests.json','execution.json','receipt.json'}
    require(set(review.get('input_sha256',{}))==names,'complete previous review input bindings')
    for name,h in review['input_sha256'].items():require(sha(path_under(prior,name))==h,'previous review input '+name)
    basis=read(prior/'jobs/basis.json',8388608);projection=read(prior/'jobs/projection.json',8388608)
    require(basis.get('complete')is False and basis.get('reason')=='receipt byte cap','actual recorded receipt-cap block')
    require(projection.get('complete')is True and review.get('artifact_replays',{}).get('projection',{}).get('projection_authorized')is True,'previous independently verified projection')
    return expected

def verify_inventory(directory,receipt):
    scope(receipt)
    require(receipt.get('solver_called')is False,'terminal no-solver scope')
    allowed={'protocol.json','source_seal.json','input.json','seal.json','run_started.json','tests.json','execution.json'}
    jobs=['jobs/primal.json','jobs/progress.json']+['jobs/'+name+'.json' for name in ARTIFACTS]
    allowed.update(jobs);allowed.update(name+'.tmp' for name in jobs)
    actual={str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file() and 'frozen_source' not in p.relative_to(directory).parts}
    actual-={'receipt.json','independent_verification.json'}
    require(not actual-allowed,'declared preprocessing artifact inventory')
    entries=receipt.get('files_sha256');require(type(entries)is dict and set(entries)==actual,'complete terminal artifact receipt')
    total_bytes=0
    for name,h in entries.items():
        p=path_under(directory,name);require(sha(p)==h,'terminal artifact hash '+name)
        base=name[:-4] if name.endswith('.tmp') else name
        cap=LIMITS['max_receipt_bytes'] if base in {'jobs/'+n+'.json' for n in ARTIFACTS} else LIMITS['max_metadata_bytes']
        require(p.stat().st_size<=cap,'bounded preprocessing artifact '+name);total_bytes+=p.stat().st_size
    return dict(files=len(entries),bytes=total_bytes)


def verify_runtime(execution):
    require(type(execution)is dict and type(execution.get('results'))is list and len(execution['results'])==1,'one predeclared preprocessing job')
    cost=execution.get('cost',{})
    for key,value in dict(requested_workers=1,workers=1,worker_memory_bytes=3*1024**3,memory_budget_bytes=3*1024**3,
            worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False,start_method='spawn',max_in_flight=1).items():
        require(type(cost.get(key))is type(value) and cost[key]==value,'single process resource contract '+key)
    row=execution['results'][0]
    require(type(row)is dict and type(row.get('index'))is int and row['index']==0 and row.get('status')in ('available','missing_resource','error'),'ordered transport status')
    if row['status']!='available':require('value' not in row,'unavailable process cannot invent returned metadata')
    for key in ('elapsed_seconds','result_bytes','payload_bytes'):
        value=cost.get(key);require(type(value)in (int,float) and math.isfinite(value) and value>=0,'finite process cost '+key)
    require(cost['result_bytes']<=65536+4096,'transport byte bound')
    for key,status in [('available','available'),('missing','missing_resource'),('errors','error')]:require(cost.get(key)==int(row['status']==status),'transport count '+key)
    return True


def projected_system(geometry,retained):
    positions={m:i for i,m in enumerate(geometry['domain'])};rows=[{} for _ in positions]
    for new,old in enumerate(retained):
        for label,q in geometry['columns'][old].items():
            if q:rows[positions[label]][new]=q
    rhs=[geometry['lhs'].get(label,BASIS.F(0)) for label in geometry['domain']]
    return rows,rhs


def producer_limits(stage):
    result=dict(max_operations=LIMITS[stage+'_operations'],max_source_cells=LIMITS['max_source_cells'],
        max_live_cells=LIMITS['max_live_cells'],max_coefficient_bits=LIMITS['max_coefficient_bits'],max_receipt_bytes=LIMITS['max_receipt_bytes'])
    if stage=='basis':result['max_fill_cells']=LIMITS['max_fill_cells']
    return result


def verify_stage_artifacts(directory,geometry,*,deadline=None,max_audit_operations=450000000,max_audit_cells=60000000):
    budget=BASIS.Budget(deadline,max_audit_operations,max_audit_cells,LIMITS['max_coefficient_bits'])
    retained,recipes=PROJECT.full15_recipes(geometry['shape'],geometry['offset'],ORIGINAL.B.gram_specs(),len(geometry['columns']))
    values={name:read(directory/'jobs'/f'{name}.json') for name in ARTIFACTS if (directory/'jobs'/f'{name}.json').exists()}
    checks={};rows=rhs=None
    projection=values.get('projection')
    if projection is not None:
        if 'limits' in projection:require(projection['limits']==producer_limits('projection'),'frozen projection producer allocation/caps')
        if projection.get('complete')is True:
            assembly=len(geometry['domain'])+sum(len(geometry['columns'][j]) for j in retained)
            budget.charge(assembly,cells=assembly);rows,rhs=projected_system(geometry,retained)
        checks['projection']=PROJECT.verify_projection(geometry['columns'],geometry['lhs'],geometry['domain'],retained,recipes,rows,rhs,projection,
            deadline=deadline,max_audit_operations=max_audit_operations-budget.operations,max_audit_cells=max_audit_cells-budget.cells,max_receipt_bytes=LIMITS['max_receipt_bytes'],authorized_limits=producer_limits('projection'))
        budget.charge(checks['projection']['audit_operations'],cells=checks['projection']['audit_cells'])
    if 'projection-check' in values:
        require(projection is not None,'projection check requires its source receipt')
        require(values['projection-check']==checks['projection'],'same deterministic worker projection check')
        scope(values['projection-check'])
    if 'basis' in values:
        require(projection is not None and projection.get('complete')is True and checks['projection']['projection_authorized']is True
            and 'projection-check' in values and values['projection-check'].get('complete')is True,'basis execution requires complete WORKER projection check')
        basis=values['basis']
        if 'limits' in basis:require(basis['limits']==producer_limits('basis'),'frozen basis producer allocation/caps')
        selected=targets=None
        if basis.get('complete')is True:
            indices=basis.get('retained_indices')
            require(type(indices)is list and all(type(i)is int and 0<=i<len(rows) for i in indices),'complete retained original equation indices')
            selected=[rows[i] for i in indices];targets=[rhs[i] for i in indices]
        checks['basis']=BASIS.verify_rows(rows,rhs,len(retained),selected,targets,basis,
            deadline=deadline,max_audit_operations=max_audit_operations-budget.operations,max_audit_cells=max_audit_cells-budget.cells,max_receipt_bytes=LIMITS['max_receipt_bytes'],authorized_limits=producer_limits('basis'))
        budget.charge(checks['basis']['audit_operations'],cells=checks['basis']['audit_cells'])
        require(basis.get('source_hash')is None or basis['source_hash']==projection['projected_rows_hash'],'complete projected/basis source binding')
    if 'basis-check' in values:
        require('basis' in values,'basis check requires source tape');scope(values['basis-check'])
        require(values['basis-check']==checks['basis'],'same deterministic worker basis check')
    return dict(values=values,checks=checks,retained=retained,recipes=recipes,projected_rows=rows,projected_rhs=rhs,
        audit_operations=budget.operations,audit_cells=budget.cells,independent_audit_work_reserve=budget.operations+sum(len(BASIS.encoded(value)) for value in values.values())+1)


def artifact_bindings(directory,artifacts):
    require(type(artifacts)is dict and set(artifacts)<=set(ARTIFACTS),'bounded known stage artifact references')
    for name,value in artifacts.items():
        require(type(value)is dict and value==dict(file=name+'.json',sha256=sha(directory/'jobs'/f'{name}.json')),'stage artifact hash '+name)
    return True


def verify_ledger(ledger,geometry,artifacts,bindings):
    require(type(ledger)is dict and set(ledger)=={'max_work','total_work_reserve','remaining_work','entries'},'complete work ledger')
    require(type(ledger['max_work'])is int and ledger['max_work']==LIMITS['max_work'],'frozen total preprocessing work')
    entries=ledger['entries'];require(type(entries)is list and 1<=len(entries)<=5,'bounded ordered work ledger')
    require([e.get('stage') for e in entries]==STAGES[:len(entries)],'ordered unique work stages')
    values=artifacts['values'];checks=artifacts['checks'];total=0;prior={}
    pending=[]
    for i,entry in enumerate(entries):
        require(type(entry)is dict and set(entry)=={'stage','allocation','reserve','charged_operations','precision'},'complete stage allocation')
        stage=entry['stage']
        require(type(entry['allocation'])is int and entry['allocation']>0 and type(entry['reserve'])is int and 0<=entry['reserve']<=entry['allocation'],'strict bounded allocation and reserve')
        if stage=='compilation':
            expected=dict(stage=stage,allocation=geometry['compilation'],reserve=geometry['compilation'],charged_operations=geometry['compilation'],precision='declared_compilation_reserve')
            require(entry==expected,'independent compilation reserve')
        else:
            remaining=LIMITS['max_work']-total
            if stage=='projection_producer':allocation=LIMITS['projection_operations']
            elif stage=='projection_checker':allocation=remaining-LIMITS['basis_operations']
            elif stage=='basis_producer':allocation=LIMITS['basis_operations']
            else:allocation=remaining
            # Producer refinements can precede the final snapshot. The checker
            # allocation was made while its producer still reserved its FULL cap.
            if stage in ('projection_checker','basis_checker'):
                producer_stage=stage.replace('checker','producer');producer=prior[producer_stage]
                allocation-=producer['allocation']-producer['reserve']
            require(entry['allocation']==allocation and allocation>0 and allocation<=remaining,'deterministic allocation '+stage)
            if entry['precision']=='allocated_unverified':
                require(entry['reserve']==entry['allocation'] and entry['charged_operations']is None,'pending stages retain full allocation')
                pending.append(stage)
            elif entry['precision']=='independently_verified':
                which='projection' if stage.startswith('projection') else 'basis'
                require(which+'-check' in values and which+'-check' in bindings and values[which+'-check'].get('verified')is True,'precision follows retained WORKER check '+stage)
                if stage.endswith('producer'):
                    require(values[which].get('complete')is True and values[which+'-check'].get('complete')is True,'producer precision requires COMPLETE corresponding worker check')
                    reserve=operations=values[which]['counts']['operations']
                else:reserve=checks[which]['independent_audit_work_reserve'];operations=checks[which]['audit_operations']
                require(entry['reserve']==reserve and type(entry['charged_operations'])is int and entry['charged_operations']==operations,'independently replayed work precision '+stage)
            else:raise ValueError('known work precision state')
            if stage in ('basis_producer','basis_checker'):
                require(prior['projection_producer']['precision']==prior['projection_checker']['precision']=='independently_verified'
                    and checks.get('projection',{}).get('complete')is True,'basis follows complete committed projection checks')
        total+=entry['reserve'];require(total<=LIMITS['max_work'],'cumulative preprocessing reserve ceiling');prior[stage]=entry
    require(type(ledger['total_work_reserve'])is int and ledger['total_work_reserve']==total
        and type(ledger['remaining_work'])is int and ledger['remaining_work']==LIMITS['max_work']-total,'complete cumulative work ledger')
    # Any recorded worker checker must fit the allocation that it was given,
    # even if an atomic-write crash prevented ledger precision commitment.
    for which in ('projection','basis'):
        if which+'-check' in values:
            stage=which+'_checker';require(stage in prior,'worker check has a recorded prior allocation')
            source_cells=(sum(map(len,geometry['columns']))+len(geometry['lhs'])+sum(map(len,artifacts['projected_rows'] or [])) if which=='projection'
                else sum(map(len,artifacts['projected_rows']))+len(artifacts['projected_rhs']))
            audit_ops=prior[stage]['allocation']-LIMITS['max_receipt_bytes']-source_cells-1
            require(checks[which]['audit_operations']<=audit_ops and checks[which]['independent_audit_work_reserve']<=prior[stage]['allocation'],'recorded independent check fits its original allocation')
    return dict(verified=True,total_work_reserve=total,remaining_work=LIMITS['max_work']-total,pending_stages=pending,
        all_stages_committed=len(entries)==5 and not pending)


def verify_state(directory,state,geometry,artifacts, *, progress=False):
    require(type(state)is dict,'explicit retained preprocessing state');scope(state)
    status=state.get('status');require(status in ('unknown','missing_resource','rejected','basis_verified'),'nonadmitted preprocessing outcome')
    bindings=state.get('artifacts',{});artifact_bindings(directory,bindings)
    ledger=state.get('ledger')
    if ledger is None:
        require(not bindings and state.get('equation_reduction_verified')is False and state.get('selected_original_row_indices')is None
            and status!='basis_verified','source failure cannot claim a basis')
        return dict(verified=True,ledger_retained=False,equation_reduction_verified=False)
    checked=verify_ledger(ledger,geometry,artifacts,bindings)
    entries={e['stage']:e for e in ledger['entries']}
    for which in ('projection','basis'):
        producer=entries.get(which+'_producer');checker=entries.get(which+'_checker')
        if producer and producer['precision']=='independently_verified':
            require(checker is not None and checker['precision']=='independently_verified','producer refinement follows checker commitment')
    if status=='basis_verified':
        require(checked['all_stages_committed'] and set(bindings)==set(ARTIFACTS),'complete committed worker equivalence ledger/artifacts')
        require(artifacts['checks'].get('projection',{}).get('complete')is True and artifacts['checks'].get('basis',{}).get('reduction_authorized')is True,
            'complete independent projection and basis replay')
        indices=artifacts['values']['basis']['retained_indices']
        require(state.get('equation_reduction_verified')is True and state.get('selected_original_row_indices')==indices
            and type(state.get('selected_original_row_indices'))is list and all(type(i)is int for i in state['selected_original_row_indices']),
            'same selected ORIGINAL equation indices')
        if not progress:
            for key,value in dict(original_rows=len(geometry['domain']),original_columns=len(geometry['columns']),
                    projection_columns=len(artifacts['retained']),retained_rows=len(indices),augmented_rank=len(indices),
                    inconsistent_augmented_pivots=artifacts['values']['basis']['inconsistent_augmented_pivots']).items():
                require(state.get(key)==value,'terminal complete row-basis dimensions '+key)
    else:
        require(state.get('equation_reduction_verified')is False and state.get('selected_original_row_indices')is None,
            'UNKNOWN/failed state selects no reduced equations')
    return dict(verified=True,ledger_retained=True,equation_reduction_verified=status=='basis_verified',ledger=checked)



SOURCE_BINDINGS=['ordinary_case_hashes','case_hashes','gram_block_hashes','storage_block_hashes','gram_archive_hashes',
    'factor_archive_hashes','divisor_archive_hashes','cell_archive_hashes','primitive_state_archive_hashes',
    'primitive_source_hashes','multiplier_source_hashes','dictionary_sha256','gram_specs',
    'complete_columns','complete_monomials','projected_columns','exact_columns_hash','exact_target_hash','compilation_work_reserve']
PROJECTION_BINDINGS=['full_columns_hash','monomial_domain_hash','target_hash','full_source_hash','projection_hash','projected_rows_hash']


def verify_worker_continuation(record,artifacts):
    require('continuation_comparison' not in record,'worker pipeline has no extra continuation replay')
    if 'complete_columns' not in record:
        require(record.get('status')!='basis_verified','no invented unbuilt continuation')
        return dict(original_source_compared=False)
    prior=ROOT/'cancellation-arithmetic-results/primitive-state-exact-row-basis-probe-001'
    previous=read(prior/'jobs/primal.json',65536)
    matches={key:key in record and key in previous and record[key]==previous[key] for key in SOURCE_BINDINGS}
    require(all(matches.values()),'unchanged complete original source and compilation')
    return dict(original_source_compared=True,original_source=matches)


def verify_stage_continuation(directory,artifacts,*,record=None,deadline,max_audit_operations,max_audit_cells):
    """Compare only completed old transcript records, under a separate audit reserve."""
    prior=ROOT/'cancellation-arithmetic-results/primitive-state-exact-row-basis-probe-001'
    budget=BASIS.Budget(deadline,max_audit_operations,max_audit_cells,LIMITS['max_coefficient_bits'])
    bytes_processed=0
    def encoded(value):
        nonlocal bytes_processed
        payload=BASIS.encoded(value);bytes_processed+=len(payload)
        require(bytes_processed<=83886080,'bounded auxiliary continuation encoded bytes')
        budget.charge(len(payload)//64+1,cells=len(payload))
        return payload
    values=artifacts['values'];projection=values.get('projection');basis=values.get('basis')
    if record is not None and 'complete_columns' in record:
        previous_record=read(prior/'jobs/primal.json',65536)
        for key in SOURCE_BINDINGS:
            require(encoded(record.get(key))==encoded(previous_record.get(key)),'same bound continuation source '+key)
    result=dict(comparison_location='independent whole-stage audit; worker pipeline unchanged',projection_compared=False,basis_source_order_compared=False,
        completed_prior_transcript_records_compared=0,all_completed_prior_records_covered=False)
    if projection is not None and projection.get('complete')is True:
        previous=read(prior/'jobs/projection.json',8388608)
        matches={key:encoded(projection.get(key))==encoded(previous.get(key)) for key in PROJECTION_BINDINGS+['retained_indices','recipes']}
        require(all(matches.values()),'same exact projection intrinsic system and recipes')
        result.update(projection_compared=True,projection_fields=matches)
    if basis is not None and all(key in basis for key in ('source_hash','ordering','row_order','transcript')):
        previous=read(prior/'jobs/basis.json',8388608)
        matches={key:encoded(basis[key])==encoded(previous.get(key)) for key in ('source_hash','ordering','row_order')}
        require(all(matches.values()),'same basis exact source and deterministic ordering')
        old=previous['transcript'];current=basis['transcript'];count=min(len(old),len(current))
        for index in range(count):
            require(encoded(old[index])==encoded(current[index]),'same completed old basis transcript prefix')
        if basis.get('complete')is True:require(len(current)>=len(old),'complete continuation covers old completed records')
        result.update(basis_source_order_compared=True,basis_fields=matches,completed_prior_transcript_records_compared=count,
            all_completed_prior_records_covered=count==len(old))
    elif basis is not None:require(basis.get('complete')is not True,'complete basis source/order fields')
    result.update(audit_operations=budget.operations,audit_cells=budget.cells,encoded_bytes_processed=bytes_processed,
        independent_audit_work_reserve=budget.operations+bytes_processed+1,max_encoded_bytes=83886080)
    return result


def verify_job(directory,transport,expected,geometry,artifacts):
    path=directory/'jobs/primal.json';record=read(path,LIMITS['max_metadata_bytes']) if path.exists() else None
    progress_path=directory/'jobs/progress.json';progress=read(progress_path,LIMITS['max_metadata_bytes']) if progress_path.exists() else None
    if transport['status']=='available':
        value=transport.get('value');require(type(value)is dict and record is not None,'available metadata required')
        scope(value)
        require(value.get('file')=='jobs/primal.json' and value.get('sha256')==sha(path)
            and value.get('status')==record.get('status') and value.get('cost')==record.get('cost'),'transport file/status/cost binding')
    state_check=progress_check=None;outer_failure_fallback=False;continuation_check=None
    if record is not None:
        require(record.get('phase')=='primal_preprocessing' and type(record.get('index'))is int and record['index']==0
            and record.get('program')==PROGRAM and record.get('scales')==[1,2,3,5] and record.get('solver_called')is False,'same solver-free arithmetic case')
        scope(record);ORIGINAL.verify_worker_cost(record['cost'])
        require(type(record.get('deadline_exceeded'))is bool,'explicit cooperative deadline diagnostic')
        if 'case_hashes' in record:
            for key,value in expected.items():require(record.get(key)==value,'complete original arithmetic archive '+key)
        elif record.get('status')=='basis_verified':raise ValueError('complete arithmetic metadata for verified basis')
        ORIGINAL.verify_compilation(record,geometry)
        if 'complete_columns' in record:require(record.get('projected_columns')==len(artifacts['retained']),'complete exact projection width')
        elif record.get('ledger')is not None:raise ValueError('compiled source metadata required before ledger')
        state_check=verify_state(directory,record,geometry,artifacts)
        continuation_check=verify_worker_continuation(record,artifacts)
    if progress is not None:
        require(progress.get('phase')in PHASES,'known durable preprocessing phase')
        progress_check=verify_state(directory,progress,geometry,artifacts,progress=True)
        if record is not None:
            outer_failure_fallback=record.get('ledger')is None and record.get('status')in ('missing_resource','rejected')
            if outer_failure_fallback:
                require(record.get('equation_reduction_verified')is False and record.get('selected_original_row_indices')is None,
                    'outer failure metadata cannot promote durable preprocessing')
            else:
                for key in ('ledger','status','equation_reduction_verified','selected_original_row_indices','artifacts'):
                    require(progress.get(key)==record.get(key),'durable progress/terminal state binding '+key)
                if record['status']=='basis_verified':require(progress['phase']=='basis_verified','terminal basis progress')
                if record['status']in ('missing_resource','rejected') and record.get('ledger')is not None:
                    require(progress['phase']==record['status'],'terminal retained failure progress')
    elif record is not None:require(record.get('ledger')is None,'complete metadata preserves durable progress')
    admitted=transport['status']=='available' and record is not None and record.get('status')=='basis_verified'
    return dict(transport_status=transport['status'],worker_status=record.get('status') if record else None,
        worker_state=state_check,progress=progress_check,continuation=continuation_check,outer_failure_without_process_return=outer_failure_fallback,retained_progress_phase=progress.get('phase') if progress else None,
        equation_reduction_verified=admitted,
        selected_original_row_indices=record['selected_original_row_indices'] if admitted else None,
        mathematical_feasibility='UNKNOWN',solver_called=False,**FLAGS)


def audit(directory, *, write=False,time_limit=900,max_audit_operations=450000000,max_audit_cells=60000000):
    require(type(time_limit)in (int,float) and math.isfinite(time_limit) and 0<time_limit<=900,'bounded independent audit seconds')
    require(type(max_audit_operations)is int and 1<=max_audit_operations<=450000000 and type(max_audit_cells)is int and 1<=max_audit_cells<=60000000,'bounded cumulative independent replay limits')
    started=time.monotonic();deadline=started+time_limit;d=Path(directory).resolve();target=d/'independent_verification.json'
    if write and target.exists():raise FileExistsError('exclusive independent exact preprocessing review')
    protocol=read(d/'protocol.json',LIMITS['max_metadata_bytes']);verify_protocol(protocol);verify_continuation(protocol)
    source=read(d/'source_seal.json',LIMITS['max_metadata_bytes']);seal=read(d/'seal.json',LIMITS['max_metadata_bytes'])
    require(set(source)==set(source_names()),'complete executed source closure')
    frozen={str(p.relative_to(d/'frozen_source')) for p in (d/'frozen_source').rglob('*') if p.is_file()}
    require(frozen==set(source),'complete frozen source inventory')
    for name,h in source.items():require(sha(path_under(ROOT,name))==h and sha(path_under(d/'frozen_source',name))==h,'immutable source '+name)
    for name in ['protocol','source_seal','input']:require(seal.get(name+'_sha256')==sha(d/(name+'.json')),'frozen preregistration '+name)
    inputs=read(d/'input.json',LIMITS['max_metadata_bytes']).get('input_sha256')
    require(type(inputs)is dict and set(inputs)==set(INPUTS),'complete publication/resource inputs')
    for name,h in inputs.items():require(sha(path_under(ROOT,name))==h,'immutable input '+name)
    manifest=read(ROOT/'cancellation-arithmetic-results/publication-013/manifest.json')
    require(type(manifest.get('files'))is dict and manifest['files'],'complete publication013 parent')
    for name,h in manifest['files'].items():require(sha(path_under(ROOT,name))==h,'immutable publication013 '+name)
    tests=read(d/'tests.json',LIMITS['max_metadata_bytes'])
    match=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',tests.get('stdout','')+tests.get('stderr',''))
    require(type(tests.get('returncode'))is int and tests['returncode']==0 and match is not None,'prescore tests passed')
    require(read(d/'run_started.json',LIMITS['max_metadata_bytes'])==dict(protocol_sha256=sha(d/'protocol.json')),'exclusive frozen execution')
    receipt=read(d/'receipt.json',LIMITS['max_metadata_bytes']);require(receipt.get('source_count')==len(source),'complete terminal source count')
    inventory=verify_inventory(d,receipt)
    execution=read(d/'execution.json',LIMITS['max_metadata_bytes']);verify_runtime(execution)
    expected,geometry=ORIGINAL.rebuild()
    retained,recipes=PROJECT.full15_recipes(geometry['shape'],geometry['offset'],ORIGINAL.B.gram_specs(),len(geometry['columns']))
    shape=dict(original_rows=len(geometry['domain']),original_columns=len(geometry['columns']),projected_columns=len(retained),omitted_columns=len(recipes))
    require(shape==EXPECTED_SHAPE,'complete unchanged published arithmetic shape')
    require(time.monotonic()<=deadline,'independent arithmetic/geometry audit deadline')
    artifacts=verify_stage_artifacts(d,geometry,deadline=deadline,max_audit_operations=max_audit_operations,max_audit_cells=max_audit_cells)
    check=verify_job(d,execution['results'][0],expected,geometry,artifacts)
    continuation=verify_stage_continuation(d,artifacts,record=read(d/'jobs/primal.json',65536) if (d/'jobs/primal.json').exists() else None,deadline=deadline,max_audit_operations=max_audit_operations-artifacts['audit_operations'],max_audit_cells=max_audit_cells-artifacts['audit_cells'])
    for name,h in source.items():require(sha(ROOT/name)==h and sha(d/'frozen_source'/name)==h,'source changed during replay '+name)
    for name,h in inputs.items():require(sha(ROOT/name)==h,'input changed during replay '+name)
    for name,h in receipt['files_sha256'].items():require(sha(path_under(d,name))==h,'artifact changed during replay '+name)
    review=dict(schema='primitive-state-exact-row-basis-probe-independent-review-v2',all_passed=True,source_count=len(source),
        tests_passed=int(match.group(1)),arithmetic_rebuilds=1,geometry_rebuilds=1,original_shape=shape,inventory=inventory,continuation=protocol['continuation'],
        parent_bound_files=len(manifest['files']),
        artifact_replays=artifacts['checks'],worker=check,continuation_replay=continuation,
        independent_replay_operations=artifacts['audit_operations']+continuation['audit_operations'],independent_replay_cells=artifacts['audit_cells']+continuation['audit_cells'],
        independent_replay_work_reserve=artifacts['independent_audit_work_reserve']+continuation['independent_audit_work_reserve'],
        independent_audit_limits=dict(seconds=time_limit,max_operations=max_audit_operations,max_cells=max_audit_cells),
        independent_arithmetic_geometry_rebuild_reserve=geometry['compilation'],
        equation_reduction_verified=check['equation_reduction_verified'],selected_original_row_indices=check['selected_original_row_indices'],
        solver_called=False,mathematical_feasibility='UNKNOWN',numerical_rank_cutoff_used=False,
        full_optimization_variables_and_cones_unchanged=True,
        elapsed_seconds=time.monotonic()-started,
        input_sha256={name:sha(d/name) for name in ['protocol.json','source_seal.json','input.json','seal.json','tests.json','execution.json','receipt.json']},**FLAGS)
    if write:
        with target.open('x') as stream:json.dump(review,stream,sort_keys=True,indent=2,allow_nan=False);stream.write('\n')
    return review


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('directory');parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=audit(args.directory,write=args.write)
    print(json.dumps(dict(all_passed=result['all_passed'],equation_reduction_verified=result['equation_reduction_verified'],**FLAGS),sort_keys=True))

"""Publish independently audited diagnostics on the unchanged primitive/state cone.

Publication reads completed independent evidence; it never launches a numerical
search, replays arithmetic, admits a floating vector, or infers infeasibility.
"""
import argparse
import ast
import json
from pathlib import Path
import re
import publish_cancellation_primitive_state_numerical as OLD
import check_primitive_state_solver_trace_run as CHECK
import check_primitive_state_raw_iterate as RAW

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
RUN=BASE/'primitive-state-solver-trace-001'
PREVIOUS=BASE/'publication-011'
SUPPLEMENT=BASE/'primitive-state-native-coordinate-review-001'
RAW_SOURCES=['check_primitive_state_raw_iterate.py','run_primitive_state_raw_iterate_review.py','test_check_primitive_state_raw_iterate.py']
NOTE='PRIMITIVE_STATE_SOLVER_TRACE_HANDOFF.txt'
SELF='publish_cancellation_primitive_state_solver_trace.py'
TEST='test_publish_cancellation_primitive_state_solver_trace.py'
FLAGS=dict(certified=False,exact_admission=False,infeasibility_proved=False,
           global_bound_proved=False,RH_proved=False)
read,sha,require,bind,write=OLD.read,OLD.sha,OLD.require,OLD.bind,OLD.write
SOURCE_FIELDS=['ordinary_case_hashes','case_hashes','gram_block_hashes','storage_block_hashes',
    'gram_archive_hashes','factor_archive_hashes','divisor_archive_hashes','cell_archive_hashes',
    'dictionary_sha256','gram_specs','primitive_state_archive_hashes','primitive_source_hashes','multiplier_source_hashes']


def publisher_sources():
    pending=[SELF[:-3],TEST[:-3]];seen=set()
    while pending:
        name=pending.pop();path=ROOT/(name+'.py')
        if name in seen or not path.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(name+'.py' for name in seen)


def previous_numerical_receipt(record):
    synthesis=record.get('synthesis',{});diagnostics=synthesis.get('diagnostics',{})
    proposal=synthesis.get('proposal_diagnostics',diagnostics.get('proposal_diagnostics',diagnostics.get('numerical_proposal')))
    if type(proposal)is not dict or type(proposal.get('transformation_receipt'))is not dict:
        raise ValueError('complete prior original-system numerical receipt')
    return proposal['transformation_receipt']


def unchanged_sources(record,trace,previous):
    comparisons=dict(arithmetic_archive_metadata_compared=False,original_equations_compared=False)
    if record is not None:
        require(record.get('program')==previous.get('program') and record.get('scales')==previous.get('scales'),
                'same historical arithmetic program and scales')
        if 'case_hashes' in record:
            for key in SOURCE_FIELDS:require(record.get(key)==previous.get(key),'unchanged complete arithmetic '+key)
            comparisons['arithmetic_archive_metadata_compared']=True
    if trace is not None:
        receipt=trace.get('transformation_receipt')
        require(type(receipt)is dict,'retained complete original-equation receipt')
        old=previous_numerical_receipt(previous)
        for key in ('original_hash','original_rows','variables'):
            require(receipt.get(key)==old.get(key),'identical original numerical equations '+key)
        comparisons['original_equations_compared']=True
    return comparisons


def completed_archive():
    # Validate recorded receipts only. CHECK.audit intentionally is not invoked.
    import run_primitive_state_solver_trace as S
    S.validate(RUN)
    protocol=CHECK.read(RUN/'protocol.json',CHECK.CAPS['metadata']);CHECK.verify_protocol(protocol)
    source=CHECK.read(RUN/'source_seal.json',CHECK.CAPS['metadata'])
    require(set(source)==set(CHECK.source_names(CHECK.TESTS))==set(S.sources()),'complete independent source closure')
    bind(ROOT,source);bind(RUN/'frozen_source',source)
    require({str(p.relative_to(RUN/'frozen_source')) for p in (RUN/'frozen_source').rglob('*') if p.is_file()}==set(source),
        'complete frozen source inventory')
    receipt=CHECK.read(RUN/'receipt.json',CHECK.CAPS['metadata']);CHECK.scope(receipt,required=True)
    CHECK.verify_inventory(RUN,receipt)
    require(receipt.get('source_count')==len(source),'terminal source count')
    review=CHECK.read(RUN/'independent_verification.json')
    require(review.get('schema')=='primitive-state-solver-trace-independent-review-v1' and review.get('all_passed')is True,
        'completed independent diagnostic review')
    CHECK.scope(review,required=True)
    require(review.get('mathematical_feasibility')=='UNKNOWN' and review.get('numerical_diagnostics_only')is True
        and review.get('canonical_primal_matrix_independently_rebuilt')is False,'nonadmission review scope')
    require(type(review.get('arithmetic_rebuilds'))is int and type(review.get('geometry_rebuilds'))is int
        and review['arithmetic_rebuilds']==review['geometry_rebuilds']==1 and review.get('source_count')==len(source),
        'complete shared arithmetic replay')
    expected_inputs={'protocol.json','source_seal.json','input.json','seal.json','tests.json','execution.json','receipt.json'}
    require(set(review.get('input_sha256',{}))==expected_inputs,'complete independent review input binding')
    bind(RUN,review['input_sha256'])
    execution=CHECK.read(RUN/'execution.json',CHECK.CAPS['metadata']);CHECK.verify_runtime(execution)
    tests=CHECK.read(RUN/'tests.json',CHECK.CAPS['metadata'])
    match=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',tests.get('stdout','')+tests.get('stderr',''))
    require(type(tests.get('returncode'))is int and tests['returncode']==0 and match is not None,'successful prescore calibration')
    require(CHECK.read(RUN/'run_started.json',CHECK.CAPS['metadata'])==dict(protocol_sha256=sha(RUN/'protocol.json')),
        'exclusive preregistered execution')
    checks=review.get('checks')
    require(type(checks)is list and [c.get('phase') for c in checks]==CHECK.PHASES,'both ordered independent diagnostic outcomes')
    jobs=[]
    for i,phase in enumerate(CHECK.PHASES):
        transport=execution['results'][i];check=checks[i]
        CHECK.scope(check,required=True)
        require(check.get('transport_status')==transport['status'] and check.get('unknown_mathematical_feasibility')is True,
            'independent transport/scope binding')
        path=RUN/f'jobs/{phase}.json';record=CHECK.read(path,CHECK.CAPS['metadata']) if path.exists() else None
        if record is not None:
            CHECK.scope(record,required=True);CHECK.verify_worker_cost(record['cost'])
            require(record.get('phase')==phase and record.get('index')==i and record.get('status')in ('trace_available','missing_resource','rejected'),
                'retained nonadmitted worker record')
            require(check.get('worker_status')==record['status'],'independent retained worker status')
            if 'complete_columns' in record:
                require(record['complete_columns']==review['complete_original_columns'] and record['complete_monomials']==review['complete_original_monomials'],
                    'complete independently rebuilt dimensions')
        else:require(check.get('worker_status')is None,'no invented missing worker metadata')
        if transport['status']=='available':
            value=transport['value'];CHECK.scope(value,required=True)
            require(record is not None and value.get('file')==str(path.relative_to(RUN)) and value.get('sha256')==sha(path)
                and value.get('status')==record['status'] and value.get('cost')==record['cost'],'transported metadata binding')
        tracepath=RUN/f'jobs/{phase}-trace.json';trace=CHECK.read(tracepath,CHECK.CAPS['trace']) if tracepath.exists() else None
        require(check.get('trace_retained')==(trace is not None),'independent trace presence binding')
        if trace is not None:
            CHECK.scope(trace);CHECK.verify_solver(trace,phase,protocol)
            require(trace.get('vector_role')in ('raw_failed_last_iterate','unavailable'),'raw diagnostics never an accepted proposal')
            require(type(check.get('trace_check'))is dict and check['trace_check'].get('verified')is True,'independent complete trace replay')
            CHECK.scope(check['trace_check'],required=True)
            if record is not None and record['status']=='trace_available':
                require(record.get('trace_file')==str(tracepath.relative_to(RUN)) and record.get('trace_sha256')==sha(tracepath),'retained final trace hash')
        elif record is not None:require(record['status']!='trace_available','no completed trace invented')
        progress=check.get('progress');require(type(progress)is dict,'independent durable progress review')
        progresspath=RUN/f'jobs/{phase}-progress.json';sourcepath=Path(str(progresspath)+'.source.json')
        require(progress.get('retained')==(progresspath.exists() or sourcepath.exists()),'durable progress presence binding')
        retained_progress=CHECK.read(progresspath if progresspath.exists() else sourcepath) if progress.get('retained') else None
        retained_trace=trace
        if retained_progress is not None and retained_progress.get('kind')in ('support','primal'):
            if trace is not None:require(retained_progress==trace,'same retained final trace and progress')
            else:
                retained_trace=retained_progress
                require(type(progress.get('checkpoint_trace_check'))is dict and progress['checkpoint_trace_check'].get('verified')is True,
                    'terminal checkpoint independently replayed despite unavailable transport')
        if retained_trace is None and sourcepath.exists():retained_trace=CHECK.read(sourcepath)
        elif retained_trace is None and retained_progress is not None and 'transformation_receipt' in retained_progress:retained_trace=retained_progress
        previous=read(OLD.RUN/f'jobs/{phase}-000.json')
        comparisons=unchanged_sources(record,retained_trace,previous)
        jobs.append(dict(phase=phase,transport=transport,record=record,trace=trace,retained_trace=retained_trace,
            check=check,source_comparisons=comparisons))
    return dict(protocol=protocol,review=review,source=source,receipt=receipt,execution=execution,
        tests_passed=int(match.group(1)),jobs=jobs)


def coordinate_supplement():
    report=CHECK.read(SUPPLEMENT/'report.json')
    require(report.get('schema')=='primitive-state-native-coordinate-independent-review-v1' and report.get('all_passed')is True,
        'completed independent native-coordinate review')
    CHECK.scope(report,required=True)
    require(report.get('canonical_matrix_independently_rebuilt')is False,'canonical matrix remains independently unreconstructed')
    for key,value in dict(canonical_variable_map_independently_derived=False,original_trace_modified=False,
            solver_rerun=False,refitted=False,numerical_diagnostics_only=True,mathematical_feasibility='UNKNOWN',
            scalar_projection_was_applied_to_archived_vector=True).items():
        require(report.get(key)==value and type(report.get(key))is type(value),'native coordinate review scope '+key)
    require(type(report.get('full_arithmetic_rebuilds'))is int and report['full_arithmetic_rebuilds']==1
        and type(report.get('geometry_rebuilds'))is int and report['geometry_rebuilds']==1,'one corrected complete arithmetic replay')
    source=report.get('source_sha256')
    require(type(source)is dict and set(source)==set(RAW_SOURCES),'complete separately bound native replay sources')
    bind(ROOT,source);bind(SUPPLEMENT/'frozen_source',source)
    frozen={str(p.relative_to(SUPPLEMENT/'frozen_source')) for p in (SUPPLEMENT/'frozen_source').rglob('*') if p.is_file()}
    require(frozen==set(source),'complete native replay frozen source inventory')
    expected={str((RUN/name).relative_to(ROOT)) for name in ['receipt.json','independent_verification.json','protocol.json','source_seal.json',
        'jobs/primal-trace.json','jobs/primal.json']}
    inputs=report.get('input_sha256')
    require(type(inputs)is dict and set(inputs)==expected,'complete native coordinate replay input binding')
    for name in inputs:CHECK.path_under(ROOT,name)
    bind(ROOT,inputs)
    seal=CHECK.read(SUPPLEMENT/'seal.json');files=seal.get('files_sha256')
    actual={str(p.relative_to(SUPPLEMENT)) for p in SUPPLEMENT.rglob('*') if p.is_file()}-{'seal.json'}
    expected_files={'input.json','report.json','tests.json'}|{'frozen_source/'+name for name in RAW_SOURCES}
    require(actual==expected_files,'complete declared native replay artifacts')
    input_record=CHECK.read(SUPPLEMENT/'input.json')
    CHECK.scope(input_record,required=True)
    require(input_record.get('source_sha256')==source and input_record.get('input_sha256')==inputs,'same native replay prepared and final bindings')
    CHECK.scope(seal,required=True)
    require(type(files)is dict and set(files)==actual,'complete native replay terminal seal')
    for name in files:CHECK.path_under(SUPPLEMENT,name)
    bind(SUPPLEMENT,files)
    tests=CHECK.read(SUPPLEMENT/'tests.json')
    match=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',tests.get('stdout','')+tests.get('stderr',''))
    require(type(tests.get('returncode'))is int and tests['returncode']==0 and match is not None and int(match.group(1))==7,
        'native transport calibration tests passed')
    trace=CHECK.read(RUN/'jobs/primal-trace.json')
    require(type(report.get('tests_passed'))is int and report['tests_passed']==7,'declared native transport calibration count')
    require(report.get('original_trace_sha256')==sha(RUN/'jobs/primal-trace.json')
        and report.get('original_system_hash')==trace['original_system_hash']
        and report.get('exact_equation_source_hash')==trace['transformation_receipt']['original_hash']
        and report.get('native_termination_status')==trace['termination_status'],'unaltered primal trace provenance')
    coordinate=report.get('coordinate_replay')
    require(type(coordinate)is dict and coordinate==RAW.replay(trace),'independently replayed complete native-coordinate transport')
    CHECK.scope(coordinate,required=True)
    corrected=report.get('corrected_original_equation_check')
    require(type(corrected)is dict and corrected.get('verified')is True,'corrected original-coordinate equation replay')
    CHECK.scope(corrected,required=True)
    require(corrected.get('canonical_system_independently_rebuilt')is False,'corrected canonical matrix remains producer-bound')
    receipt=trace['transformation_receipt'];transformation=corrected.get('transformation',{})
    for key,value in [('original_rows',receipt['original_rows']),('reduced_rows',len(receipt['retained_indices'])),('variables',receipt['variables'])]:
        require(transformation.get(key)==value,'corrected original equation dimensions '+key)
    require(corrected.get('diagnostics',{}).get('nonnegative_min')==coordinate['raw_nonnegative_min'],
        'corrected scalar signs bind raw native coordinates')
    return dict(report=report,source=source,tests_passed=int(match.group(1)))


def load_inputs():
    prior=OLD.load_inputs()
    manifest=read(PREVIOUS/'manifest.json');bind(ROOT,manifest['files'])
    require(read(PREVIOUS/'report.json').get('schema')==11,'publication011 parent')
    stage=completed_archive();oldspec=read(OLD.RUN/'protocol.json');spec=stage['protocol']
    for key in ('program','language','gram_specs'):require(spec.get(key)==oldspec.get(key),'unchanged mathematical cone '+key)
    require(spec['scales']==oldspec['training_scales'],'unchanged historical development grid')
    priors=dict(prior['priors']);priors['publication-011']=dict(manifest_sha256=sha(PREVIOUS/'manifest.json'),bound_files=len(manifest['files']))
    return dict(priors=priors,stage=stage,coordinate_supplement=coordinate_supplement())


def report(inputs):
    stage=inputs['stage'];rows=[]
    for job in stage['jobs']:
        phase=job['phase'];record=job['record'];trace=job['trace'];retained=job['retained_trace'];check=job['check']
        independent=check.get('trace_check') or check['progress'].get('checkpoint_trace_check')
        row=dict(phase=phase,transport_status=job['transport']['status'],worker_status=record['status'] if record else None,
            reason=record.get('reason') if record else job['transport'].get('reason'),cost=record.get('cost') if record else None,
            complete_trace_retained=trace is not None,progress=check['progress'],unchanged_source_comparisons=job['source_comparisons'])
        if record is not None:row.update(file=f'jobs/{phase}.json',sha256=sha(RUN/f'jobs/{phase}.json'))
        if retained is not None:
            row['solver']=retained.get('solver');row['termination_status']=retained.get('termination_status')
            row['termination_message']=retained.get('termination_message');row['error']=retained.get('error')
            row['archived_producer_vector_role']=retained.get('vector_role');row['archived_complete_coordinate_vector_present']=retained.get('original_vector')is not None
            receipt=retained.get('transformation_receipt',{})
            row['equations']=dict(original_rows=receipt.get('original_rows'),retained_rows=len(receipt.get('retained_indices',[])),
                original_variables=receipt.get('variables'),original_system_sha256=receipt.get('original_hash'),
                compression_operations=receipt.get('operations'),source_cells=receipt.get('cells'))
            row['native_termination_info']=retained.get('raw_info');row['native_iteration_info']=retained.get('raw_solution',{}).get('iterations')
            log=retained.get('retained_log')
            if log is not None:row['native_log']={k:v for k,v in log.items() if k!='text'}
        progresspath=RUN/f'jobs/{phase}-progress.json'
        if progresspath.exists():
            progress_record=CHECK.read(progresspath)
            row['retained_progress_file']=dict(file=str(progresspath.relative_to(RUN)),sha256=sha(progresspath))
            if 'raw_info' in progress_record:row['retained_native_progress_info']=progress_record['raw_info']
        sourcepath=Path(str(progresspath)+'.source.json')
        if sourcepath.exists():row['retained_startup_source_file']=dict(file=str(sourcepath.relative_to(RUN)),sha256=sha(sourcepath))
        logpath=RUN/f'jobs/{phase}-native.log'
        if logpath.exists():row['retained_native_log_file']=dict(file=str(logpath.relative_to(RUN)),sha256=sha(logpath),bytes=logpath.stat().st_size)
        if independent is not None:
            row['archived_vector_independent_residuals_and_signs']=independent.get('diagnostics')
            row['independent_coefficient_ranges']=independent.get('coefficient_metrics')
            row['diagnostic_rounding']=independent.get('rounding')
            row['independent_resource_proxies']={k:independent[k] for k in ('trace_bytes','metric_cells') if k in independent}
            row['exact_transformation_replay']=independent.get('transformation')
            row['canonical_system_independently_rebuilt']=independent.get('canonical_system_independently_rebuilt')
        supplement=inputs.get('coordinate_supplement')
        if phase=='primal' and supplement is not None:
            correction=supplement['report'];coordinate=correction['coordinate_replay'];corrected=correction['corrected_original_equation_check']
            row['native_coordinate_correction']=dict(report_sha256=sha(SUPPLEMENT/'report.json'),
                schema=coordinate['schema'],changed_coordinate_count=coordinate['changed_coordinate_count'],
                changed_coordinate_indices=coordinate['changed_coordinate_indices'],
                raw_vector_sha256=coordinate['original_vector_sha256'],archived_vector_sha256=coordinate['archived_vector_sha256'],
                canonical_vector_sha256=coordinate['canonical_vector_sha256'],projection=coordinate['projection'],
                raw_nonnegative_min=coordinate['raw_nonnegative_min'],archived_nonnegative_min=coordinate['archived_nonnegative_min'],
                raw_objective=coordinate['raw_objective'],archived_objective=coordinate['archived_objective'],
                canonical_variable_map_independently_derived=False,canonical_matrix_independently_rebuilt=False,
                independent_raw_coordinate_diagnostics=corrected['diagnostics'],diagnostic_rounding=corrected['rounding'],
                tests_passed=supplement['tests_passed'],**FLAGS)
        rows.append(row)
    return dict(schema=12,previous_research_publication='publication-011',prior_manifests=inputs['priors'],
        source_count=len(stage['source']),tests_passed=stage['tests_passed'],
        coordinate_transport_supplement=(dict(report_sha256=sha(SUPPLEMENT/'report.json'),seal_sha256=sha(SUPPLEMENT/'seal.json'),
            source_sha256=inputs['coordinate_supplement']['source'],tests_passed=inputs['coordinate_supplement']['tests_passed']) if 'coordinate_supplement' in inputs else None),
        archived_primal_vector_is_unmodified_native_iterate=False,
        independent_receipt_sha256=sha(RUN/'independent_verification.json'),terminal_receipt_sha256=sha(RUN/'receipt.json'),
        mathematical_cone_and_target_unchanged=True,historical_development_scales=True,
        complete_original_columns=stage['review']['complete_original_columns'],complete_original_monomials=stage['review']['complete_original_monomials'],
        redundant_storage_cross_columns=stage['review']['redundant_storage_cross_columns'],
        numerical_transformation='exact augmented proportional-row compression and positive infinity scaling; identity columns',
        canonical_primal_matrix_independently_rebuilt=False,raw_failed_last_iterate_is_accepted_proposal=False,
        floating_metrics_are_certified_error_enclosures=False,discarded_log_bytes_independently_replayed=False,
        arithmetic_rebuilds=stage['review']['arithmetic_rebuilds'],geometry_rebuilds=stage['review']['geometry_rebuilds'],
        jobs=rows,mathematical_feasibility='UNKNOWN',diagnostic_only=True,no_exact_reconstruction_in_this_stage=True,
        critical_finite_certificate_found=False,exact_primitive_state_cone_separator_found=False,uniform_innovation_bound_proved=False,
        resources=dict(workers=2,worker_memory_bytes=3*1024**3,total_memory_bytes=6*1024**3,
            cooperative_seconds=900,cooperative_clock_includes_source_build=True,external_seconds=1800,
            numerical_threads_per_worker=1,max_source_compilation_operations=200000000,max_numerical_work=450000000,
            max_source_cells=4000000,max_trace_bytes=8388608,max_log_bytes=1048576),
        execution_cost=stage['execution']['cost'],handoff=NOTE,
        next_action='use independently recomputed residuals and retained native termination information to choose exact simplification or fixed-vector exact replay; preserve unknown feasibility',**FLAGS)


def publish():
    inputs=load_inputs();out=BASE/'publication-012';require(not out.exists(),'exclusive publication012')
    previous=read(BASE/'latest.json')
    require(previous.get('publication')=='publication-011' and previous.get('manifest_sha256')==sha(PREVIOUS/'manifest.json')
        and previous.get('report_sha256')==sha(PREVIOUS/'report.json'),'latest publication011 binding')
    files={ROOT/NOTE,PREVIOUS/'manifest.json',PREVIOUS/'report.json'}
    files.update(ROOT/n for n in publisher_sources());files.update(ROOT/n for n in inputs['stage']['source'])
    files.update(ROOT/n for n in inputs['coordinate_supplement']['source'])
    files.update(p for p in SUPPLEMENT.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
    files.update(p for p in RUN.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
    hashes={str(p.relative_to(ROOT)):sha(p) for p in sorted(files)}
    out.mkdir();(out/'frozen_source').mkdir()
    for name in [NOTE,SELF,TEST]:
        path=out/('frozen_source/'+name if name.endswith('.py') else name)
        path.write_bytes((ROOT/name).read_bytes());hashes[str(path.relative_to(ROOT))]=sha(path)
    write(out/'report.json',report(inputs));hashes[str((out/'report.json').relative_to(ROOT))]=sha(out/'report.json')
    write(out/'manifest.json',dict(schema=1,files=hashes,**FLAGS));bind(ROOT,read(out/'manifest.json')['files'])
    load_inputs();bind(ROOT,read(out/'manifest.json')['files'])
    require(read(BASE/'latest.json')==previous,'no intervening publication')
    pointer=dict(publication='publication-012',manifest_sha256=sha(out/'manifest.json'),report_sha256=sha(out/'report.json'),**FLAGS)
    write(BASE/'latest-012.tmp',pointer);(BASE/'latest-012.tmp').replace(BASE/'latest.json')
    return dict(publication='publication-012',bound_files=len(hashes),**FLAGS)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('action',choices=['validate','publish'])
    args=parser.parse_args()
    print(json.dumps(publish() if args.action=='publish' else dict(all_passed=True,publication_written=False,report=report(load_inputs())),sort_keys=True))

"""Publish completed exact equation-preprocessing evidence, without replay or search."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import publish_cancellation_primitive_state_solver_trace as OLD
import check_primitive_state_exact_row_basis_probe as CHECK

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
RUN=BASE/'primitive-state-exact-row-basis-probe-001'
PREVIOUS=BASE/'publication-012'
NOTE='PRIMITIVE_STATE_EXACT_BASIS_HANDOFF.txt'
SELF='publish_cancellation_primitive_state_exact_basis.py'
TEST='test_publish_cancellation_primitive_state_exact_basis.py'
FLAGS=dict(OLD.FLAGS)
read,sha,require,bind,write=OLD.read,OLD.sha,OLD.require,OLD.bind,OLD.write


def publisher_sources():
    pending=[SELF[:-3],TEST[:-3]];seen=set()
    while pending:
        name=pending.pop();p=ROOT/(name+'.py')
        if name in seen or not p.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(p.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def validate_outcome(review,record,execution,values):
    CHECK.scope(review)
    require(review.get('all_passed')is True and review.get('schema')=='primitive-state-exact-row-basis-probe-independent-review-v1','completed independent whole-stage review')
    require(review.get('original_shape')==CHECK.EXPECTED_SHAPE,'complete original finite equation scope')
    for k,v in dict(solver_called=False,mathematical_feasibility='UNKNOWN',numerical_rank_cutoff_used=False,full_optimization_variables_and_cones_unchanged=True).items():
        require(review.get(k)==v and type(review.get(k))is type(v),'nonadmission review '+k)
    worker=review.get('worker');require(type(worker)is dict,'independent worker outcome')
    CHECK.scope(worker)
    transport=execution['results'][0]
    require(worker.get('transport_status')==transport['status'] and worker.get('worker_status')==(record.get('status') if record else None),'independent transport/status binding')
    admitted=transport['status']=='available' and record is not None and record.get('status')=='basis_verified'
    require(type(review.get('equation_reduction_verified'))is bool and review['equation_reduction_verified']==admitted==worker.get('equation_reduction_verified'),'strict equation equivalence admission')
    indices=review.get('selected_original_row_indices')
    require(indices==worker.get('selected_original_row_indices'),'independent selected original indices')
    if admitted:
        require(record.get('equation_reduction_verified')is True and indices==record.get('selected_original_row_indices'),'terminal selected equations')
        require(type(indices)is list and all(type(i)is int and 0<=i<5641 for i in indices) and len(set(indices))==len(indices),'original row index domain')
        for name in ('projection','basis'):
            require(values.get(name,{}).get('complete')is True and review['artifact_replays'].get(name,{}).get('complete')is True,'complete independently checked '+name)
            require(values.get(name+'-check')==review['artifact_replays'][name],'bound deterministic worker check '+name)
        require(values['basis'].get('coefficient_consistency')in ('consistent','inconsistent'),'explicit exact coefficient consistency')
        require(indices==values['basis'].get('retained_indices') and len(indices)==values['basis'].get('augmented_rank'),'exact rank/selected row binding')
        state=worker.get('worker_state',{});require(state.get('equation_reduction_verified')is True and state.get('ledger',{}).get('all_stages_committed')is True and not state.get('ledger',{}).get('pending_stages'),'complete independently audited ledger')
    else:require(indices is None,'unknown outcome cannot publish selected rows')
    return admitted


def completed_archive():
    # No CHECK.audit, arithmetic rebuild, producer invocation, or numerical solve.
    protocol=CHECK.read(RUN/'protocol.json',65536);CHECK.verify_protocol(protocol)
    source=CHECK.read(RUN/'source_seal.json',65536)
    require(set(source)==set(CHECK.source_names()) and len(source)==101,'complete executed source closure')
    bind(ROOT,source);bind(RUN/'frozen_source',source)
    require({str(p.relative_to(RUN/'frozen_source')) for p in (RUN/'frozen_source').rglob('*') if p.is_file()}==set(source),'complete frozen source inventory')
    seal=read(RUN/'seal.json')
    for n in ('protocol','source_seal','input'):require(seal.get(n+'_sha256')==sha(RUN/(n+'.json')),'preregistered seal '+n)
    inputs=read(RUN/'input.json')['input_sha256'];require(set(inputs)==set(CHECK.INPUTS),'complete stage input set');bind(ROOT,inputs)
    receipt=read(RUN/'receipt.json');CHECK.verify_inventory(RUN,receipt)
    require(receipt.get('source_count')==101,'terminal source count')
    execution=read(RUN/'execution.json');CHECK.verify_runtime(execution)
    require(read(RUN/'run_started.json')==dict(protocol_sha256=sha(RUN/'protocol.json')),'exclusive preregistered execution')
    tests=read(RUN/'tests.json');match=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',tests.get('stdout','')+tests.get('stderr',''))
    require(type(tests.get('returncode'))is int and tests['returncode']==0 and match is not None and int(match.group(1))==63,'63 frozen calibration tests')
    review=read(RUN/'independent_verification.json')
    expected={'protocol.json','source_seal.json','input.json','seal.json','tests.json','execution.json','receipt.json'}
    require(set(review.get('input_sha256',{}))==expected,'complete independent review bindings');bind(RUN,review['input_sha256'])
    require(review.get('source_count')==101 and review.get('tests_passed')==63 and review.get('arithmetic_rebuilds')==review.get('geometry_rebuilds')==1,'one complete independent arithmetic rebuild')
    path=RUN/'jobs/primal.json';record=read(path) if path.exists() else None
    transport=execution['results'][0]
    if record is not None:
        CHECK.scope(record);CHECK.ORIGINAL.verify_worker_cost(record['cost'])
        require(record.get('program')==CHECK.PROGRAM and record.get('scales')==[1,2,3,5] and record.get('solver_called')is False,'same solver-free historical target')
        old=read(OLD.RUN/'jobs/primal.json')
        if 'case_hashes' in record:
            for key in OLD.SOURCE_FIELDS:require(record.get(key)==old.get(key),'unchanged exact arithmetic source '+key)
        elif record.get('status')=='basis_verified':raise ValueError('complete verified arithmetic provenance')
        if 'complete_columns' in record:
            for key in ('complete_columns','complete_monomials','exact_columns_hash','exact_target_hash'):
                require(record.get(key)==old.get(key),'identical complete original equations '+key)
            require(record['complete_columns']==1957 and record['complete_monomials']==5641,'complete unchanged finite dimensions')
    if transport['status']=='available':
        value=transport['value'];CHECK.scope(value)
        require(record is not None and value.get('file')=='jobs/primal.json' and value.get('sha256')==sha(path) and value.get('status')==record['status'] and value.get('cost')==record['cost'],'transport metadata binding')
    values={n:CHECK.read(RUN/'jobs'/f'{n}.json',8388608) for n in CHECK.ARTIFACTS if (RUN/'jobs'/f'{n}.json').exists()}
    admitted=validate_outcome(review,record,execution,values)
    return dict(protocol=protocol,source=source,review=review,record=record,execution=execution,values=values,equivalent=admitted)


def load_inputs():
    prior=OLD.load_inputs();manifest=read(PREVIOUS/'manifest.json');bind(ROOT,manifest['files'])
    require(len(manifest['files'])==259 and read(PREVIOUS/'report.json').get('schema')==12,'publication012 parent')
    priors=dict(prior['priors']);priors['publication-012']=dict(manifest_sha256=sha(PREVIOUS/'manifest.json'),bound_files=259)
    return dict(priors=priors,stage=completed_archive())


def report(inputs):
    stage=inputs['stage'];review=stage['review'];record=stage['record'];basis=stage['values'].get('basis',{});indices=review['selected_original_row_indices'];verified=stage['equivalent']
    consistency=basis.get('coefficient_consistency') if verified else None
    action=('derive an exact left-null inconsistency witness separately' if consistency=='inconsistent' else 'run a new numerical trial on selected FULL 1957-coordinate equations with corrected native export') if verified else 'address the actual recorded preprocessing resource block; retain unknown equation equivalence'
    summaries={}
    for name in ('projection','basis'):
        value=stage['values'].get(name)
        summaries[name]=None if value is None else {k:value[k] for k in ('status','complete','reason','counts','source_hash','full_source_hash','projected_rows_hash','augmented_rank','coefficient_consistency') if k in value and (k not in ('augmented_rank','coefficient_consistency') or verified)}
    return dict(schema=13,previous_research_publication='publication-012',prior_manifests=inputs['priors'],source_count=101,tests_passed=63,
        independent_receipt_sha256=sha(RUN/'independent_verification.json'),terminal_receipt_sha256=sha(RUN/'receipt.json'),
        mathematical_cone_and_target_unchanged=True,full_optimization_variables_and_cones_unchanged=True,original_variables=1957,original_finite_equations=5641,
        equation_reduction_verified=verified,selected_original_row_indices=indices,selected_original_row_indices_sha256=(hashlib.sha256(json.dumps(indices,separators=(',',':')).encode()).hexdigest() if verified else None),
        augmented_rank=basis.get('augmented_rank') if verified else None,coefficient_consistency=consistency,preprocessing=summaries,
        transport_status=stage['execution']['results'][0]['status'],worker_status=record.get('status') if record else None,reason=record.get('reason') if record else stage['execution']['results'][0].get('reason'),
        deadline_exceeded=record.get('deadline_exceeded') if record else None,worker_cost=record.get('cost') if record else None,
        ledger=record.get('ledger') if record else None,independent_worker_review=review['worker'],resources=dict(CHECK.PARALLEL),limits=dict(CHECK.LIMITS),
        execution_cost=stage['execution']['cost'],solver_called=False,mathematical_feasibility='UNKNOWN',diagnostic_only=True,
        exact_row_equivalence_is_not_a_PSD_certificate=True,uniform_innovation_bound_proved=False,critical_finite_certificate_found=False,
        original_finite_scope_is_not_a_uniform_proof=True,handoff=NOTE,next_action=action,**FLAGS)


def publish():
    inputs=load_inputs();out=BASE/'publication-013';require(not out.exists(),'exclusive publication013')
    previous=read(BASE/'latest.json')
    require(previous.get('publication')=='publication-012' and previous.get('manifest_sha256')==sha(PREVIOUS/'manifest.json') and previous.get('report_sha256')==sha(PREVIOUS/'report.json'),'latest publication012 binding')
    files={ROOT/NOTE,PREVIOUS/'manifest.json',PREVIOUS/'report.json'}
    files.update(ROOT/n for n in publisher_sources());files.update(ROOT/n for n in inputs['stage']['source']);files.update(ROOT/n for n in CHECK.INPUTS)
    files.update(p for p in RUN.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
    hashes={str(p.relative_to(ROOT)):sha(p) for p in sorted(files)}
    out.mkdir();(out/'frozen_source').mkdir()
    for name in (NOTE,SELF,TEST):
        p=out/('frozen_source/'+name if name.endswith('.py') else name);p.write_bytes((ROOT/name).read_bytes());hashes[str(p.relative_to(ROOT))]=sha(p)
    write(out/'report.json',report(inputs));hashes[str((out/'report.json').relative_to(ROOT))]=sha(out/'report.json')
    write(out/'manifest.json',dict(schema=1,files=hashes,**FLAGS));bind(ROOT,read(out/'manifest.json')['files'])
    load_inputs();bind(ROOT,read(out/'manifest.json')['files']);require(read(BASE/'latest.json')==previous,'no intervening publication')
    write(BASE/'latest-013.tmp',dict(publication='publication-013',manifest_sha256=sha(out/'manifest.json'),report_sha256=sha(out/'report.json'),**FLAGS));(BASE/'latest-013.tmp').replace(BASE/'latest.json')
    return dict(publication='publication-013',bound_files=len(hashes),**FLAGS)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('action',choices=['validate','publish']);args=parser.parse_args()
    print(json.dumps(publish() if args.action=='publish' else dict(all_passed=True,publication_written=False,report=report(load_inputs())),sort_keys=True))

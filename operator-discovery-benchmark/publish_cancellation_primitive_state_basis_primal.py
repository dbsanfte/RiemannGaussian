"""Archive independently audited direct numerical evidence without rerunning it."""
import argparse
import ast
import json
from pathlib import Path
import re
import publish_cancellation_primitive_state_exact_basis_v2 as OLD
import check_primitive_state_basis_primal_run as CHECK

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
RUN=BASE/'primitive-state-basis-primal-001'
PREVIOUS=BASE/'publication-014'
NOTE='PRIMITIVE_STATE_BASIS_PRIMAL_HANDOFF.txt'
SELF='publish_cancellation_primitive_state_basis_primal.py'
TEST='test_publish_cancellation_primitive_state_basis_primal.py'
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


def validate_outcome(review,record,execution,trace,check):
    CHECK.scope(review)
    require(review.get('schema')=='primitive-state-basis-primal-independent-review-v1' and review.get('all_passed')is True,'completed independent native trial audit')
    require(review.get('original_rows')==5641 and review.get('original_variables')==1957 and review.get('licensed_selected_rows')==779,'unchanged complete original system')
    require(review.get('mathematical_feasibility')=='UNKNOWN' and review.get('numerical_diagnostics_only')is True,'numerical evidence only')
    license=review.get('basis_license_replay');require(type(license)is dict,'fresh exact proof replay')
    require(license.get('prior_equation_admission')is False and license.get('fresh_equation_authorization')is True,'fresh authorization preserves old failure')
    indices=license.get('indices')
    require(type(indices)is list and len(indices)==779 and len(set(indices))==779 and all(type(i)is int and 0<=i<5641 for i in indices),'full selected original row domain')
    for name in ('projection','basis'):
        value=license.get('replay_checks',{}).get(name,{})
        require(value.get('verified')is True and value.get('complete')is True,'complete independent exact '+name+' replay')
    trial=review.get('trial');require(type(trial)is dict,'independent numerical outcome');CHECK.scope(trial)
    require(trial.get('accepted_proposal')is False and trial.get('mathematical_feasibility')=='UNKNOWN','no numerical proof admission')
    transport=execution['results'][0]
    require(trial.get('transport_status')==transport['status'] and trial.get('worker_status')==(record.get('status') if record else None),'audited terminal status binding')
    available=transport['status']=='available' and record is not None and record.get('status')=='trace_verified'
    require(type(trial.get('terminal_numerical_diagnostics_available'))is bool and trial['terminal_numerical_diagnostics_available']==available,'strict available diagnostic transport')
    if available:
        CHECK.scope(record)
        require(record.get('fresh_exact_basis_authorized')is True and record.get('numerical_verification_pending')is False,'fresh proof gate before completed numerical trial')
        require(record.get('selected_original_indices')==license.get('indices') and len(license['indices'])==779,'selected ORIGINAL equation indices')
        require(type(trace)is dict and type(check)is dict and check==trial.get('trace_check') and check.get('verified')is True,'bound complete independent numerical check')
        require(review.get('canonical_primal_matrix_independently_rebuilt')is True and check.get('canonical_system_independently_rebuilt')is True,'independent canonical matrix reconstruction')
        require(trial.get('ledger',{}).get('all_stages_committed')is True and not trial.get('ledger',{}).get('pending_stages'),'complete audited conservative work ledger')
        require(record.get('termination_status')==trace.get('termination_status'),'terminal native status')
        require(record.get('raw_vector_available')==(trace.get('original_vector')is not None),'raw native coordinate availability')
    return available


def completed_archive():
    protocol=CHECK.read(RUN/'protocol.json',65536);CHECK.verify_protocol(protocol)
    source=CHECK.read(RUN/'source_seal.json',65536)
    require(set(source)==set(CHECK.source_names()),'complete frozen source closure')
    bind(ROOT,source);bind(RUN/'frozen_source',source)
    require({str(p.relative_to(RUN/'frozen_source')) for p in (RUN/'frozen_source').rglob('*') if p.is_file()}==set(source),'complete frozen source inventory')
    seal=read(RUN/'seal.json')
    for name in ('protocol','source_seal','input'):require(seal.get(name+'_sha256')==sha(RUN/(name+'.json')),'preregistered seal '+name)
    inputs=read(RUN/'input.json')['input_sha256'];require(set(inputs)==set(CHECK.INPUTS),'complete exact evidence/resource inputs');bind(ROOT,inputs)
    receipt=read(RUN/'receipt.json');CHECK.verify_inventory(RUN,receipt)
    require(receipt.get('source_count')==len(source),'terminal source count')
    execution=read(RUN/'execution.json');CHECK.verify_runtime(execution)
    require(read(RUN/'run_started.json')==dict(protocol_sha256=sha(RUN/'protocol.json')),'exclusive preregistered execution')
    tests=read(RUN/'tests.json');match=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',tests.get('stdout','')+tests.get('stderr',''))
    require(type(tests.get('returncode'))is int and tests['returncode']==0 and match is not None and int(match.group(1))>0,'passed frozen calibration tests')
    review=read(RUN/'independent_verification.json')
    names={'protocol.json','source_seal.json','input.json','seal.json','tests.json','execution.json','receipt.json'}
    require(set(review.get('input_sha256',{}))==names,'complete independent review bindings');bind(RUN,review['input_sha256'])
    require(review.get('source_count')==len(source) and review.get('tests_passed')==int(match.group(1)) and review.get('arithmetic_rebuilds')==review.get('geometry_rebuilds')==1,'one complete independent arithmetic/geometry rebuild')
    path=RUN/'jobs/primal.json';record=read(path) if path.exists() else None
    tracepath=RUN/'jobs/primal-trace.json';trace=CHECK.read(tracepath) if tracepath.exists() else None
    checkpath=RUN/'jobs/primal-check.json';check=CHECK.read(checkpath) if checkpath.exists() else None
    if record is not None:
        CHECK.scope(record);CHECK.ORIGINAL.verify_worker_cost(record['cost'])
        require(record.get('program')==CHECK.PROGRAM and record.get('scales')==[1,2,3,5],'same historical arithmetic target')
        require(record.get('basis_evidence')==protocol.get('basis_evidence'),'same frozen basis evidence')
    if execution['results'][0]['status']=='available':
        value=execution['results'][0]['value'];CHECK.scope(value)
        require(record is not None and value==dict(file='jobs/primal.json',sha256=sha(path),status=record['status'],cost=record['cost'],**FLAGS),'complete transported terminal metadata')
    available=validate_outcome(review,record,execution,trace,check)
    return dict(protocol=protocol,source=source,review=review,record=record,execution=execution,trace=trace,check=check,available=available)


def load_inputs():
    prior=OLD.load_inputs();manifest=read(PREVIOUS/'manifest.json');bind(ROOT,manifest['files'])
    require(len(manifest['files'])==279 and read(PREVIOUS/'report.json').get('schema')==14,'publication014 parent')
    priors=dict(prior['priors']);priors['publication-014']=dict(manifest_sha256=sha(PREVIOUS/'manifest.json'),bound_files=len(manifest['files']))
    stage=completed_archive();require(stage['review'].get('parent_bound_files')==len(manifest['files']),'complete audited parent')
    return dict(priors=priors,stage=stage)


def report(inputs):
    stage=inputs['stage'];review=stage['review'];record=stage['record'];trace=stage['trace'];trial=review['trial']
    check=trial.get('trace_check');status=trace.get('termination_status') if trace else None
    action='diagnose the recorded numerical or resource failure before choosing a new trial'
    if stage['available'] and status in ('Solved','AlmostSolved'):
        action='attempt bounded rational restoration and exact sign/PSD verification against ALL 5641 original equations'
    elif stage['available'] and status in ('PrimalInfeasible','AlmostPrimalInfeasible'):
        action='attempt separate rational reconstruction of the native dual ray; exact verification is required before any finite-cone exclusion'
    raw=trace.get('raw_solution') if trace else None
    return dict(schema=15,previous_research_publication='publication-014',prior_manifests=inputs['priors'],source_count=review['source_count'],tests_passed=review['tests_passed'],
        independent_receipt_sha256=sha(RUN/'independent_verification.json'),terminal_receipt_sha256=sha(RUN/'receipt.json'),
        full_optimization_variables_and_cones_unchanged=True,mathematical_cone_and_target_unchanged=True,original_variables=1957,original_finite_equations=5641,selected_original_equations=779,
        previous_run_equation_admission=False,fresh_equation_replay=review['basis_license_replay'],
        canonical_primal_matrix_independently_rebuilt=review['canonical_primal_matrix_independently_rebuilt'],
        terminal_numerical_diagnostics_available=stage['available'],transport_status=stage['execution']['results'][0]['status'],worker_status=record.get('status') if record else None,
        termination_status=status,vector_role=trace.get('vector_role') if trace else None,
        raw_vector_lengths={name:len(raw[name]) if type(raw)is dict and type(raw.get(name))is list else None for name in ('x','z','s')},
        independent_diagnostics=check.get('diagnostics') if check else None,
        native_info=trace.get('raw_info') if trace else None,solver=trace.get('solver') if trace else None,
        worker_cost=record.get('cost') if record else None,ledger=record.get('ledger') if record else None,
        reason=record.get('reason') if record else stage['execution']['results'][0].get('reason'),
        execution_cost=stage['execution']['cost'],independent_replay_operations=review['independent_replay_operations'],independent_replay_cells=review['independent_replay_cells'],
        resources=dict(CHECK.PARALLEL),limits=dict(CHECK.LIMITS),mathematical_feasibility='UNKNOWN',diagnostic_only=True,
        accepted_proposal=False,critical_finite_certificate_found=False,uniform_innovation_bound_proved=False,original_finite_scope_is_not_a_uniform_proof=True,
        handoff=NOTE,next_action=action,**FLAGS)


def publish():
    inputs=load_inputs();out=BASE/'publication-015';require(not out.exists(),'exclusive publication015')
    previous=read(BASE/'latest.json')
    require(previous.get('publication')=='publication-014' and previous.get('manifest_sha256')==sha(PREVIOUS/'manifest.json') and previous.get('report_sha256')==sha(PREVIOUS/'report.json'),'latest publication014 binding')
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
    write(BASE/'latest-015.tmp',dict(publication='publication-015',manifest_sha256=sha(out/'manifest.json'),report_sha256=sha(out/'report.json'),**FLAGS));(BASE/'latest-015.tmp').replace(BASE/'latest.json')
    return dict(publication='publication-015',bound_files=len(hashes),**FLAGS)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('action',choices=['validate','publish']);args=parser.parse_args()
    result=publish() if args.action=='publish' else dict(all_passed=True,publication_written=False,report=report(load_inputs()))
    print(json.dumps(result,sort_keys=True))

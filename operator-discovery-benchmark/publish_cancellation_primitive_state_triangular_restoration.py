"""Publish independently checked exact restoration evidence without recomputation."""
import argparse
import ast
import json
from pathlib import Path
import re
import publish_cancellation_primitive_state_cached_variants as OLD
import check_primitive_state_triangular_restoration_run as CHECK

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
RUN=BASE/'primitive-state-triangular-restoration-001'
PREVIOUS=BASE/'publication-016'
NOTE='PRIMITIVE_STATE_TRIANGULAR_RESTORATION_HANDOFF.txt'
ANALYSIS='primitive_state_free_coordinate_search_analysis_v1.txt'
SELF='publish_cancellation_primitive_state_triangular_restoration.py'
TEST='test_publish_cancellation_primitive_state_triangular_restoration.py'
FLAGS=dict(CHECK.FLAGS)
read,sha,require,bind,write=OLD.read,OLD.sha,OLD.require,OLD.bind,OLD.write


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


def validate_outcome(review,execution,record,producer,check):
    CHECK.scope(review)
    require(review.get('schema')=='primitive-state-triangular-restoration-independent-review-v1' and review.get('all_passed')is True,'completed exact restoration archive audit')
    for key,value in dict(original_finite_equations=5641,original_variables=1957,projected_variables=1224,rank=779,parent_source_rebuilds=0,new_solver_calls=0,new_elimination_calls=0,uniform_or_RH_admission=False,objective_preserved=False).items():
        require(type(review.get(key))is type(value) and review[key]==value,'unchanged restoration scope '+key)
    require(len(execution.get('results',[]))==1,'one restoration transport')
    transport=execution['results'][0];job=review.get('job');require(type(job)is dict,'explicit audited restoration outcome');CHECK.scope(job)
    require(job.get('transport_status')==transport.get('status') and job.get('worker_status')==(record.get('status') if record else None),'bound terminal restoration status')
    available=transport.get('status')=='available' and record is not None and record.get('status')=='restoration_verified'
    require(job.get('restoration_verified')is available,'strict completed restoration availability')
    if record is not None:CHECK.scope(record)
    if check is not None:CHECK.scope(check);require(check==review.get('restoration_check'),'same independent exact restoration receipt')
    if available:
        require(record.get('deadline_exceeded')is False and record.get('restoration_verified')is True,'completed restoration within declared deadline')
        require(type(producer)is dict and producer.get('status')=='restored' and producer.get('complete')is True,'complete fixed-seed producer')
        CHECK.scope(producer)
        require(type(check)is dict and check.get('verified')is True and check.get('complete')is True and check.get('restoration_verified')is True,'independent complete exact replay')
        require(check.get('all_original_equations_checked')==5641 and check.get('original_variables')==1957 and check.get('candidate_hash')==producer.get('candidate_hash'),'full original equation domain and lifted candidate')
        require(job.get('lifecycle',{}).get('ledger',{}).get('all_stages_committed')is True,'committed conservative restoration ledger')
        feasible=check.get('finite_candidate_feasible');require(type(feasible)is bool and record.get('finite_candidate_feasible')is feasible and job.get('finite_candidate_feasible')is feasible,'exact finite outcome binding')
        exact=check.get('exact_candidate_checks',{})
        require(exact.get('equality_complete')is True and exact.get('scalar_signs_complete')is True and set(exact.get('psd_blocks',{}))=={'full_child','full_parent','storage_K'},'complete exact equality/sign/PSD checks')
        for key in ('equality_mismatch_count','negative_scalar_count'):require(type(exact.get(key))is int and exact[key]>=0,'exact defect count '+key)
        require(all(type(q.get('psd'))is bool for q in exact['psd_blocks'].values()),'exact PSD verdicts')
        passed=exact['equality_mismatch_count']==0 and exact['negative_scalar_count']==0 and all(q['psd'] for q in exact['psd_blocks'].values())
        require(feasible is passed and exact.get('finite_candidate_feasible')is feasible,'finite verdict follows all original constraints')
    else:
        require(job.get('finite_candidate_feasible')is None,'partial or failed transport cannot promote candidate')
    return available


def completed_archive():
    protocol=CHECK.read(RUN/'protocol.json',65536);CHECK.verify_protocol(protocol,protocol['parent_license'])
    sources=CHECK.read(RUN/'source_seal.json',65536);require(set(sources)==set(CHECK.source_names()),'complete frozen restoration source closure')
    bind(ROOT,sources);bind(RUN/'frozen_source',sources)
    require({str(p.relative_to(RUN/'frozen_source')) for p in (RUN/'frozen_source').rglob('*') if p.is_file()}==set(sources),'complete frozen restoration source inventory')
    seal=read(RUN/'seal.json')
    for name in ('protocol','source_seal','input'):require(seal.get(name+'_sha256')==sha(RUN/(name+'.json')),'preregistered restoration seal '+name)
    inputs=read(RUN/'input.json');require(set(inputs.get('input_sha256',{}))==set(CHECK.INPUTS),'complete restoration parent bindings');bind(ROOT,inputs['input_sha256'])
    terminal=read(RUN/'receipt.json');CHECK.verify_inventory(RUN,terminal);require(terminal.get('source_count')==len(sources),'complete terminal source count')
    execution=read(RUN/'execution.json');CHECK.verify_runtime(execution)
    require(read(RUN/'run_started.json')==dict(protocol_sha256=sha(RUN/'protocol.json')),'exclusive frozen restoration execution')
    tests=read(RUN/'tests.json');match=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',tests.get('stdout','')+tests.get('stderr',''))
    require(tests.get('returncode')==0 and match is not None and int(match.group(1))>0,'passed restoration calibration')
    review=read(RUN/'independent_verification.json');names={'protocol','source_seal','input','seal','tests','execution','receipt'}
    require(set(review.get('input_sha256',{}))==names,'complete independent restoration review inputs');bind(RUN,{name+'.json':value for name,value in review['input_sha256'].items()})
    require(review.get('source_count')==len(sources) and review.get('tests_passed')==int(match.group(1)) and review.get('parent_bound_files')==309 and review.get('ancestor_bound_files')==285,'bound parent and calibration dimensions')
    values={key:CHECK.read(RUN/'jobs'/name) if (RUN/'jobs'/name).exists() else None for key,name in [('record','restoration-job.json'),('producer','restoration.json'),('check','check.json')]}
    available=validate_outcome(review,execution,**values)
    return dict(protocol=protocol,sources=sources,review=review,execution=execution,available=available,**values)


def load_inputs():
    prior=OLD.load_inputs();manifest=read(PREVIOUS/'manifest.json');bind(ROOT,manifest['files'])
    require(len(manifest['files'])==309 and read(PREVIOUS/'report.json').get('schema')==16,'completed publication016 parent')
    priors=dict(prior['priors']);priors['publication-016']=dict(manifest_sha256=sha(PREVIOUS/'manifest.json'),bound_files=309)
    return dict(priors=priors,stage=completed_archive())


def report(inputs):
    s=inputs['stage'];review=s['review'];record=s['record'];producer=s['producer'];check=s['check']
    feasible=review['job']['finite_candidate_feasible'] if s['available'] else None
    action='resolve the recorded incomplete restoration or resource failure'
    if feasible is False:action='search the445 free coordinates for exact cone feasibility using the licensed triangular map'
    elif feasible is True:action='run typed finite-certificate admission, then investigate a uniform identity and all-scale innovation bound'
    return dict(schema=17,previous_research_publication='publication-016',prior_manifests=inputs['priors'],
        independent_receipt_sha256=sha(RUN/'independent_verification.json'),terminal_receipt_sha256=sha(RUN/'receipt.json'),
        source_count=review['source_count'],tests_passed=review['tests_passed'],job=review['job'],
        original_finite_equations=5641,original_variables=1957,projected_variables=1224,rank=779,free_coordinates=445,
        one_fixed_seed=True,restoration_available=s['available'],finite_candidate_feasible=feasible,
        producer_status=producer.get('status') if producer else None,producer_counts=producer.get('counts') if producer else None,
        producer_reason=producer.get('reason') if producer else None,clipped_free_square_indices=producer.get('clipped_free_square_indices') if producer else None,
        exact_checks=check.get('exact_candidate_checks') if check else None,independent_check_complete=check.get('complete') if check else None,
        candidate_hash=check.get('candidate_hash') if check else None,worker_cost=record.get('cost') if record else None,worker_ledger=record.get('ledger') if record else None,
        execution_cost=s['execution'].get('cost'),independent_replay_operations=review['independent_replay_operations'],independent_replay_cells=review['independent_replay_cells'],
        total_independent_audit_operations=review['total_independent_audit_operations'],total_independent_audit_cells=review['total_independent_audit_cells'],
        original_objective_preserved=False,parent_source_rebuilds=0,new_solver_calls=0,new_elimination_calls=0,
        mathematical_cone_feasibility='feasible finite candidate awaiting typed admission' if feasible is True else 'UNKNOWN',
        accepted_proposal=False,uniform_innovation_bound_proved=False,next_action=action,
        followup_analysis=dict(file=ANALYSIS,sha256=sha(ROOT/ANALYSIS)),limits=CHECK.LIMITS,resources=CHECK.PARALLEL,handoff=NOTE,**FLAGS)


def publish():
    out=BASE/'publication-017';require(not out.exists(),'exclusive publication017');inputs=load_inputs()
    previous=read(BASE/'latest.json');require(previous.get('publication')=='publication-016' and previous.get('manifest_sha256')==sha(PREVIOUS/'manifest.json') and previous.get('report_sha256')==sha(PREVIOUS/'report.json'),'latest completed publication016')
    files={ROOT/NOTE,ROOT/ANALYSIS,PREVIOUS/'manifest.json',PREVIOUS/'report.json'}
    files.update(ROOT/name for name in publisher_sources());files.update(ROOT/name for name in inputs['stage']['sources']);files.update(ROOT/name for name in CHECK.INPUTS)
    files.update(path for path in RUN.rglob('*') if path.is_file() and '__pycache__' not in path.parts)
    hashes={str(path.relative_to(ROOT)):sha(path) for path in sorted(files)};out.mkdir();(out/'frozen_source').mkdir()
    for name in (NOTE,SELF,TEST):
        path=out/('frozen_source/'+name if name.endswith('.py') else name);path.write_bytes((ROOT/name).read_bytes());hashes[str(path.relative_to(ROOT))]=sha(path)
    write(out/'report.json',report(inputs));hashes[str((out/'report.json').relative_to(ROOT))]=sha(out/'report.json')
    write(out/'manifest.json',dict(schema=1,files=hashes,**FLAGS));bind(ROOT,hashes)
    load_inputs();bind(ROOT,hashes);require(read(BASE/'latest.json')==previous,'no intervening publication')
    write(BASE/'latest-017.tmp',dict(publication='publication-017',manifest_sha256=sha(out/'manifest.json'),report_sha256=sha(out/'report.json'),**FLAGS));(BASE/'latest-017.tmp').replace(BASE/'latest.json')
    return dict(publication='publication-017',bound_files=len(hashes),**FLAGS)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('action',choices=['validate','publish']);a=p.parse_args()
    print(json.dumps(publish() if a.action=='publish' else report(load_inputs()),sort_keys=True))

"""Publish completed shared-cache numerical evidence without rebuilding or solving."""
import argparse
import ast
import json
from pathlib import Path
import re
import publish_cancellation_primitive_state_basis_primal as OLD
import check_primitive_state_cached_primal_variants_run_v2 as CHECK

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
RUN=BASE/'primitive-state-cached-primal-variants-001'
PREVIOUS=BASE/'publication-015'
NOTE='PRIMITIVE_STATE_CACHED_VARIANTS_HANDOFF.txt'
SELF='publish_cancellation_primitive_state_cached_variants.py'
TEST='test_publish_cancellation_primitive_state_cached_variants.py'
ANALYSES=['primitive_state_cached_restoration_analysis_v1.txt','primitive_state_lossless_cone_quotient_analysis_v1.txt']
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


def validate_outcomes(review,preparation,execution,records,traces,checks):
    CHECK.scope(review)
    require(review.get('schema')==CHECK.SCHEMA and review.get('all_passed')is True,'completed supplemental independent shared-cache audit')
    envelope=review.get('protocol_envelope',{})
    require(envelope.get('file')=='protocol.json' and envelope.get('original_max_bytes')==65536 and envelope.get('supplemental_max_bytes')==CHECK.PROTOCOL_MAX_BYTES,'explicit protocol envelope correction')
    require(type(envelope.get('actual_bytes'))is int and 65536<envelope['actual_bytes']<=CHECK.PROTOCOL_MAX_BYTES and envelope.get('original_audit_contract_satisfied')is False and review.get('original_audit_contract_satisfied')is False,'original failed envelope is never retroactively admitted')
    for k,v in dict(original_variables=1957,original_finite_equations=5641,selected_original_rows=779,mathematical_feasibility='UNKNOWN',numerical_diagnostics_only=True).items():
        require(type(review.get(k))is type(v) and review[k]==v,'unchanged diagnostic scope '+k)
    prep=review.get('preparation');require(type(prep)is dict,'independent preparation outcome');CHECK.scope(prep)
    require(prep.get('transport_status')==preparation['results'][0]['status'],'bound preparation transport')
    if prep.get('shared_cache_available')is True:
        require(preparation['results'][0]['status']=='available' and prep.get('worker_status')=='cache_verified','completed shared cache gate')
        require(review.get('cache_check',{}).get('verified')is True and review['cache_check'].get('canonical_system_independently_rebuilt')is True,'independent full cache reconstruction')
    elif execution.get('status')!='blocked':raise ValueError('failed preparation cannot launch variants')
    jobs=review.get('jobs');require(type(jobs)is list and len(jobs)==len(CHECK.VARIANTS),'complete ordered variant audit')
    available=[]
    for index,spec in enumerate(CHECK.VARIANTS):
        name=spec['id'];job=jobs[index];CHECK.scope(job)
        require(job.get('variant')==name,'fixed ordered variant identity')
        transport=execution['results'][index] if execution.get('status')!='blocked' else dict(status='blocked')
        record=records.get(name);trace=traces.get(name);check=checks.get(name)
        require(job.get('transport_status')==transport['status'] and job.get('worker_status')==(record.get('status') if record else None),'bound variant terminal outcome')
        admitted=transport['status']=='available' and record is not None and record.get('status')=='trace_verified'
        require(type(job.get('numerical_diagnostics_available'))is bool and job['numerical_diagnostics_available']==admitted,'strict numerical transport admission')
        if admitted:
            CHECK.scope(record)
            require(record.get('numerical_verification_pending')is False and record.get('variant')==name,'completed fixed variant metadata')
            require(type(trace)is dict and trace.get('variant')==name and trace.get('termination_status')==record.get('termination_status'),'bound raw native variant status')
            require(type(check)is dict and check==job.get('trace_check') and check.get('verified')is True,'complete deterministic independent variant check')
            require(check.get('canonical_system_independently_rebuilt')is True and check.get('mathematical_feasibility')=='UNKNOWN','checked canonical input without numerical theorem')
            require(job.get('lifecycle',{}).get('ledger',{}).get('all_stages_committed')is True,'complete conservative variant work ledger')
        available.append(admitted)
    return available


def completed_archive():
    protocol=CHECK.read(RUN/'protocol.json',CHECK.PROTOCOL_MAX_BYTES);CHECK.verify_protocol(protocol)
    source=CHECK.read(RUN/'source_seal.json',65536);require(set(source)==set(CHECK.source_names()),'complete frozen source closure')
    bind(ROOT,source);bind(RUN/'frozen_source',source)
    require({str(p.relative_to(RUN/'frozen_source')) for p in (RUN/'frozen_source').rglob('*') if p.is_file()}==set(source),'complete frozen source inventory')
    seal=read(RUN/'seal.json')
    for name in ('protocol','source_seal','input'):require(seal.get(name+'_sha256')==sha(RUN/(name+'.json')),'preregistered seal '+name)
    inputs=read(RUN/'input.json')['input_sha256'];require(set(inputs)==set(CHECK.INPUTS),'complete parent/cache resource bindings');bind(ROOT,inputs)
    receipt=read(RUN/'receipt.json');CHECK.verify_inventory(RUN,receipt);require(receipt.get('source_count')==len(source),'terminal source count')
    execution=read(RUN/'execution.json');preparation=read(RUN/'preparation-execution.json');CHECK.verify_runtime(execution,preparation)
    require(read(RUN/'run_started.json')==dict(protocol_sha256=sha(RUN/'protocol.json')),'exclusive preregistered execution')
    tests=read(RUN/'tests.json');match=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',tests.get('stdout','')+tests.get('stderr',''))
    require(type(tests.get('returncode'))is int and tests['returncode']==0 and match is not None and int(match.group(1))>0,'passed frozen calibration')
    review=read(RUN/CHECK.REVIEW_NAME);names={'protocol.json','source_seal.json','input.json','seal.json','tests.json','preparation-execution.json','execution.json','receipt.json'}
    require(review.get('protocol_envelope')==CHECK.protocol_envelope(RUN),'actual original protocol envelope failure binding')
    require(set(review.get('audit_source_sha256',{}))==set(CHECK.AUDIT_FILES),'complete supplemental audit source bindings');bind(ROOT,review['audit_source_sha256'])
    require(set(review.get('input_sha256',{}))==names,'complete independent review bindings');bind(RUN,review['input_sha256'])
    require(review.get('source_count')==len(source) and review.get('tests_passed')==int(match.group(1)) and review.get('arithmetic_rebuilds')==review.get('geometry_rebuilds')==review.get('parent_basis_replays')==1,'one independent original source and parent proof replay')
    records={};traces={};checks={}
    for spec in CHECK.VARIANTS:
        name=spec['id'];folder=RUN/'jobs'/name
        for result,file in ((records,'job.json'),(traces,'trace.json'),(checks,'check.json')):
            result[name]=CHECK.read(folder/file) if (folder/file).exists() else None
    available=validate_outcomes(review,preparation,execution,records,traces,checks)
    prep_path=RUN/'jobs/prepare/job.json';prep_record=CHECK.read(prep_path,65536) if prep_path.exists() else None
    return dict(protocol=protocol,source=source,review=review,execution=execution,preparation_execution=preparation,preparation_record=prep_record,records=records,traces=traces,checks=checks,available=available)


def load_inputs():
    old=OLD.load_inputs();manifest=read(PREVIOUS/'manifest.json');bind(ROOT,manifest['files'])
    require(len(manifest['files'])==285 and read(PREVIOUS/'report.json').get('schema')==15,'publication015 parent')
    priors=dict(old['priors']);priors['publication-015']=dict(manifest_sha256=sha(PREVIOUS/'manifest.json'),bound_files=285)
    stage=completed_archive();require(stage['review'].get('parent_bound_files')==285,'complete independently bound parent')
    return dict(priors=priors,stage=stage)


def report(inputs):
    stage=inputs['stage'];review=stage['review'];summaries=[]
    for i,spec in enumerate(CHECK.VARIANTS):
        name=spec['id'];trace=stage['traces'].get(name);record=stage['records'].get(name);job=review['jobs'][i]
        check=job.get('trace_check');native=check.get('trace_check') if check else None
        status=trace.get('termination_status') if trace else None
        action='diagnose recorded numerical or resource failure'
        if stage['available'][i] and status in ('Solved','AlmostSolved'):action='measure full-system residual amplification and cone defects before choosing a bounded exact rational restoration attempt'
        elif stage['available'][i] and status in ('PrimalInfeasible','AlmostPrimalInfeasible'):action='attempt separate exact dual-ray reconstruction before any finite-cone exclusion'
        summaries.append(dict(variant=name,settings_change=spec['options'],numerical_diagnostics_available=stage['available'][i],transport_status=job['transport_status'],worker_status=job['worker_status'],termination_status=status,
            independent_diagnostics=native.get('diagnostics') if native else None,native_info=trace.get('raw_info') if trace else None,vector_role=trace.get('vector_role') if trace else None,
            worker_cost=record.get('cost') if record else None,ledger=record.get('ledger') if record else None,reason=record.get('reason') if record else None,next_action=action,accepted_proposal=False,**FLAGS))
    prep=stage['preparation_record']
    return dict(schema=16,previous_research_publication='publication-015',prior_manifests=inputs['priors'],source_count=review['source_count'],tests_passed=review['tests_passed'],
        independent_receipt_sha256=sha(RUN/CHECK.REVIEW_NAME),terminal_receipt_sha256=sha(RUN/'receipt.json'),
        supplemental_audit=True,original_audit_contract_satisfied=False,protocol_envelope=review['protocol_envelope'],
        followup_analyses={name:sha(ROOT/name) for name in ANALYSES},
        mathematical_cone_and_target_unchanged=True,full_optimization_variables_and_cones_unchanged=True,original_variables=1957,original_finite_equations=5641,selected_original_equations=779,
        shared_preparation_count=1,exact_basis_replay_per_solver=False,cache_check=review['cache_check'],preparation=review['preparation'],
        preparation_worker_cost=prep.get('cost') if prep else None,preparation_ledger=prep.get('ledger') if prep else None,
        variants=summaries,execution_cost=stage['execution'].get('cost'),preparation_execution_cost=stage['preparation_execution'].get('cost'),
        independent_replay_operations=review['independent_replay_operations'],independent_replay_cells=review['independent_replay_cells'],
        resources=dict(preparation=CHECK.PREP_PARALLEL,variants=CHECK.VARIANT_PARALLEL),limits=CHECK.LIMITS,
        mathematical_feasibility='UNKNOWN',diagnostic_only=True,accepted_proposal=False,critical_finite_certificate_found=False,uniform_innovation_bound_proved=False,handoff=NOTE,**FLAGS)


def publish():
    inputs=load_inputs();out=BASE/'publication-016';require(not out.exists(),'exclusive publication016')
    previous=read(BASE/'latest.json');require(previous.get('publication')=='publication-015' and previous.get('manifest_sha256')==sha(PREVIOUS/'manifest.json') and previous.get('report_sha256')==sha(PREVIOUS/'report.json'),'latest publication015 binding')
    files={ROOT/NOTE,PREVIOUS/'manifest.json',PREVIOUS/'report.json'}
    files.update(ROOT/n for n in publisher_sources());files.update(ROOT/n for n in inputs['stage']['source']);files.update(ROOT/n for n in CHECK.INPUTS)
    files.update(ROOT/n for n in CHECK.AUDIT_FILES)
    files.update(ROOT/n for n in ANALYSES)
    files.update(p for p in RUN.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
    hashes={str(p.relative_to(ROOT)):sha(p) for p in sorted(files)};out.mkdir();(out/'frozen_source').mkdir()
    for name in (NOTE,SELF,TEST):
        p=out/('frozen_source/'+name if name.endswith('.py') else name);p.write_bytes((ROOT/name).read_bytes());hashes[str(p.relative_to(ROOT))]=sha(p)
    write(out/'report.json',report(inputs));hashes[str((out/'report.json').relative_to(ROOT))]=sha(out/'report.json')
    write(out/'manifest.json',dict(schema=1,files=hashes,**FLAGS));bind(ROOT,read(out/'manifest.json')['files'])
    load_inputs();bind(ROOT,read(out/'manifest.json')['files']);require(read(BASE/'latest.json')==previous,'no intervening publication')
    write(BASE/'latest-016.tmp',dict(publication='publication-016',manifest_sha256=sha(out/'manifest.json'),report_sha256=sha(out/'report.json'),**FLAGS));(BASE/'latest-016.tmp').replace(BASE/'latest.json')
    return dict(publication='publication-016',bound_files=len(hashes),**FLAGS)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('action',choices=['validate','publish']);args=parser.parse_args()
    print(json.dumps(publish() if args.action=='publish' else dict(all_passed=True,report=report(load_inputs())),sort_keys=True))

"""Publish the audited typed-storage search; publication archives are immutable."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
RUN=BASE/'anchored-storage-search-001'
REPLAY=BASE/'anchored-storage-leaf-replay-001'
FLAGS=dict(global_bound_proved=False,RH_proved=False)
NOTES=['ANCHORED_STORAGE_SEARCH_HANDOFF.txt','anchored_storage_uniform_scope.txt',
       'anchored_storage_cone_redundancy.txt','anchored_storage_resource_authorization.txt']

def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(condition,message):
    if not condition:raise ValueError(message)
def write(p,value):
    with p.open('x') as f:json.dump(value,f,sort_keys=True,indent=2,allow_nan=False);f.write('\n')
def bindings(base,hashes):
    for name,h in hashes.items():require(sha(base/name)==h,'bound artifact '+str(base/name))

def load_inputs():
    import run_anchored_storage_search as R
    import check_anchored_storage_search as I
    from publish_cancellation_complete_gram import prior_manifests
    priors=prior_manifests();m=read(BASE/'publication-007/manifest.json')
    require(len(m['files'])==401,'prior publication007 file count');bindings(ROOT,m['files'])
    priors['publication-007']=dict(manifest_sha256=sha(BASE/'publication-007/manifest.json'),bound_files=401)
    R.validate(RUN)
    review=read(RUN/'independent_verification.json')
    require(review.get('all_passed')is True,'whole independent stage admission')
    bindings(RUN,review['input_sha256'])
    source=read(RUN/'source_seal.json')
    require(set(source)==set(R.sources())==set(I.source_names()),'complete frozen source closure')
    bindings(ROOT,source);bindings(RUN/'frozen_source',source)
    terminal=read(RUN/'receipt.json')
    actual={str(p.relative_to(RUN)):sha(p) for p in RUN.rglob('*.json') if p.name not in ['receipt.json','independent_verification.json']}
    require(terminal['files_sha256']==actual and terminal['source_count']==len(source) and terminal['refitted']is False,'complete immutable terminal receipt')
    bindings(RUN,terminal['files_sha256'])
    protocol=read(RUN/'protocol.json')
    for key,value in dict(program=R.PROGRAM,language=I.B.SPEC,gram_specs=I.B.gram_specs(),storage_operator=I.B.SPEC,parallel=R.PARALLEL,limits=R.LIMITS,solver_limits=R.SOLVER_LIMITS,dual_limits=R.DUAL_LIMITS,tests=R.TESTS).items():
        require(protocol.get(key)==value,'preregistered protocol '+key)
    require(protocol['no_actual_signed_response_inputs']is True and protocol['final_refit']is False,'source selection and fixed transfer')
    tests=read(RUN/'tests.json');match=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',tests['stdout']+tests['stderr'])
    require(tests['returncode']==0 and match is not None,'prescore calibrations')
    decision=read(RUN/'decision.json');require(review['decision']==decision,'independently audited branching')
    jobs=[]
    for path in sorted((RUN/'jobs').glob('*.json')):
        if path.name.endswith('-proposal.json'):continue
        r=read(path);require(r['refitted']is False and all(r.get(k)is False for k in FLAGS),'finite job scope')
        if r['status']in ['exact_separator','finite_PSD_certificate']:require(r['independent_check']['verified']is True,'exact job admission')
        jobs.append((path,r))
    for phase,count in [('dual',1)]+([('primal',1)] if decision['run_primal'] else [])+([('final',2)] if decision['final_scales'] else []):
        I.verify_runtime(read(RUN/(phase+'_execution.json')),count)
    import run_anchored_storage_leaf_replay as K
    import check_anchored_storage_leaf_replay as J
    K.validate(REPLAY)
    kr=read(REPLAY/'independent_verification.json');require(kr.get('all_passed')is True,'independent leaf replay admission')
    bindings(REPLAY,kr['input_sha256'])
    ks=read(REPLAY/'source_seal.json');require(set(ks)==set(K.sources())==set(J.source_names()),'complete leaf replay source closure')
    bindings(ROOT,ks);bindings(REPLAY/'frozen_source',ks)
    kt=read(REPLAY/'receipt.json');actual={str(p.relative_to(REPLAY)):sha(p) for p in REPLAY.rglob('*.json') if p.name not in ['receipt.json','independent_verification.json']}
    require(kt['files_sha256']==actual and kt['source_count']==len(ks),'complete leaf replay terminal receipt')
    bindings(REPLAY,kt['files_sha256'])
    kp=read(REPLAY/'protocol.json');require(kp['limits']==K.LIMITS and kp['prepare_limits']==K.PREPARE_LIMITS and kp['parallel']==K.PARALLEL and kp['same_cone']is True and kp['no_new_float_search']is True,'same cone and authorized replay limits')
    ke=read(REPLAY/'execution.json');I.verify_runtime(ke,1)
    saved=read(REPLAY/'support.json');cp=read(RUN/'jobs/dual-000-proposal.json')
    require(saved['indices']==cp['support'] and len(saved['indices'])==703,'same full703 support')
    ktests=read(REPLAY/'tests.json');km=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',ktests['stdout']+ktests['stderr'])
    require(ktests['returncode']==0 and km is not None,'leaf replay calibrations')
    kres=read(REPLAY/'result.json') if (REPLAY/'result.json').exists() else None
    if kres and kres['status']=='exact_separator':
        require(kr['proof']['verified']is True and kr['proof']['same_support_verified']is True and kr['proof']['total_work_proxy']<=450000000,'full-cone and resource-admitted leaf separator')
        require(kres['synthesis']['saved_support']==saved['indices'],'all original variable indices retained')
    return dict(priors=priors,source=source,review=review,protocol=protocol,tests_passed=int(match.group(1)),decision=decision,jobs=jobs,
                replay_review=kr,replay_sources=ks,replay_result=kres,replay_tests_passed=int(km.group(1)))

def report(inputs):
    jobs=[]
    for p,r in inputs['jobs']:
        s=r.get('synthesis',{});entry=dict(file=str(p.relative_to(RUN)),sha256=sha(p),phase=r['phase'],status=r['status'],reason=s.get('reason',r.get('reason')),scales=r.get('scales'),cost=r['cost'])
        for key in ['constant_coordinates','lhs_dot_y']:
            if key in s:entry[key]=s[key]
        if s.get('saved_support')is not None:entry['saved_support_size']=len(s['saved_support'])
        compression=s.get('diagnostics',{}).get('row_compression')
        if compression is not None:entry['reconstruction']={k:v for k,v in compression.items() if not isinstance(v,(dict,list))}
        if s.get('grams'):
            entry['storage_K_nonzero']=any(v!='0' for row in s['grams']['storage_K'] for v in row)
            entry['fixed_matrices_sha256']=hashlib.sha256(json.dumps(s['grams'],sort_keys=True,separators=(',',':')).encode()).hexdigest()
        jobs.append(entry)
    admitted=any(r['phase']=='primal' and r['status']=='finite_PSD_certificate' for _,r in inputs['jobs'])
    separated=any(r['status']=='exact_separator' for _,r in inputs['jobs'])
    retry=inputs['replay_result'];recovered=bool(retry and retry['status']=='exact_separator')
    separated=separated or recovered
    leaf=retry.get('synthesis',{}).get('diagnostics',{}).get('leaf_elimination',{}) if retry else {}
    replay_report=dict(status=retry['status'] if retry else inputs['replay_review']['result_status'],source_count=len(inputs['replay_sources']),tests_passed=inputs['replay_tests_passed'],independent_receipt_sha256=sha(REPLAY/'independent_verification.json'),same_saved_support_count=703,new_floating_search=False,same_cone=True,work_limit=450000000,worker_memory_bytes=6*1024**3,total_memory_bytes=6*1024**3,cooperative_seconds=360,external_seconds=1200)
    if retry:
        replay_report.update(result_sha256=sha(REPLAY/'result.json'),cost=retry['cost'])
        for key in ['original_rows','original_variables','remaining_rows','remaining_variables','leaf_total_work_proxy','compilation_work_reserve','dual_build_work_proxy','dual_verification_work_reserve','total_work_proxy']:
            if key in leaf:replay_report[key]=leaf[key]
        replay_report['eliminated_variables_restored']=len(leaf.get('pivots',[]))
        comp=leaf.get('remaining_compression',{})
        replay_report['remaining_native_rows_after_compression']=comp.get('reduced_rows')
        replay_report['remaining_native_work_proxy']=comp.get('native_work_proxy')
        if recovered:
            replay_report.update(constant_coordinates=retry['synthesis']['constant_coordinates'],target_pairing=retry['synthesis']['lhs_dot_y'],full_original_equations_and_three_PSD_matrices_verified=True)
    next_action=('analyze admitted exact fixed state and weights for a uniform identity and critical scalar budget; no uniform promotion from the finite grid' if admitted else
                 'use the admitted storage-cone separator to diagnose missing arithmetic constraints or a structurally different coefficient/state law' if separated else
                 'inspect bounded numerical checkpoints and exact resource receipts before a preregistered same-proposal optimization or a different complete grammar')
    return dict(schema=8,previous_research_publication='publication-007',prior_manifests=inputs['priors'],source_count=len(inputs['source']),tests_passed=inputs['tests_passed'],independent_receipt_sha256=sha(RUN/'independent_verification.json'),gram_dimensions=dict(full_child=14,full_parent=14,storage_K=14),storage_is_nonnegative_SOS=False,signed_increment='child minus four parent',coercivity='R=e_prefix e_prefix^T+K; K PSD',original_target_and_all_scalar_sources_preserved=True,all_105_storage_pairs_retained=True,restricted_dual_redundant_cross_equations=91,redundancy_is_exact_not_source_truncation=True,initial_cost='1+v1^T K v1, v1=(1,0,0,1,0,...,0)',gamma_gate_scope='necessary for the uniform fixed-template critical extracted scalar budget under recorded unchanged scalar-growth hypotheses',uniform_recovery_is_conditional=True,scope_note_sha256=sha(ROOT/'anchored_storage_uniform_scope.txt'),historical_development_scales=True,decision=inputs['decision'],jobs=jobs,leaf_replay=replay_report,critical_finite_certificate_found=admitted,exact_storage_cone_separator_found=separated,uniform_innovation_bound_proved=False,future_resources=dict(current_worker_memory_bytes=6*1024**3,current_total_memory_bytes=6*1024**3,authorized_memory_when_limiting_bytes=16*1024**3,authorized_total_memory_when_limiting_bytes=16*1024**3,cooperative_seconds=360,external_seconds=1200,charged_backend_reconstruction_work=450000000),next_action=next_action,**FLAGS)

def publish():
    inputs=load_inputs();out=BASE/'publication-008';require(not out.exists(),'exclusive publication008')
    previous=read(BASE/'latest.json')
    require(previous['publication']=='publication-007' and previous['manifest_sha256']==sha(BASE/'publication-007/manifest.json') and previous['report_sha256']==sha(BASE/'publication-007/report.json'),'prior latest binding')
    files={ROOT/n for n in NOTES+['publish_cancellation_anchored_storage.py']}
    files.update(p for p in RUN.rglob('*') if p.is_file() and '__pycache__'not in p.parts)
    files.update(ROOT/n for n in inputs['source'])
    files.update(p for p in REPLAY.rglob('*') if p.is_file() and '__pycache__'not in p.parts)
    files.update(ROOT/n for n in inputs['replay_sources'])
    files.update(BASE/'publication-007'/n for n in ['manifest.json','report.json'])
    hashes={str(p.relative_to(ROOT)):sha(p) for p in sorted(files)}
    out.mkdir();(out/'frozen_source').mkdir()
    for n in NOTES+['publish_cancellation_anchored_storage.py']:
        p=out/('frozen_source/'+n if n.endswith('.py') else n);p.write_bytes((ROOT/n).read_bytes());hashes[str(p.relative_to(ROOT))]=sha(p)
    write(out/'report.json',report(inputs));hashes[str((out/'report.json').relative_to(ROOT))]=sha(out/'report.json')
    write(out/'manifest.json',dict(schema=1,files=hashes,**FLAGS));bindings(ROOT,read(out/'manifest.json')['files'])
    load_inputs();bindings(ROOT,read(out/'manifest.json')['files'])
    require(read(BASE/'latest.json')==previous,'no intervening publication')
    pointer=dict(publication='publication-008',manifest_sha256=sha(out/'manifest.json'),report_sha256=sha(out/'report.json'),**FLAGS)
    write(BASE/'latest-008.tmp',pointer);(BASE/'latest-008.tmp').replace(BASE/'latest.json')
    return dict(publication='publication-008',bound_files=len(hashes),**FLAGS)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('action',choices=['validate','publish']);args=parser.parse_args()
    print(json.dumps(publish() if args.action=='publish' else dict(all_passed=True,publication_written=False,report=report(load_inputs()))))

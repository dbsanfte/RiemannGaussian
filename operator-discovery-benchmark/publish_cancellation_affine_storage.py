"""Publish the audited affine diagnostic and complete full15 search immutably."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
PROBE=BASE/'affine-storage-moment-probe-001'
RUN=BASE/'affine-storage-search-001'
PREVIOUS=BASE/'publication-008'
FLAGS=dict(global_bound_proved=False,RH_proved=False)
NOTES=['AFFINE_STORAGE_SEARCH_HANDOFF.txt','affine_storage_uniform_scope.txt']


def read(path):return json.loads(path.read_text())
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def require(value,message):
    if not value:raise ValueError(message)
def bind(base,hashes):
    for name,h in hashes.items():require(sha(base/name)==h,'bound affine publication artifact '+str(base/name))
def write(path,value):
    with path.open('x') as stream:json.dump(value,stream,sort_keys=True,indent=2,allow_nan=False);stream.write('\n')


def archived(directory,source_names,validate):
    validate(directory)
    review=read(directory/'independent_verification.json')
    require(review.get('all_passed')is True,'whole independent admission '+directory.name)
    bind(directory,review['input_sha256'])
    source=read(directory/'source_seal.json')
    require(set(source)==set(source_names()),'complete source closure '+directory.name)
    bind(ROOT,source);bind(directory/'frozen_source',source)
    receipt=read(directory/'receipt.json')
    actual={str(p.relative_to(directory)):sha(p) for p in directory.rglob('*.json') if p.name not in ['receipt.json','independent_verification.json']}
    require(receipt['files_sha256']==actual and receipt['source_count']==len(source),'complete immutable terminal receipt '+directory.name)
    tests=read(directory/'tests.json')
    match=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',tests['stdout']+tests['stderr'])
    require(tests['returncode']==0 and match is not None,'successful prescore calibrations '+directory.name)
    return dict(review=review,source=source,tests_passed=int(match.group(1)))


def load_inputs():
    import publish_cancellation_anchored_storage as OLD
    import run_affine_storage_moment_probe as P
    import check_affine_storage_probe_run as PC
    import run_affine_storage_search as S
    import check_affine_storage_search as SC
    priors=OLD.load_inputs()['priors']
    manifest=read(PREVIOUS/'manifest.json');require(len(manifest['files'])==294,'unchanged publication008 count');bind(ROOT,manifest['files'])
    priors['publication-008']=dict(manifest_sha256=sha(PREVIOUS/'manifest.json'),bound_files=len(manifest['files']))
    probe=archived(PROBE,PC.source_names,P.validate)
    search=archived(RUN,SC.source_names,S.validate)
    require(set(probe['source'])==set(P.sources()),'producer/checker diagnostic source closure')
    require(set(search['source'])==set(S.sources()),'producer/checker full15 source closure')
    pr=read(PROBE/'result.json');require(pr['status']=='witness_invalid_for_affine_cone' and probe['review']['result_status']==pr['status'] and probe['review']['proof']['verified']is True,'admitted diagnostic justifies expanded search')
    spec=read(RUN/'protocol.json')
    expected=dict(program=S.PROGRAM,language=SC.B.SPEC,gram_specs=SC.B.gram_specs(),storage_operator=SC.B.SPEC,
                  limits=S.LIMITS,solver_limits=S.SOLVER_LIMITS,dual_limits=S.DUAL_LIMITS,parallel=S.PARALLEL,tests=S.TESTS,
                  final_refit=False,no_actual_signed_response_inputs=True)
    for key,value in expected.items():require(spec.get(key)==value,'frozen full15 protocol '+key)
    decision=read(RUN/'decision.json');require(search['review']['decision']==decision,'independent branching')
    jobs=[]
    for path in sorted((RUN/'jobs').glob('*.json')):
        if path.name.endswith('-proposal.json'):continue
        result=read(path)
        require(result.get('refitted')is False and all(result.get(k)is False for k in FLAGS),'finite frozen job')
        if result['status'] in ['exact_separator','finite_PSD_certificate']:
            require(result['independent_check']['verified']is True,'exact job admission')
            checks={r['file']:r['proof'] for r in search['review']['checks']}
            require(checks[str(path.relative_to(RUN))]['verified']is True,'whole archive certificate admission')
        jobs.append((path,result))
    for phase,count in [('dual',1)]+([('primal',1)] if decision['run_primal'] else [])+([('final',2)] if decision['final_scales'] else []):
        SC.verify_runtime(read(RUN/(phase+'_execution.json')),count)
    return dict(priors=priors,probe=probe,probe_result=pr,search=search,decision=decision,jobs=jobs)


def report(inputs):
    groups={}
    for name,r in inputs['probe_result']['probe']['groups'].items():
        groups[name]={k:r[k] for k in ['status','direction','quadratic_value','expanded_polynomial_sha256'] if k in r}
        groups[name]['missing_coordinates']=len(r['missing'])
    rows=[]
    for path,r in inputs['jobs']:
        s=r.get('synthesis',{})
        entry=dict(file=str(path.relative_to(RUN)),sha256=sha(path),phase=r['phase'],status=r['status'],scales=r.get('scales'),
                   reason=s.get('reason',r.get('reason')),cost=r['cost'])
        for key in ['lhs_dot_y','constant_coordinates','all_C_q_extension_requires_zero_constant_coordinates']:
            if key in s:entry[key]=s[key]
        if 'saved_support' in s:entry['saved_support_size']=len(s['saved_support'])
        leaf=s.get('diagnostics',{}).get('leaf_elimination')
        if leaf:
            entry['leaf_reconstruction']={k:leaf[k] for k in ['original_rows','original_variables','remaining_rows','remaining_variables',
                'leaf_total_work_proxy','compilation_work_reserve','dual_build_work_proxy','dual_verification_work_reserve','total_work_proxy'] if k in leaf}
            entry['leaf_reconstruction']['eliminated_variables']=len(leaf.get('pivots',[]))
            entry['leaf_reconstruction']['restored_all_original_variables']=leaf.get('status')=='full_original_equality_verified'
            compression=leaf.get('remaining_compression',{})
            entry['leaf_reconstruction']['native_rows_after_compression']=compression.get('reduced_rows')
            entry['leaf_reconstruction']['native_work_proxy']=compression.get('native_work_proxy')
        if s.get('grams'):
            entry['fixed_matrices_sha256']=hashlib.sha256(json.dumps(s['grams'],sort_keys=True,separators=(',',':')).encode()).hexdigest()
        rows.append(entry)
    admitted=any(r['phase']=='primal' and r['status']=='finite_PSD_certificate' for _,r in inputs['jobs'])
    separated=any(r['status']=='exact_separator' for _,r in inputs['jobs'])
    next_action=('try to prove the admitted fixed identity and critical scalar budget uniformly with the required q schedule' if admitted else
                 'test systematic valid arithmetic localizers or a different uniformly recoverable coefficient/state law against the new separator' if separated else
                 'inspect retained numerical and exact reconstruction checkpoints; preserve unknown feasibility')
    return dict(schema=9,previous_research_publication='publication-008',prior_manifests=inputs['priors'],
        diagnostic=dict(status=inputs['probe_result']['status'],groups=groups,tests_passed=inputs['probe']['tests_passed'],
            source_count=len(inputs['probe']['source']),cost=inputs['probe_result']['cost'],
            result_sha256=sha(PROBE/'result.json'),independent_receipt_sha256=sha(PROBE/'independent_verification.json'),
            no_new_floating_search=True,larger_cone_feasibility_proved=False),
        source_count=len(inputs['search']['source']),tests_passed=inputs['search']['tests_passed'],
        independent_receipt_sha256=sha(RUN/'independent_verification.json'),
        gram_dimensions=dict(full_child=15,full_parent=15,storage_K=15),unit_prepended_to_every_ordinary_state=True,
        complete_upper_pairs_per_matrix=120,original_target_and_all_scalar_sources_preserved=True,
        storage_is_nonnegative_SOS=False,signed_increment='child minus four parent',
        formal_constant_vector=['1']+['0']*5+['-1/2']*9,
        actual_initial_vector=['1','1','0','0','1']+['0']*10,
        initial_cost='1+u^T K u',historical_development_scales=True,
        gamma_gate_scope='conditional on uniform fixed-template matching and critical extracted scalar budget under unchanged scalar-growth hypotheses',
        scope_note_sha256=sha(ROOT/'affine_storage_uniform_scope.txt'),decision=inputs['decision'],jobs=rows,
        critical_finite_certificate_found=admitted,exact_affine_storage_cone_separator_found=separated,
        uniform_innovation_bound_proved=False,
        resources=dict(worker_memory_bytes=6*1024**3,total_memory_bytes=6*1024**3,
            authorized_memory_when_limiting_bytes=16*1024**3,cooperative_seconds=360,external_seconds=1200,
            charged_backend_reconstruction_work=450000000),next_action=next_action,**FLAGS)


def publish():
    inputs=load_inputs();out=BASE/'publication-009';require(not out.exists(),'exclusive publication009')
    previous=read(BASE/'latest.json')
    require(previous['publication']=='publication-008' and previous['manifest_sha256']==sha(PREVIOUS/'manifest.json') and previous['report_sha256']==sha(PREVIOUS/'report.json'),'latest publication008 binding')
    files={ROOT/n for n in NOTES+['publish_cancellation_affine_storage.py']}
    for directory,data in [(PROBE,inputs['probe']),(RUN,inputs['search'])]:
        files.update(p for p in directory.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
        files.update(ROOT/n for n in data['source'])
    files.update(PREVIOUS/n for n in ['manifest.json','report.json'])
    hashes={str(p.relative_to(ROOT)):sha(p) for p in sorted(files)}
    out.mkdir();(out/'frozen_source').mkdir()
    for name in NOTES+['publish_cancellation_affine_storage.py']:
        p=out/('frozen_source/'+name if name.endswith('.py') else name)
        p.write_bytes((ROOT/name).read_bytes());hashes[str(p.relative_to(ROOT))]=sha(p)
    write(out/'report.json',report(inputs));hashes[str((out/'report.json').relative_to(ROOT))]=sha(out/'report.json')
    write(out/'manifest.json',dict(schema=1,files=hashes,**FLAGS));bind(ROOT,read(out/'manifest.json')['files'])
    load_inputs();bind(ROOT,read(out/'manifest.json')['files'])
    require(read(BASE/'latest.json')==previous,'no intervening publication')
    pointer=dict(publication='publication-009',manifest_sha256=sha(out/'manifest.json'),report_sha256=sha(out/'report.json'),**FLAGS)
    write(BASE/'latest-009.tmp',pointer);(BASE/'latest-009.tmp').replace(BASE/'latest.json')
    return dict(publication='publication-009',bound_files=len(hashes),**FLAGS)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('action',choices=['validate','publish'])
    args=parser.parse_args()
    print(json.dumps(publish() if args.action=='publish' else dict(all_passed=True,publication_written=False,report=report(load_inputs()))))

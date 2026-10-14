"""Publish the audited arithmetic relation/state expansion and its full search."""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
import publish_cancellation_affine_storage as OLD

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
PROBE=BASE/'primitive-state-localizer-probe-001'
RUN=BASE/'primitive-state-localizer-search-001'
PREVIOUS=BASE/'publication-009'
FLAGS=dict(global_bound_proved=False,RH_proved=False)
NOTES=['PRIMITIVE_STATE_LOCALIZER_SEARCH_HANDOFF.txt','primitive_state_localizers_uniform_scope.txt']
read,sha,require,bind,write,archived=OLD.read,OLD.sha,OLD.require,OLD.bind,OLD.write,OLD.archived


def load_inputs():
    import run_primitive_state_localizer_probe as P
    import check_primitive_state_localizer_probe_run as PC
    import run_primitive_state_localizer_search as S
    import check_primitive_state_localizer_search as SC
    priors=OLD.load_inputs()['priors']
    manifest=read(PREVIOUS/'manifest.json')
    require(len(manifest['files'])==275,'unchanged publication009 count');bind(ROOT,manifest['files'])
    priors['publication-009']=dict(manifest_sha256=sha(PREVIOUS/'manifest.json'),bound_files=len(manifest['files']))
    probe=archived(PROBE,PC.source_names,P.validate)
    search=archived(RUN,SC.source_names,S.validate)
    require(set(probe['source'])==set(P.sources()),'producer/checker diagnostic closure')
    require(set(search['source'])==set(S.sources()),'producer/checker localizer search closure')
    pr=read(PROBE/'result.json')
    require(pr['status']=='witness_invalid_for_localizer_cone' and probe['review']['result_status']==pr['status']
            and probe['review']['proof']['verified']is True,'admitted diagnostic justifies expanded search')
    spec=read(RUN/'protocol.json')
    expected=dict(program=S.PROGRAM,language=SC.B.SPEC,gram_specs=SC.B.gram_specs(),storage_operator=SC.B.B.SPEC,
        dictionary=SC.B.descriptors(),limits=S.LIMITS,solver_limits=S.SOLVER_LIMITS,dual_limits=S.DUAL_LIMITS,
        parallel=S.PARALLEL,tests=S.TESTS,final_refit=False,no_actual_signed_response_inputs=True,
        primitive_state_closure='all seven primitive relation families, both regions and all fifteen state multipliers; 210 additional signed groups',
        primitive_archive_hash_scope='complete semantic archive except optional polynomial_sha256 metadata; full native groups, primitive sources and multipliers separately bound')
    for key,value in expected.items():require(spec.get(key)==value,'frozen arithmetic localizer protocol '+key)
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
    import cancellation_primitive_state_localizers as L
    pr=inputs['probe_result'];p=pr['probe'];descriptors=L.additions()['relation'];families={}
    require(len(descriptors)==len(p['rows'])==210,'every declared diagnostic column')
    for d,r in zip(descriptors,p['rows']):
        require(d['id']==r['descriptor_id'],'diagnostic descriptor binding')
        families.setdefault(d['primitive_family'],Counter())[r['status']]+=1
    counts=Counter(r['status'] for r in p['rows'])
    require(dict(counts)==p['counts'],'diagnostic counts')
    rows=[]
    for path,r in inputs['jobs']:
        s=r.get('synthesis',{})
        entry=dict(file=str(path.relative_to(RUN)),sha256=sha(path),phase=r['phase'],status=r['status'],scales=r.get('scales'),
                   reason=s.get('reason',r.get('reason')),cost=r['cost'])
        for key in ['lhs_dot_y','constant_coordinates','all_C_q_extension_requires_zero_constant_coordinates']:
            if key in s:entry[key]=s[key]
        if 'saved_support' in s:entry['saved_support_size']=len(s['saved_support'])
        checkpoint=s.get('proposal_checkpoint')
        if checkpoint:
            entry['complete_moment_coordinates']=len(checkpoint['monomials'])
            entry['complete_columns']=len(checkpoint['column_layout'])
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
    next_action=('attempt a uniform proof of the fixed identity and its critical scalar budget, with all required q and boundary conditions' if admitted else
                 'test systematic refinements of arithmetic grouping or uniformly recoverable scale laws against the new separator' if separated else
                 'inspect retained numerical and exact reconstruction checkpoints; preserve unknown feasibility')
    return dict(schema=10,previous_research_publication='publication-009',prior_manifests=inputs['priors'],
        diagnostic=dict(status=pr['status'],counts=p['counts'],family_counts=families,missing_coordinates=len(p['missing_coordinates']),
            tests_passed=inputs['probe']['tests_passed'],source_count=len(inputs['probe']['source']),cost=pr['cost'],
            result_sha256=sha(PROBE/'result.json'),independent_receipt_sha256=sha(PROBE/'independent_verification.json'),
            no_new_floating_search=True,larger_cone_feasibility_proved=False,
            scope='unit relations also violate the old witness; this is arithmetic compatibility evidence, not a prime-distribution estimate'),
        source_count=len(inputs['search']['source']),tests_passed=inputs['search']['tests_passed'],
        independent_receipt_sha256=sha(RUN/'independent_verification.json'),
        gram_dimensions=dict(full_child=15,full_parent=15,storage_K=15),additional_signed_groups=210,
        scalar_square_groups=366,scalar_relation_groups=613,
        source_rule='every existing primitive family times every affine state coordinate, in both regions',
        relation_scope='grouped subspace of the arithmetic ideal with fixed shared coefficients',
        original_target_and_all_scalar_sources_preserved=True,storage_is_nonnegative_SOS=False,
        signed_increment='child minus four parent',initial_cost='1+u^T K u',historical_development_scales=True,
        added_scalar_charge='O_beta(X^2) for fixed weights using only SF(t)<=t and pi(t)<=t',
        gamma_gate_scope='conditional on uniform fixed-template matching and critical extracted scalar budget under unchanged scalar-growth hypotheses',
        scope_note_sha256=sha(ROOT/'primitive_state_localizers_uniform_scope.txt'),decision=inputs['decision'],jobs=rows,
        critical_finite_certificate_found=admitted,exact_primitive_state_cone_separator_found=separated,
        uniform_innovation_bound_proved=False,
        resources=dict(worker_memory_bytes=6*1024**3,total_memory_bytes=6*1024**3,
            authorized_memory_when_limiting_bytes=16*1024**3,cooperative_seconds=360,external_seconds=1200,
            charged_backend_reconstruction_work=450000000),next_action=next_action,**FLAGS)


def publish():
    inputs=load_inputs();out=BASE/'publication-010';require(not out.exists(),'exclusive publication010')
    previous=read(BASE/'latest.json')
    require(previous['publication']=='publication-009' and previous['manifest_sha256']==sha(PREVIOUS/'manifest.json')
            and previous['report_sha256']==sha(PREVIOUS/'report.json'),'latest publication009 binding')
    files={ROOT/n for n in NOTES+['publish_cancellation_primitive_state.py']}
    for directory,data in [(PROBE,inputs['probe']),(RUN,inputs['search'])]:
        files.update(p for p in directory.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
        files.update(ROOT/n for n in data['source'])
    files.update(PREVIOUS/n for n in ['manifest.json','report.json'])
    hashes={str(p.relative_to(ROOT)):sha(p) for p in sorted(files)}
    out.mkdir();(out/'frozen_source').mkdir()
    for name in NOTES+['publish_cancellation_primitive_state.py']:
        p=out/('frozen_source/'+name if name.endswith('.py') else name)
        p.write_bytes((ROOT/name).read_bytes());hashes[str(p.relative_to(ROOT))]=sha(p)
    write(out/'report.json',report(inputs));hashes[str((out/'report.json').relative_to(ROOT))]=sha(out/'report.json')
    write(out/'manifest.json',dict(schema=1,files=hashes,**FLAGS));bind(ROOT,read(out/'manifest.json')['files'])
    load_inputs();bind(ROOT,read(out/'manifest.json')['files'])
    require(read(BASE/'latest.json')==previous,'no intervening publication')
    pointer=dict(publication='publication-010',manifest_sha256=sha(out/'manifest.json'),report_sha256=sha(out/'report.json'),**FLAGS)
    write(BASE/'latest-010.tmp',pointer);(BASE/'latest-010.tmp').replace(BASE/'latest.json')
    return dict(publication='publication-010',bound_files=len(hashes),**FLAGS)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('action',choices=['validate','publish'])
    args=parser.parse_args()
    print(json.dumps(publish() if args.action=='publish' else dict(all_passed=True,publication_written=False,report=report(load_inputs()))))

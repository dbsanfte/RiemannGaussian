"""Publish the equivalent numerical reformulation of the arithmetic state search."""
import argparse
import json
from pathlib import Path
import publish_cancellation_primitive_state as OLD

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
RUN=BASE/'primitive-state-scaled-search-001'
PREVIOUS=BASE/'publication-010'
NOTE='PRIMITIVE_STATE_NUMERICAL_SEARCH_HANDOFF.txt'
SELF='publish_cancellation_primitive_state_numerical.py'
FLAGS=dict(global_bound_proved=False,RH_proved=False)
read,sha,require,bind,write,archived=OLD.read,OLD.sha,OLD.require,OLD.bind,OLD.write,OLD.archived


def load_inputs():
    import run_primitive_state_scaled_search as S
    import check_primitive_state_scaled_search_v2 as C
    prior=OLD.load_inputs()
    manifest=read(PREVIOUS/'manifest.json');require(len(manifest['files'])==304,'publication010 closure')
    bind(ROOT,manifest['files'])
    previous_spec=read(OLD.RUN/'protocol.json');spec=read(RUN/'protocol.json')
    for key in ['program','training_scales','final_scales','language','dictionary','gram_specs','storage_operator',
                'primitive_state_closure','primitive_archive_hash_scope','final_refit','no_actual_signed_response_inputs']:
        require(spec[key]==previous_spec[key],'unchanged mathematical search '+key)
    for key,value in dict(numerical_transformation=C.NUMERICAL_TRANSFORMATION,limits=S.LIMITS,
                         solver_limits=S.SOLVER_LIMITS,dual_limits=S.DUAL_LIMITS,parallel=S.PARALLEL,tests=S.TESTS).items():
        require(spec.get(key)==value,'frozen numerical search '+key)
    data=archived(RUN,C.source_names,S.validate)
    revision=data['review'].get('auditor_revision',{})
    require(revision.get('schema')=='prepared-checkpoint-audit-revision-v2' and revision.get('test_returncode')==0
            and revision.get('tests_passed')==10,'corrected prepared-checkpoint auditor tests')
    require(set(revision['source_sha256'])=={'check_primitive_state_scaled_search_v2.py','test_check_primitive_state_scaled_search_v2.py'},'complete audit revision source')
    bind(ROOT,revision['source_sha256'])
    require(set(data['source'])==set(S.sources()),'complete independent source closure')
    decision=read(RUN/'decision.json');require(decision==data['review']['decision'],'independent branch decisions')
    checks={row['file']:row['proof'] for row in data['review']['checks']};jobs=[]
    for path in sorted((RUN/'jobs').glob('*.json')):
        if path.name.endswith('-proposal.json'):continue
        r=read(path);require(r.get('refitted')is False and all(r.get(k)is False for k in FLAGS),'finite job scope')
        require(checks[str(path.relative_to(RUN))]['verified']is True,'whole job admission')
        if r['status'] in ['exact_separator','finite_PSD_certificate']:
            require(r['independent_check']['verified']is True,'independent exact certificate')
        if r['phase'] in ['dual','primal'] and 'case_hashes' in r:
            previous=read(OLD.RUN/'jobs'/path.name)
            for key in ['ordinary_case_hashes','case_hashes','gram_block_hashes','storage_block_hashes',
                        'dictionary_sha256','primitive_state_archive_hashes','primitive_source_hashes','multiplier_source_hashes']:
                require(r[key]==previous[key],'identical complete original system '+key)
        jobs.append((path,r))
    for phase,count in [('dual',1)]+([('primal',1)] if decision['run_primal'] else [])+([('final',2)] if decision['final_scales'] else []):
        C.verify_runtime(read(RUN/(phase+'_execution.json')),count)
    priors=dict(prior['priors']);priors['publication-010']=dict(manifest_sha256=sha(PREVIOUS/'manifest.json'),bound_files=304)
    return dict(priors=priors,search=data,decision=decision,jobs=jobs)


def report(inputs):
    rows=[]
    for path,r in inputs['jobs']:
        s=r.get('synthesis',{});diag=s.get('diagnostics',{})
        row=dict(file=str(path.relative_to(RUN)),sha256=sha(path),phase=r['phase'],status=r['status'],
                 reason=s.get('reason',r.get('reason')),cost=r['cost'],scales=r.get('scales'))
        numerical=s.get('proposal_diagnostics',diag.get('proposal_diagnostics',diag.get('numerical_proposal')))
        if numerical:
            receipt=numerical['transformation_receipt']
            row['numerical_proposal']=dict(original_rows=receipt['original_rows'],retained_rows=len(receipt['retained_indices']),
                original_variables=receipt['variables'],original_system_sha256=receipt['original_hash'],
                zero_rows=sum(i is None for i in receipt['row_representative']),
                exact_compression_operations=receipt['operations'],source_cells=receipt['cells'],
                attempts=numerical['attempts'],worker_verification_pending=diag.get('numerical_verification_pending',False))
            if diag.get('numerical_work_reserve')is not None:
                row['numerical_proposal']['charged_work_reserve']=diag['numerical_work_reserve']
            if numerical.get('support')is not None:row['numerical_proposal']['proposed_support_size']=len(numerical['support'])
        for key in ['lhs_dot_y','constant_coordinates','all_C_q_extension_requires_zero_constant_coordinates']:
            if key in s:row[key]=s[key]
        if s.get('saved_support')is not None:row['exact_support_size']=len(s['saved_support'])
        if diag.get('leaf_elimination'):
            leaf=diag['leaf_elimination']
            row['leaf_reconstruction']={k:leaf[k] for k in ['status','original_rows','original_variables','remaining_rows',
                'remaining_variables','leaf_total_work_proxy','compilation_work_reserve','dual_build_work_proxy',
                'dual_verification_work_reserve','total_work_proxy'] if k in leaf}
        if diag.get('native_attempt_receipts'):
            row['native_attempt_count']=len(diag['native_attempt_receipts'])
            row['total_charged_work_proxy']=diag.get('total_charged_work_proxy')
        rows.append(row)
    admitted=any(r['phase']=='primal' and r['status']=='finite_PSD_certificate' for _,r in inputs['jobs'])
    separated=any(r['status']=='exact_separator' for _,r in inputs['jobs'])
    return dict(schema=11,previous_research_publication='publication-010',prior_manifests=inputs['priors'],
        source_count=len(inputs['search']['source']),tests_passed=inputs['search']['tests_passed'],
        independent_receipt_sha256=sha(RUN/'independent_verification.json'),
        auditor_revision=inputs['search']['review']['auditor_revision'],
        mathematical_cone_and_target_unchanged=True,
        numerical_transformation='exact augmented proportional-row compression and positive infinity scaling; identity columns',
        full_original_equations_required_for_exact_admission=True,numerical_rank_truncation=False,
        charged_reserve_includes_numerical_preprocessing_and_independent_replay=True,
        historical_development_scales=True,decision=inputs['decision'],jobs=rows,
        critical_finite_certificate_found=admitted,exact_primitive_state_cone_separator_found=separated,
        uniform_innovation_bound_proved=False,
        resources=dict(worker_memory_bytes=6*1024**3,total_memory_bytes=6*1024**3,cooperative_seconds=360,
            external_seconds=1200,charged_backend_reconstruction_work=450000000),
        next_action=('attempt a uniform identity and critical budget proof for the fixed candidate with required q/boundary conditions' if admitted else
                     'use the new exact obstruction to test systematic arithmetic refinements' if separated else
                     'capture detailed numerical termination and residual logs; investigate exact simplification and use authorized runtime extension where needed'),**FLAGS)


def publish():
    inputs=load_inputs();out=BASE/'publication-011';require(not out.exists(),'exclusive publication011')
    previous=read(BASE/'latest.json')
    require(previous['publication']=='publication-010' and previous['manifest_sha256']==sha(PREVIOUS/'manifest.json')
            and previous['report_sha256']==sha(PREVIOUS/'report.json'),'latest publication010 binding')
    files={ROOT/NOTE,ROOT/SELF,PREVIOUS/'manifest.json',PREVIOUS/'report.json'}
    files.update(p for p in RUN.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
    files.update(ROOT/n for n in inputs['search']['source'])
    files.update(ROOT/n for n in inputs['search']['review']['auditor_revision']['source_sha256'])
    hashes={str(p.relative_to(ROOT)):sha(p) for p in sorted(files)}
    out.mkdir();(out/'frozen_source').mkdir()
    for name in [NOTE,SELF]:
        p=out/('frozen_source/'+name if name.endswith('.py') else name)
        p.write_bytes((ROOT/name).read_bytes());hashes[str(p.relative_to(ROOT))]=sha(p)
    write(out/'report.json',report(inputs));hashes[str((out/'report.json').relative_to(ROOT))]=sha(out/'report.json')
    write(out/'manifest.json',dict(schema=1,files=hashes,**FLAGS));bind(ROOT,read(out/'manifest.json')['files'])
    load_inputs();bind(ROOT,read(out/'manifest.json')['files'])
    require(read(BASE/'latest.json')==previous,'no intervening publication')
    pointer=dict(publication='publication-011',manifest_sha256=sha(out/'manifest.json'),report_sha256=sha(out/'report.json'),**FLAGS)
    write(BASE/'latest-011.tmp',pointer);(BASE/'latest-011.tmp').replace(BASE/'latest.json')
    return dict(publication='publication-011',bound_files=len(hashes),**FLAGS)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('action',choices=['validate','publish'])
    args=parser.parse_args()
    print(json.dumps(publish() if args.action=='publish' else dict(all_passed=True,publication_written=False,report=report(load_inputs()))))

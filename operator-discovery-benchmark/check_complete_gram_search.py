"""Independent complete-regional signed search, proposal and stage audit."""
import ast
import json
import math
from pathlib import Path
from fractions import Fraction as F
import check_cancellation_complete_gram_program as B
import check_cancellation_shared_gram as G
import check_joint_gram_compressed_replay as C
import check_joint_gram_search as OLD
ROOT=Path(__file__).resolve().parent
FLAGS=dict(global_bound_proved=False,RH_proved=False)
PROGRAM=dict(target='mu',q=6,C=32,claim='critical',constraint='zero_cubic',dictionary_mode='extended',allow_constant_slack=True)

def verify_dual_checkpoint(checkpoint,instances,blocks,specs):
    if checkpoint.get('schema')!='shared-Gram-dual-proposal-v2' or checkpoint.get('proposal_only')is not True or checkpoint.get('certified')is not False:raise ValueError('proposal-only dual checkpoint')
    if len(json.dumps(checkpoint,sort_keys=True,separators=(',',':'),allow_nan=False).encode())>8388608:raise ValueError('8MiB checkpoint')
    columns,lhs,domain,shape,offset,layout=OLD.checkpoint_columns(instances,blocks,specs)
    ns,nr=shape;nn=list(range(ns))+list(range(ns+2*nr,offset));rr=list(range(ns,ns+2*nr))
    for entry in layout[offset:]:
        (nn if entry['i']==entry['j'] else rr).append(entry['index'])
    expected=dict(source_hashes=list(map(G.digest,instances)),gram_block_hashes=list(map(G.digest,blocks)),gram_specs=specs,monomials=[dict(instance=m[0],m=list(m[1:])) for m in domain],scalar_shape=shape,scalar_offset=offset,column_layout=layout,layout_hash=G.digest(layout),exact_columns_hash=G.digest([[[list(m),str(q)] for m,q in sorted(p.items())] for p in columns]),exact_target_hash=G.digest([[list(m),str(q)] for m,q in sorted(lhs.items())]),nonnegative_indices=nn,relation_indices=rr,dual_equation_order=rr+nn,dual_variable_order='positive monomial coordinates; negative monomial coordinates; nonnegative column slacks',numerical_options=dict(solver='HiGHS',threads=1,parallel=False,support_threshold='1e-8'),refitted=False)
    expected['row_order_hash']=G.digest(expected['monomials'])
    for key,value in expected.items():
        if checkpoint.get(key)!=value:raise ValueError('complete exact checkpoint binding '+key)
    if checkpoint.get('phase') not in ['prepared_domain','LP_proposal','native_reconstruction','independent_admission']:raise ValueError('checkpoint phase')
    support=checkpoint['support'];variables=2*len(domain)+len(nn)
    if support is not None and (type(support)is not list or any(type(i)is not int or not 0<=i<variables for i in support) or len(support)!=len(set(support))):raise ValueError('saved support variable domain')
    limits=checkpoint['limits'];expected_limits=dict(time_limit=180,max_work=450000000,max_cells=4000000,max_preprocessing_operations=200000000,max_preprocessing_cells=4000000,max_rows=2500,max_variables=60000,max_denominator=2**4096,max_coefficient_bits=4096)
    if limits!=expected_limits:raise ValueError('frozen dual checkpoint limits')
    if any(checkpoint.get(k)is not False for k in ['global_bound_proved','RH_proved']):raise ValueError('proposal finite scope')
    return dict(verified=True,complete_exact_domain_and_columns_verified=True,proposal_only=True)

def verify_compressed_dual(instances,blocks,specs,result):
    full=G.verify_dual(instances,blocks,specs,result)
    columns,lhs,domain,nn,rr=C.independent_columns(instances,blocks,specs);eq,target=C.dual_equations(columns,lhs,domain,nn,rr);support=result['saved_support'];report=result['diagnostics']['row_compression'];variables=2*len(domain)+len(nn)
    if report['dual_build_work_proxy']!=(len(columns)+1)*variables or report['dual_verification_work_reserve']!=3*sum(map(len,columns))+2*len(lhs)+variables+2*len(domain)+len(support)+1:raise ValueError('exact dual fullwork accounting')
    if report['preprocessing_work']>200000000 or report.get('preprocessing_actual_work',report['preprocessing_work'])>200000000 or report['preprocessing_cells']>4000000:raise ValueError('preprocessing work/cell caps')
    compression=C.verify_producer_compression(eq,target,support,report);C.verify_original_solution(eq,target,support,result['exact_support_weights'])
    if any(F(q)<0 for q in result['exact_support_weights']):raise ValueError('nonnegative exact support weights')
    v=[F(0)]*variables
    for i,q in zip(support,result['exact_support_weights']):v[i]=F(q)
    if [v[i]-v[i+len(domain)] for i in range(len(domain))]!=list(map(F,result['weights'])):raise ValueError('same support reconstructed moments')
    return dict(verified=True,full_Gram_dual=full,compression=compression,**FLAGS)

def expected_plan(dual_status,primal_status=None):
    if dual_status=='exact_separator':return []
    if primal_status is None:return [dict(phase='primal',program=PROGRAM)]
    if primal_status=='finite_PSD_certificate':return [dict(phase='final',program=PROGRAM,X=X) for X in [8,13]]
    return []

def verify_fixed_transfer(training,result):
    if training['status']!='finite_PSD_certificate' or result['status']!='finite_PSD_certificate' or result['synthesis']['weights']!=training['synthesis']['weights'] or result['synthesis']['grams']!=training['synthesis']['grams']:raise ValueError('unchanged admitted training candidate')
    if result.get('refitted') is not False or result['program']!=PROGRAM or result['scales'] not in [[8],[13]]:raise ValueError('fixed transfer case')
    return True

def verify_record(record,phase,scales):
    if record['program']!=PROGRAM or record.get('scales',scales)!=scales or record['phase']!=phase or record.get('refitted')is not False:raise ValueError('signed-only fixed stage case')
    if any(record.get(k)is not False for k in ['global_bound_proved','RH_proved']):raise ValueError('finite stage scope')
    built=[B.build(PROGRAM,X) for X in scales];ordinary=[b['instance'] for b in built];instances=list(ordinary);blocks=[b['gram_blocks'] for b in built]
    if phase in ['dual','train','primal']:
        aux=B.auxiliary();instances.append(aux['instance']);blocks.append(aux['gram_blocks'])
    expected=dict(ordinary_case_hashes=list(map(G.digest,ordinary)),case_hashes=list(map(G.digest,instances)),gram_block_hashes=list(map(G.digest,blocks)),gram_archive_hashes=[G.digest(b['gram_archive']) for b in built],factor_archive_hashes=[G.digest(b['factor_archive']) for b in built],divisor_archive_hashes=[G.digest(b['divisor_archive']) for b in built],cell_archive_hashes=[G.digest(b['cell_archive']) for b in built],dictionary_sha256=built[0]['dictionary_sha256'],gram_specs=B.gram_specs())
    if 'case_hashes' in record:
        for key,value in expected.items():
            if record.get(key)!=value:raise ValueError('complete source/target archive '+key)
    elif record['status'] in ['exact_separator','finite_PSD_certificate']:raise ValueError('admitted result complete metadata')
    result=record.get('synthesis',{});status=record['status']
    if status=='exact_separator':
        if phase!='dual' or result.get('status')!=status:raise ValueError('dual-only separator')
        proof=verify_compressed_dual(instances,blocks,B.gram_specs(),result)
    elif status=='finite_PSD_certificate':
        if phase=='dual' or result.get('status')!=status:raise ValueError('primal-only finite certificate')
        proof=G.verify_primal(instances,blocks,B.gram_specs(),result)
    elif status in ['uncertified','missing_resource','rejected','no_certificate_found']:
        if result.get('certified') is True or 'certificates' in result:raise ValueError('failure cannot retain certified certificate')
        proof=dict(verified=True,admitted=False,**FLAGS)
    else:raise ValueError('explicit exact or nonadmitted status')
    return dict(proof=proof,instances=instances,blocks=blocks)

def verify_runtime(execution,expected_jobs):
    cost=execution['cost'];contract=dict(workers=1,requested_workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False)
    for key,value in contract.items():
        if type(cost.get(key))is not type(value) or cost[key]!=value:raise ValueError('executed resource contract '+key)
    if len(execution['results'])!=expected_jobs:raise ValueError('all ordered jobs')
    for j,row in enumerate(execution['results']):
        if row['index']!=j or row['status'] not in ['available','missing_resource','error']:raise ValueError('ordered process statuses')
    return True

TESTS=['test_check_cancellation_complete_gram_program','test_cancellation_shared_gram_dual_v2','test_cancellation_shared_gram_synthesis_v2','test_check_cancellation_shared_gram','test_run_complete_gram_search','test_check_complete_gram_search']
LIMITS=dict(OLD.LIMITS)
SOLVER_LIMITS=dict(OLD.SOLVER_LIMITS)
DUAL_LIMITS=dict(OLD.DUAL_LIMITS,max_preprocessing_operations=200000000,max_preprocessing_cells=4000000,max_checkpoint_bytes=8388608)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=600,max_jobs=8,max_result_bytes=65536)

def source_names():
    pending=['run_complete_gram_search','check_complete_gram_search',*TESTS];seen=set()
    while pending:
        name=pending.pop();path=ROOT/(name+'.py')
        if name in seen or not path.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)

def audit(directory):
    d=Path(directory).resolve();target=d/'independent_verification.json'
    if target.exists():raise FileExistsError('exclusive independent search review')
    read=OLD.I.read;sha=OLD.I.sha;protocol=read(d/'protocol.json');source=read(d/'source_seal.json');seal=read(d/'seal.json')
    if set(source)!=set(source_names()):raise ValueError('complete executed source closure')
    for name,h in source.items():
        if sha(ROOT/name)!=h or sha(d/'frozen_source'/name)!=h:raise ValueError('frozen source '+name)
    for name in ['protocol','source_seal','input']:
        if seal[name+'_sha256']!=sha(d/(name+'.json')):raise ValueError('sealed preregistration '+name)
    inputs=read(d/'input.json')['input_sha256'];expected_inputs={'cancellation-arithmetic-results/publication-006/'+n for n in ['manifest.json','report.json']}|{'cancellation-arithmetic-results/complete-gram-moment-probe-002/'+n for n in ['protocol.json','result.json','receipt.json','independent_verification.json']}
    if set(inputs)!=expected_inputs:raise ValueError('complete prior input binding')
    for name,h in inputs.items():
        if sha(ROOT/name)!=h:raise ValueError('prior input '+name)
    for name,h in read(ROOT/'cancellation-arithmetic-results/publication-006/manifest.json')['files'].items():
        if sha(ROOT/name)!=h:raise ValueError('immutable publication '+name)
    probe_dir=ROOT/'cancellation-arithmetic-results/complete-gram-moment-probe-002';probe_review=read(probe_dir/'independent_verification.json');probe=read(probe_dir/'result.json')
    if probe_review.get('all_passed')is not True or probe['status']!='complete':raise ValueError('admitted complete diagnostic required')
    for name,h in probe_review['input_sha256'].items():
        if sha(probe_dir/name)!=h:raise ValueError('diagnostic admission '+name)
    states=[r['status'] for r in probe['probe']['regions'].values()]
    if len(states)!=2 or all(s=='PSD_extension' for s in states) or any(s not in ['PSD_extension','witness_invalid_for_complete_cone','unknown_missing_coordinates'] for s in states):raise ValueError('preregistered diagnostic search trigger')
    expected=dict(schema=1,program=PROGRAM,training_scales=[1,2,3,5],final_scales=[8,13],language=B.SPEC,gram_specs=B.gram_specs(),gram_groups=B.group_descriptors(),dictionary=B.B.B.C.descriptors(),limits=LIMITS,solver_limits=SOLVER_LIMITS,dual_limits=DUAL_LIMITS,parallel=PARALLEL,tests=TESTS,final_refit=False,no_actual_signed_response_inputs=True,strategy='exact dual pruning first; otherwise primal; only admitted primal transfers')
    for key,value in expected.items():
        if protocol.get(key)!=value:raise ValueError('known signed-only protocol '+key)
    if read(d/'tests.json')['returncode']!=0:raise ValueError('pre-score tests pass')
    receipt=read(d/'receipt.json');files={str(p.relative_to(d)) for p in d.rglob('*.json')}-{'receipt.json'}
    if set(receipt['files_sha256'])!=files:raise ValueError('complete terminal JSON receipt')
    for name,h in receipt['files_sha256'].items():
        if sha(d/name)!=h:raise ValueError('terminal artifact '+name)
    checks=[];checkpoint_checks=[]
    def execution(phase,count):
        e=read(d/(phase+'_execution.json'));verify_runtime(e,count);records=[]
        for j,row in enumerate(e['results']):
            path=d/f'jobs/{phase}-{j:03d}.json'
            if row['status']!='available':
                if 'value' in row:raise ValueError('process failure no invented result')
                saved=d/f'jobs/{phase}-{j:03d}-proposal.json'
                if saved.exists():
                    if phase=='final':raise ValueError('no transfer proposal')
                    built=[B.build(PROGRAM,X) for X in [1,2,3,5]];aux=B.auxiliary();instances=[b['instance'] for b in built]+[aux['instance']];blocks=[b['gram_blocks'] for b in built]+[aux['gram_blocks']]
                    if phase=='dual':verify_dual_checkpoint(read(saved),instances,blocks,B.gram_specs())
                    else:OLD.verify_checkpoint(read(saved),instances,blocks,B.gram_specs())
                    checkpoint_checks.append(str(saved.relative_to(d)))
                records.append(None);continue
            v=row['value']
            if v['file']!=str(path.relative_to(d)) or v['sha256']!=sha(path):raise ValueError('ordered isolated job hash')
            record=read(path)
            if record['index']!=j or record['status']!=v['status'] or record['cost']!=v['cost']:raise ValueError('job status/cost binding')
            scales=[[8],[13]][j] if phase=='final' else [1,2,3,5];checked=verify_record(record,phase,scales);checks.append(dict(file=v['file'],proof=checked['proof']));records.append(record)
            saved=d/f'jobs/{phase}-{j:03d}-proposal.json'
            if saved.exists():
                if record.get('proposal_checkpoint')!=dict(file=str(saved.relative_to(d)),sha256=sha(saved)):raise ValueError('persisted numerical checkpoint binding')
                checkpoint=read(saved)
                if phase=='dual':verify_dual_checkpoint(checkpoint,checked['instances'],checked['blocks'],B.gram_specs())
                elif phase=='primal':OLD.verify_checkpoint(checkpoint,checked['instances'],checked['blocks'],B.gram_specs())
                else:raise ValueError('transfer must not fit numerical proposal')
                checkpoint_checks.append(str(saved.relative_to(d)))
                returned=record.get('synthesis',{}).get('proposal_checkpoint')
                if returned is not None:
                    keys=set(returned)&set(checkpoint)-{'phase','native_status','native_reason','native_diagnostics','independently_verified','reconstruction_attempts','failure'}
                    if any(returned[k]!=checkpoint[k] for k in keys):raise ValueError('same saved numerical proposal')
                if phase=='dual' and record['status']=='exact_separator' and checkpoint['support']!=record['synthesis']['saved_support']:raise ValueError('same checkpoint exact support')
            elif 'proposal_checkpoint' in record or record.get('synthesis',{}).get('proposal_checkpoint')is not None:raise ValueError('no lost checkpoint')
        return e,records
    decision=read(d/'decision.json');de,dr=execution('dual',1);dual_status=dr[0]['status'] if dr[0] else de['results'][0]['status']
    want=dict(dual_status=dual_status,run_primal=dual_status!='exact_separator',final_scales=[])
    if want['run_primal']:
        pe,pr=execution('primal',1);status=pr[0]['status'] if pr[0] else pe['results'][0]['status'];want['primal_status']=status
        if status=='finite_PSD_certificate':
            v=pe['results'][0]['value'];candidate=dict(attempt_file=v['file'],attempt_sha256=v['sha256'],final_scales=[8,13])
            if read(d/'candidate.json')!=candidate:raise ValueError('sealed admitted primal candidate')
            fe,fr=execution('final',2);want['final_scales']=[8,13]
            for r in fr:
                if r and r['status']=='finite_PSD_certificate':verify_fixed_transfer(pr[0],r)
        elif (d/'candidate.json').exists() or (d/'final_execution.json').exists():raise ValueError('nonadmitted primal cannot transfer')
    elif any((d/n).exists() for n in ['primal_execution.json','candidate.json','final_execution.json']):raise ValueError('exact dual prunes remaining search')
    if decision!=want:raise ValueError('deterministic stage decisions')
    review=dict(all_passed=True,checks=checks,checkpoint_checks=checkpoint_checks,decision=decision,input_sha256={n:sha(d/n) for n in ['protocol.json','source_seal.json','input.json','seal.json','tests.json','decision.json','receipt.json']},**FLAGS)
    with target.open('x') as stream:json.dump(review,stream,sort_keys=True,indent=2);stream.write('\n')
    return review

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('directory');args=parser.parse_args();print(json.dumps(dict(all_passed=audit(args.directory)['all_passed']),sort_keys=True))

"""Independent complete affine-storage search, checkpoint and stage audit."""
import ast
import json
import math
from pathlib import Path
from fractions import Fraction as F
import check_cancellation_affine_storage as B
import check_cancellation_shared_gram as G
import check_joint_gram_compressed_replay as C
import check_joint_gram_search as OLD
import check_cancellation_divisor_cells as DICTIONARY
import check_native_exact_support_leaf as LEAF
ROOT=Path(__file__).resolve().parent
FLAGS=dict(global_bound_proved=False,RH_proved=False)
PROGRAM=dict(target='mu',q=6,C=32,claim='critical',constraint='zero_cubic',dictionary_mode='extended',allow_constant_slack=True)

def prepared(instances,blocks,storage,specs):
    system=B.coefficient_system(instances,blocks,storage,specs)
    def flat(poly):return {(k,)+m:q for (k,m),q in poly.items()}
    columns=list(map(flat,system['columns']));lhs=flat(system['lhs'])
    domain=[(k,)+m for k,m in system['domain']];offset=system['offset'];ns,nr,_=system['shape']
    layout=[dict(index=i,kind='scalar') for i in range(offset)]
    nn=list(range(ns))+list(range(ns+2*nr,offset));rr=list(range(ns,ns+2*nr));positions={}
    for group,n in sorted(specs.items()):
        for i in range(n):
            for j in range(i,n):
                pos=len(layout);positions[group,i,j]=pos
                layout.append(dict(index=pos,kind='Gram',group=group,i=i,j=j))
                (nn if i==j else rr).append(pos)
    removed=[];proof=[]
    for i in range(15):
        for j in range(i+1,15):
            kc=positions['storage_K',i,j];cc=positions['full_child',i,j];pc=positions['full_parent',i,j]
            combined=dict(columns[cc])
            for m,q in columns[pc].items():combined[m]=combined.get(m,F(0))-4*q
            combined={m:q for m,q in combined.items() if q}
            if combined!=columns[kc] or any(pos not in rr for pos in [kc,cc,pc]):raise ValueError('exact restricted cross redundancy')
            removed.append(kc)
            proof.append(dict(storage_column=kc,child_column=cc,parent_column=pc,child_multiplier='1',parent_multiplier='-4',exact_polynomial_hash=G.digest([[list(m),str(q)] for m,q in sorted(combined.items())])))
    keep=[i for i in range(len(columns)) if i not in set(removed)];lookup={old:new for new,old in enumerate(keep)}
    rn=[lookup[i] for i in nn];rrr=[lookup[i] for i in rr if i in lookup]
    pairs=sum(len(row[i])*len(row[j]) for groups in blocks for rows in groups.values() for row in rows for i in range(15) for j in range(i,15))
    compilation=len(json.dumps(instances,sort_keys=True,separators=(',',':')).encode())+8*pairs+8*sum(map(len,columns))+1
    return dict(columns=columns,lhs=lhs,domain=domain,shape=[ns,nr],offset=offset,layout=layout,
                nn=nn,rr=rr,restricted=[columns[i] for i in keep],rn=rn,rrr=rrr,keep=keep,
                redundancy=proof,compilation=compilation)


def checkpoint_common(checkpoint,instances,blocks,storage,specs,schema):
    if checkpoint.get('schema')!=schema or checkpoint.get('proposal_only')is not True or checkpoint.get('certified')is not False:raise ValueError('proposal-only anchored checkpoint')
    if len(json.dumps(checkpoint,sort_keys=True,separators=(',',':'),allow_nan=False).encode())>8388608:raise ValueError('8MiB checkpoint')
    d=prepared(instances,blocks,storage,specs)
    expected=dict(source_hashes=list(map(G.digest,instances)),gram_block_hashes=list(map(G.digest,blocks)),storage_block_hashes=list(map(G.digest,storage)),gram_specs=specs,grammar_hash=G.digest(B.SPEC),monomials=[dict(instance=m[0],m=list(m[1:])) for m in d['domain']],scalar_shape=d['shape'],scalar_offset=d['offset'],column_layout=d['layout'],layout_hash=G.digest(d['layout']),exact_columns_hash=G.digest([[[list(m),str(q)] for m,q in sorted(p.items())] for p in d['columns']]),exact_target_hash=G.digest([[list(m),str(q)] for m,q in sorted(d['lhs'].items())]))
    expected['row_order_hash']=G.digest(expected['monomials'])
    for key,value in expected.items():
        if checkpoint.get(key)!=value:raise ValueError('complete anchored checkpoint binding '+key)
    if any(checkpoint.get(k)is not False for k in FLAGS):raise ValueError('finite checkpoint scope')
    return d


def verify_dual_checkpoint(checkpoint,instances,blocks,storage,specs):
    d=checkpoint_common(checkpoint,instances,blocks,storage,specs,'affine-storage-dual-proposal-v1')
    expected=dict(nonnegative_indices=d['nn'],relation_indices=d['rr'],restricted_column_indices=d['keep'],restricted_exact_columns_hash=G.digest([[[list(m),str(q)] for m,q in sorted(p.items())] for p in d['restricted']]),storage_cross_redundancy=d['redundancy'],restricted_nonnegative_indices=d['rn'],restricted_relation_indices=d['rrr'],dual_equation_order=[d['keep'][i] for i in d['rrr']+d['rn']],dual_variable_order='positive monomial coordinates; negative monomial coordinates; nonnegative column slacks',numerical_options=dict(solver='HiGHS',threads=1,parallel=False,support_threshold='1e-8'),refitted=False,compilation_work_reserve=d['compilation']+sum(map(len,d['columns']))+1)
    for key,value in expected.items():
        if checkpoint.get(key)!=value:raise ValueError('restricted checkpoint binding '+key)
    if checkpoint.get('phase') not in ['prepared_domain','LP_proposal','native_reconstruction','independent_admission']:raise ValueError('checkpoint phase')
    support=checkpoint['support'];variables=2*len(d['domain'])+len(d['rn'])
    if support is not None and (type(support)is not list or any(type(i)is not int or not 0<=i<variables for i in support) or len(support)!=len(set(support))):raise ValueError('saved support domain')
    limits=dict(time_limit=360,max_work=450000000,max_cells=4000000,max_preprocessing_operations=200000000,max_preprocessing_cells=4000000,max_rows=2500,max_variables=60000,max_denominator=2**4096,max_coefficient_bits=4096)
    if checkpoint['limits']!=limits:raise ValueError('frozen dual limits')
    native=verify_leaf_checkpoint(checkpoint,d)
    return dict(verified=True,complete_exact_domain_and_columns_verified=True,redundant_cross_equations_verified=True,native_checkpoint=native,proposal_only=True)


def verify_leaf_checkpoint(checkpoint,d):
    logs=checkpoint.get('native_receipts')
    if type(logs)is not list or len(logs)>4:raise ValueError('bounded leaf checkpoint stages')
    emitted=[r for r in logs if r.get('origin')=='callback']
    terminal=[r for r in logs if r.get('origin')=='terminal_return']
    stages=[r.get('status') for r in emitted]
    allowed=[[],['prepared_remaining_system']]
    for middle in ['remaining_native_completed','remaining_native_failure']:
        allowed.append(['prepared_remaining_system',middle])
        for final in ['full_original_equality_verified','remaining_system_inconsistent']:
            allowed.append(['prepared_remaining_system',middle,final])
    if len(emitted)+len(terminal)!=len(logs) or len(terminal)>1 or logs!=emitted+terminal or stages not in allowed:raise ValueError('ordered complete leaf checkpoint stages')
    receipt=checkpoint.get('native_receipt')
    if receipt is None:
        if logs:raise ValueError('no lost emitted leaf receipt')
        return dict(verified=True,emitted_stages=0,exact_reconstruction_proved=False)
    if not logs:raise ValueError('retained native receipt requires emission log')
    expected=dict(origin=logs[-1]['origin'],status=receipt['status'],receipt_sha256=G.digest(receipt),total_work_proxy=receipt.get('total_work_proxy'),preprocessing_actual_work=receipt.get('preprocessing_actual_work'))
    if logs[-1]!=expected:raise ValueError('last emitted complete leaf receipt binding')
    columns,lhs,domain,nn,rr=d['restricted'],d['lhs'],d['domain'],d['rn'],d['rrr']
    support=checkpoint['support']
    if support is None:raise ValueError('leaf reconstruction requires saved LP support')
    equations,target=C.dual_equations(columns,lhs,domain,nn,rr)
    variables=2*len(domain)+len(nn);build=(len(columns)+1)*variables
    verification=3*sum(map(len,columns))+2*len(lhs)+variables+2*len(domain)+len(support)+1
    reserve=d['compilation']+sum(map(len,d['columns']))+1
    for key,value in dict(dual_build_work_proxy=build,dual_verification_work_reserve=verification,compilation_work_reserve=reserve).items():
        if receipt.get(key)!=value:raise ValueError('emitted leaf wrapper reserves '+key)
    checked=None
    if receipt.get('status')=='preprocessing' and terminal and not emitted:
        if checkpoint.get('native_status') not in ['missing_resource','uncertified']:raise ValueError('incomplete preprocessing is never admitted')
    else:
        checked=LEAF.verify_leaf_preprocessing(equations,target,support,receipt,max_rows=2500,max_columns=60000,
            max_work=450000000-reserve-build-verification,max_cells=4000000,max_preprocessing_cells=4000000,max_preprocessing_operations=200000000,max_coefficient_bits=4096)
    diagnostic=checkpoint.get('native_diagnostics')
    if diagnostic is not None and ('leaf_elimination' in diagnostic or diagnostic.get('leaf_receipt_sha256')!=G.digest(receipt)):
        raise ValueError('deduplicated retained leaf receipt binding')
    return dict(verified=True,emitted_stages=len(emitted),terminal_partial_retained=bool(terminal),retained_preprocessing=checked,
                earlier_stage_hashes_recorded_not_replayed=True,exact_reconstruction_proved=False)


def verify_primal_checkpoint(checkpoint,instances,blocks,storage,specs):
    d=checkpoint_common(checkpoint,instances,blocks,storage,specs,'affine-storage-SDP-proposal-v1')
    vector=checkpoint['float_vector'];offset=d['offset'];columns=d['columns']
    if type(vector)is not list or len(vector)!=len(columns) or any(type(v)not in(int,float) or not math.isfinite(v) for v in vector):raise ValueError('finite complete SDP vector')
    if checkpoint['active_threshold']!=1e-7 or checkpoint['active_support']!=[i for i in range(offset) if vector[i]>1e-7]+list(range(offset,len(columns))):raise ValueError('complete saved active face')
    if checkpoint['numerical_options']!=dict(solver='CLARABEL',max_threads=1,row_normalization=True):raise ValueError('known numerical options')
    if checkpoint['float_objective']is not None and (type(checkpoint['float_objective'])not in(int,float) or not math.isfinite(checkpoint['float_objective'])):raise ValueError('finite objective')
    limits=dict(max_exact_work=450000000,max_exact_cells=4000000,max_denominator=1000000,max_coefficient_bits=4096,max_operations=200000000,time_limit=360)
    if checkpoint['reconstruction_limits']!=limits or type(checkpoint['reconstruction_attempts'])is not list or checkpoint['compilation_work_reserve']!=d['compilation']:raise ValueError('frozen primal reconstruction contract')
    attempts=verify_primal_work_receipts(checkpoint,d)
    return dict(verified=True,complete_exact_domain_and_columns_verified=True,work_receipts=attempts,proposal_only=True)


def verify_primal_work_receipts(checkpoint,d):
    receipts=checkpoint['native_attempt_receipts'];vector=checkpoint['float_vector']
    if type(receipts)is not list or len(receipts)>3:raise ValueError('bounded exact correction attempts')
    charge=d['compilation'];columns=d['columns'];lhs=d['lhs'];support=checkpoint['active_support']
    permitted=[64,4096,1000000];replayed=[]
    for index,attempt in enumerate(receipts):
        if attempt['bound']!=permitted[index]:raise ValueError('ordered rational correction bounds')
        initial=[F(float(v)).limit_denominator(attempt['bound']) for v in vector]
        for j in range(d['offset']):
            if abs(vector[j])<1e-7:initial[j]=F(0)
        residual=dict(lhs)
        for p,w in zip(columns,initial):
            for m,q in p.items():residual[m]=residual.get(m,F(0))-w*q
        residual={m:q for m,q in residual.items() if q}
        assembly=8*sum(map(len,columns))+len(lhs)+len(initial)+1
        expected=dict(initial_hash=G.digest(list(map(str,initial))),residual_hash=G.digest([[list(m),str(q)] for m,q in sorted(residual.items())]),support_hash=G.digest(support),charge_before=charge,assembly_reserve=assembly,charge_before_native=charge+assembly,remaining_work=450000000-charge-assembly)
        for key,value in expected.items():
            if attempt.get(key)!=value:raise ValueError('replayed correction resource binding '+key)
        charge+=assembly;remaining=450000000-charge
        info=attempt.get('exact_diagnostics',{}).get('row_compression')
        if info is not None:
            # Replay a rejected request too, without claiming its native work ran.
            replay=C.verify_producer_compression(columns,residual,support,info,max_work=max(1,remaining,info['total_work_proxy']))
            if attempt['native_gate_rejected']:
                if attempt['native_returned'] or info['total_work_proxy']<=remaining or attempt.get('reason')!='compressed native plus preprocessing total work proxy':raise ValueError('native work rejection precedes execution')
                addition=info['preprocessing_work']
            else:
                if info['total_work_proxy']>remaining:raise ValueError('native correction within remaining work')
                addition=info['total_work_proxy']
            if attempt.get('native_charge')!=addition or attempt.get('charge_after')!=charge+addition:raise ValueError('cumulative native work receipt')
            charge+=addition;replayed.append(replay)
        elif attempt.get('native_returned'):
            raise ValueError('returned native correction requires compression receipt')
        elif index!=len(receipts)-1:
            raise ValueError('incomplete native attempt cannot precede another attempt')
        if not attempt.get('native_returned') and index!=len(receipts)-1:raise ValueError('failed native attempt stops reconstruction')
    return dict(attempts=len(receipts),compression_receipts_replayed=len(replayed),cumulative_charged_proxy=charge,all_returned=all(r.get('native_returned') for r in receipts))


def verify_leaf_dual(instances,blocks,storage,specs,result):
    full=B.verify_dual(instances,blocks,storage,specs,result)
    d=prepared(instances,blocks,storage,specs)
    columns,lhs,domain,nn,rr=d['restricted'],d['lhs'],d['domain'],d['rn'],d['rrr']
    if result['restricted_column_indices']!=d['keep'] or result['storage_cross_redundancy']!=d['redundancy']:raise ValueError('exact restricted transpose geometry')
    dots=result['columns_dot_y']+result['gram_columns_dot_y']
    if result['restricted_columns_dot_y']!=[dots[i] for i in d['keep']]:raise ValueError('full and reduced moments agree')
    eq,target=C.dual_equations(columns,lhs,domain,nn,rr);support=result['saved_support'];report=result['diagnostics']['leaf_elimination'];variables=2*len(domain)+len(nn)
    build=(len(columns)+1)*variables
    verification=3*sum(map(len,columns))+2*len(lhs)+variables+2*len(domain)+len(support)+1
    if report['dual_build_work_proxy']!=build or report['dual_verification_work_reserve']!=verification:raise ValueError('exact dual work accounting')
    reserve=d['compilation']+sum(map(len,d['columns']))+1
    total=report['leaf_total_work_proxy']+reserve+build+verification
    if report['compilation_work_reserve']!=reserve or report['total_work_proxy']!=total or total>450000000:raise ValueError('total compilation and native work gate')
    leaf=LEAF.verify_leaf_solution(eq,target,support,result['exact_support_weights'],report,
        require_nonnegative=True,max_work=450000000-reserve-build-verification,
        max_cells=4000000,max_preprocessing_operations=200000000,max_preprocessing_cells=4000000,max_coefficient_bits=4096)
    v=[F(0)]*variables
    for i,q in zip(support,result['exact_support_weights']):v[i]=F(q)
    if [v[i]-v[i+len(domain)] for i in range(len(domain))]!=list(map(F,result['weights'])):raise ValueError('same reconstructed support moments')
    return dict(verified=True,full_Gram_dual=full,leaf_elimination=leaf,all_original_equations_verified=True,redundant_cross_equations_verified=True,total_work_proxy=total,**FLAGS)

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
    built=[B.build(PROGRAM,X) for X in scales];ordinary=[b['instance'] for b in built];instances=list(ordinary);blocks=[b['gram_blocks'] for b in built];storage=[b['storage_blocks'] for b in built]
    if phase in ['dual','train','primal']:
        aux=B.auxiliary();instances.append(aux['instance']);blocks.append(aux['gram_blocks']);storage.append(aux['storage_blocks'])
    expected=dict(ordinary_case_hashes=list(map(G.digest,ordinary)),case_hashes=list(map(G.digest,instances)),gram_block_hashes=list(map(G.digest,blocks)),storage_block_hashes=list(map(G.digest,storage)),gram_archive_hashes=[G.digest(b['gram_archive']) for b in built],factor_archive_hashes=[G.digest(b['factor_archive']) for b in built],divisor_archive_hashes=[G.digest(b['divisor_archive']) for b in built],cell_archive_hashes=[G.digest(b['cell_archive']) for b in built],dictionary_sha256=built[0]['dictionary_sha256'],gram_specs=B.gram_specs())
    if 'case_hashes' in record:
        for key,value in expected.items():
            if record.get(key)!=value:raise ValueError('complete source/target archive '+key)
    elif record['status'] in ['exact_separator','finite_PSD_certificate']:raise ValueError('admitted result complete metadata')
    result=record.get('synthesis',{});status=record['status']
    if status=='exact_separator':
        if phase!='dual' or result.get('status')!=status:raise ValueError('dual-only separator')
        proof=verify_leaf_dual(instances,blocks,storage,B.gram_specs(),result)
    elif status=='finite_PSD_certificate':
        if phase=='dual' or result.get('status')!=status:raise ValueError('primal-only finite certificate')
        proof=B.verify_primal(instances,blocks,storage,B.gram_specs(),result)
        if phase=='primal':
            resource=verify_primal_checkpoint(result['proposal_checkpoint'],instances,blocks,storage,B.gram_specs())['work_receipts']
            if not resource['all_returned'] or resource['attempts']<1 or resource['cumulative_charged_proxy']>450000000:raise ValueError('admitted primal cumulative work')
            if result['diagnostics']['native_attempt_receipts']!=result['proposal_checkpoint']['native_attempt_receipts'] or result['diagnostics']['total_charged_work_proxy']!=resource['cumulative_charged_proxy']:raise ValueError('same cumulative primal receipts')
            proof['reconstruction_resources']=resource
    elif status in ['uncertified','missing_resource','rejected','no_certificate_found']:
        if result.get('certified') is True or 'certificates' in result:raise ValueError('failure cannot retain certified certificate')
        proof=dict(verified=True,admitted=False,**FLAGS)
    else:raise ValueError('explicit exact or nonadmitted status')
    return dict(proof=proof,instances=instances,blocks=blocks,storage=storage)

def verify_runtime(execution,expected_jobs):
    cost=execution['cost'];contract=dict(workers=1,requested_workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False)
    for key,value in contract.items():
        if type(cost.get(key))is not type(value) or cost[key]!=value:raise ValueError('executed resource contract '+key)
    if len(execution['results'])!=expected_jobs:raise ValueError('all ordered jobs')
    for j,row in enumerate(execution['results']):
        if row['index']!=j or row['status'] not in ['available','missing_resource','error']:raise ValueError('ordered process statuses')
    return True

TESTS=['test_check_cancellation_complete_gram_program','test_cancellation_affine_storage','test_cancellation_affine_storage_synthesis','test_cancellation_affine_storage_dual','test_check_cancellation_affine_storage','test_run_affine_storage_search','test_check_affine_storage_search']
LIMITS=dict(OLD.LIMITS,time_limit=360)
SOLVER_LIMITS=dict(OLD.SOLVER_LIMITS,time_limit=360)
DUAL_LIMITS=dict(OLD.DUAL_LIMITS,time_limit=360,max_preprocessing_operations=200000000,max_preprocessing_cells=4000000,max_checkpoint_bytes=8388608)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=1200,max_jobs=8,max_result_bytes=65536)

def source_names():
    pending=['run_affine_storage_search','check_affine_storage_search',*TESTS];seen=set()
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
    inputs=read(d/'input.json')['input_sha256'];expected_inputs={'cancellation-arithmetic-results/publication-008/'+n for n in ['manifest.json','report.json']}|{'cancellation-arithmetic-results/affine-storage-moment-probe-001/'+n for n in ['protocol.json','result.json','receipt.json','independent_verification.json','source_seal.json']}|{'affine_storage_uniform_scope.txt','anchored_storage_resource_authorization.txt'}
    if set(inputs)!=expected_inputs:raise ValueError('complete prior input binding')
    for name,h in inputs.items():
        if sha(ROOT/name)!=h:raise ValueError('prior input '+name)
    for name,h in read(ROOT/'cancellation-arithmetic-results/publication-008/manifest.json')['files'].items():
        if sha(ROOT/name)!=h:raise ValueError('immutable publication '+name)
    probe_dir=ROOT/'cancellation-arithmetic-results/affine-storage-moment-probe-001';probe_review=read(probe_dir/'independent_verification.json');probe=read(probe_dir/'result.json')
    if probe_review.get('all_passed')is not True or probe['status']!='witness_invalid_for_affine_cone' or probe_review['result_status']!=probe['status'] or probe_review['proof']['verified']is not True:raise ValueError('exact affine diagnostic required')
    for name,h in probe_review['input_sha256'].items():
        if sha(probe_dir/name)!=h:raise ValueError('diagnostic admission '+name)
    for name,h in read(probe_dir/'receipt.json')['files_sha256'].items():
        if sha(probe_dir/name)!=h:raise ValueError('complete diagnostic artifact '+name)
    for name,h in read(probe_dir/'source_seal.json').items():
        if sha(ROOT/name)!=h or sha(probe_dir/'frozen_source'/name)!=h:raise ValueError('frozen diagnostic source '+name)
    expected=dict(schema=1,program=PROGRAM,training_scales=[1,2,3,5],final_scales=[8,13],language=B.SPEC,gram_specs=B.gram_specs(),storage_operator=B.SPEC,dictionary=DICTIONARY.descriptors(),limits=LIMITS,solver_limits=SOLVER_LIMITS,dual_limits=DUAL_LIMITS,parallel=PARALLEL,tests=TESTS,final_refit=False,no_actual_signed_response_inputs=True,strategy='exact affine storage-cone dual pruning first; otherwise primal; only admitted fixed full15 primal transfers',affine_completion='prepend unit to every full14 regional/storage vector; keep all 120 pairs per matrix')
    for key,value in expected.items():
        if protocol.get(key)!=value:raise ValueError('known signed-only protocol '+key)
    if read(d/'tests.json')['returncode']!=0:raise ValueError('pre-score tests pass')
    if read(d/'run_started.json')!=dict(protocol_sha256=sha(d/'protocol.json')):raise ValueError('exclusive preregistered execution')
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
                    built=[B.build(PROGRAM,X) for X in [1,2,3,5]];aux=B.auxiliary();instances=[b['instance'] for b in built]+[aux['instance']];blocks=[b['gram_blocks'] for b in built]+[aux['gram_blocks']];storage=[b['storage_blocks'] for b in built]+[aux['storage_blocks']]
                    if phase=='dual':verify_dual_checkpoint(read(saved),instances,blocks,storage,B.gram_specs())
                    else:verify_primal_checkpoint(read(saved),instances,blocks,storage,B.gram_specs())
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
                if phase=='dual':verify_dual_checkpoint(checkpoint,checked['instances'],checked['blocks'],checked['storage'],B.gram_specs())
                elif phase=='primal':verify_primal_checkpoint(checkpoint,checked['instances'],checked['blocks'],checked['storage'],B.gram_specs())
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

"""Independent full-cone and resource audit of the unchanged 703-support replay."""
import ast
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import check_anchored_storage_search as S
import check_native_exact_support_leaf as L
import check_joint_gram_compressed_replay as C

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'cancellation-arithmetic-results/anchored-storage-search-001'
FLAGS=dict(global_bound_proved=False,RH_proved=False)
LIMITS=dict(time_limit=360,max_rows=2500,max_variables=60000,max_work=450000000,
 max_cells=4000000,max_preprocessing_operations=200000000,max_preprocessing_cells=4000000,max_denominator=2**4096,max_coefficient_bits=4096,max_receipt_bytes=8388608)
PREPARE_LIMITS=dict(max_columns=2048,max_monomials=100000,max_operations=200000000,
 max_coefficient_bits=4096,max_horizon=80,max_degree=12)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,
 timeout_seconds=1200,max_jobs=1,max_result_bytes=65536)
TESTS=['test_anchored_storage_leaf_replay','test_check_anchored_storage_leaf_replay','test_native_exact_support_leaf','test_check_native_exact_support_leaf']

def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def bind(base,hashes):
    for name,h in hashes.items():
        if sha(base/name)!=h:raise ValueError('replay evidence binding '+str(base/name))

def source_names():
    pending=['run_anchored_storage_leaf_replay','check_anchored_storage_leaf_replay',*TESTS];seen=set()
    while pending:
        name=pending.pop();path=ROOT/(name+'.py')
        if name in seen or not path.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)

def verify_leaf_dual(instances,blocks,storage,specs,result,support):
    full=S.B.verify_dual(instances,blocks,storage,specs,result)
    d=S.prepared(instances,blocks,storage,specs)
    if result['saved_support']!=support or result['saved_support_sha256']!=S.G.digest(support):raise ValueError('unchanged saved support')
    if result['restricted_column_indices']!=d['keep'] or result['storage_cross_redundancy']!=d['redundancy']:raise ValueError('same exact full/restricted geometry')
    dots=result['columns_dot_y']+result['gram_columns_dot_y']
    if result['restricted_columns_dot_y']!=[dots[i] for i in d['keep']]:raise ValueError('complete dual dot transport')
    columns,lhs,domain,nn,rr=d['restricted'],d['lhs'],d['domain'],d['rn'],d['rrr']
    equations,target=C.dual_equations(columns,lhs,domain,nn,rr)
    variables=2*len(domain)+len(nn)
    build=(len(columns)+1)*variables
    verification=3*sum(map(len,columns))+2*len(lhs)+variables+2*len(domain)+len(support)+1
    compilation=d['compilation']+sum(map(len,d['columns']))+1
    diagnostic=result['diagnostics'];leaf=diagnostic['leaf_elimination']
    for name,value in dict(dual_build_work_proxy=build,dual_verification_work_reserve=verification,compilation_work_reserve=compilation).items():
        if leaf.get(name)!=value:raise ValueError('wrapper work accounting '+name)
    check=L.verify_leaf_solution(equations,target,support,result['exact_support_weights'],leaf,
        require_nonnegative=True,max_work=450000000-build-verification-compilation,
        max_cells=4000000,max_preprocessing_operations=200000000,max_preprocessing_cells=4000000,
        max_coefficient_bits=4096)
    total=leaf['leaf_total_work_proxy']+build+verification+compilation
    if leaf['total_work_proxy']!=total or total>450000000:raise ValueError('unchanged total450m work gate')
    answer=list(map(F,result['exact_support_weights']));v=[F(0)]*variables
    for i,q in zip(support,answer):v[i]=q
    if [v[i]-v[i+len(domain)] for i in range(len(domain))]!=list(map(F,result['weights'])):raise ValueError('full703 variable reconstruction gives admitted moments')
    return dict(verified=True,leaf_elimination=check,full_Gram_dual=full,
                same_support_verified=True,total_work_proxy=total,**FLAGS)

def audit(directory):
    d=Path(directory).resolve();out=d/'independent_verification.json'
    if out.exists():raise FileExistsError('exclusive independent replay audit')
    source=read(d/'source_seal.json')
    if set(source)!=set(source_names()):raise ValueError('complete replay source closure')
    bind(ROOT,source);bind(d/'frozen_source',source)
    for n in ['protocol','source_seal','input','support']:
        if read(d/'seal.json')[n+'_sha256']!=sha(d/(n+'.json')):raise ValueError('frozen replay '+n)
    inputs=read(d/'input.json')['input_sha256']
    names=['jobs/dual-000.json','jobs/dual-000-proposal.json','protocol.json','source_seal.json','receipt.json','independent_verification.json']
    if set(inputs)!=({str((PARENT/n).relative_to(ROOT)) for n in names}|{'anchored_storage_resource_authorization.txt'}):raise ValueError('all original inputs and new runtime authorization')
    bind(ROOT,inputs)
    original_review=read(PARENT/'independent_verification.json')
    if original_review['all_passed']is not True:raise ValueError('original independently admitted failure')
    bind(PARENT,original_review['input_sha256']);bind(PARENT,read(PARENT/'receipt.json')['files_sha256'])
    bind(ROOT,read(PARENT/'source_seal.json'));bind(PARENT/'frozen_source',read(PARENT/'source_seal.json'))
    original=read(PARENT/'jobs/dual-000.json');checkpoint=read(PARENT/'jobs/dual-000-proposal.json')
    if original['status']!='missing_resource' or original['synthesis']['reason']!='total charged anchored reconstruction work cap':raise ValueError('original resource failure retained')
    saved=read(d/'support.json')
    if saved!=dict(indices=checkpoint['support'],original_dual_sha256=sha(PARENT/'jobs/dual-000.json'),proposal_sha256=sha(PARENT/'jobs/dual-000-proposal.json')) or len(saved['indices'])!=703:raise ValueError('same703 full support')
    protocol=read(d/'protocol.json')
    expected=dict(program=S.PROGRAM,scales=[1,2,3,5],gram_specs=S.B.gram_specs(),limits=LIMITS,prepare_limits=PREPARE_LIMITS,parallel=PARALLEL,support_count=703,tests=TESTS,no_new_float_search=True,same_cone=True,**FLAGS)
    for key,value in expected.items():
        if protocol.get(key)!=value:raise ValueError('known same-cone replay '+key)
    if read(d/'tests.json')['returncode']!=0:raise ValueError('frozen prescore calibrations')
    receipt=read(d/'receipt.json');actual={str(p.relative_to(d)):sha(p) for p in d.rglob('*.json') if p.name!='receipt.json'}
    if receipt['files_sha256']!=actual or receipt['source_count']!=len(source):raise ValueError('complete terminal archive')
    execution=read(d/'execution.json');S.verify_runtime(execution,1);row=execution['results'][0]
    result_status=row['status'];proof=None
    if row['status']=='available':
        value=row['value']
        if value['file']!='result.json' or value['sha256']!=sha(d/'result.json'):raise ValueError('isolated replay result')
        r=read(d/'result.json');result_status=r['status']
        if r['status']!=value['status'] or r['cost']!=value['cost'] or r['program']!=S.PROGRAM or r['scales']!=[1,2,3,5] or r['same_cone']is not True or r['no_new_float_search']is not True:raise ValueError('actual fixed replay status')
        checked=S.verify_record(original,'dual',[1,2,3,5])
        instances,blocks,storage=checked['instances'],checked['blocks'],checked['storage']
        S.verify_dual_checkpoint(checkpoint,instances,blocks,storage,S.B.gram_specs())
        for key in ['case_hashes','gram_block_hashes','storage_block_hashes','gram_archive_hashes']:
            if r[key]!=original[key]:raise ValueError('unchanged complete source '+key)
        result=r['synthesis']
        saved_checkpoint=d/'leaf-checkpoint.json'
        if saved_checkpoint.exists():
            if r.get('leaf_checkpoint')!=dict(file='leaf-checkpoint.json',sha256=sha(saved_checkpoint)):raise ValueError('bounded saved elimination checkpoint')
            cp=read(saved_checkpoint)
            if len(json.dumps(cp,sort_keys=True,separators=(',',':')).encode())>8388608:raise ValueError('bounded elimination receipt')
            system=S.prepared(instances,blocks,storage,S.B.gram_specs())
            eq,target=C.dual_equations(system['restricted'],system['lhs'],system['domain'],system['rn'],system['rrr'])
            L.verify_leaf_preprocessing(eq,target,saved['indices'],cp,max_cells=4000000,max_preprocessing_cells=4000000,max_work=450000000)
            if result_status=='exact_separator' and cp!=result['diagnostics']['leaf_elimination']:raise ValueError('final admitted receipt equals saved checkpoint')
        elif result_status=='exact_separator' or 'leaf_checkpoint' in r:raise ValueError('no lost pre-native elimination checkpoint')
        if result_status=='exact_separator':proof=verify_leaf_dual(instances,blocks,storage,S.B.gram_specs(),result,saved['indices'])
        elif result_status not in ['missing_resource','uncertified'] or result.get('certified'):raise ValueError('no failure promotion')
    review=dict(all_passed=True,result_status=result_status,proof=proof,source_count=len(source),
        same_support_verified=True,no_new_floating_search=True,
        input_sha256={n:sha(d/n) for n in ['protocol.json','source_seal.json','input.json','support.json','seal.json','tests.json','execution.json','receipt.json']},**FLAGS)
    with out.open('x') as stream:json.dump(review,stream,sort_keys=True,indent=2);stream.write('\n')
    return review

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('directory');args=parser.parse_args()
    review=audit(args.directory);print(json.dumps(dict(all_passed=review['all_passed'],result_status=review['result_status'])))

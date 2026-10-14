"""Independent frozen-source, arithmetic-domain and full-column probe audit."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import check_cancellation_primitive_state_localizers as L
import check_primitive_state_localizer_probe as C

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
PARENT=BASE/'affine-storage-search-001'
PUBLICATION=BASE/'publication-009'
PARENT_RESULT='jobs/dual-000.json'
FLAGS=dict(global_bound_proved=False,RH_proved=False,larger_cone_feasibility_proved=False)
TESTS=['test_cancellation_primitive_state_localizers','test_check_cancellation_primitive_state_localizers','test_primitive_state_localizer_probe']
PROGRAM=dict(target='mu',q=6,C=32,claim='critical',constraint='zero_cubic',dictionary_mode='extended',allow_constant_slack=True)
SCALES=[1,2,3,5]
LIMITS=dict(max_horizon=80,max_operations=200000000,max_terms=100000,max_coefficient_bits=4096)
PARALLEL=dict(workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,timeout_seconds=1200,max_jobs=1,max_result_bytes=65536)
DIAGNOSTIC=dict(version='primitive-state-functional-probe-v1',selection='every declared relation-state column, in descriptor order',
    signed_relation_rule='exact zero pairing required',missing_policy='unknown after exact polynomial cancellation',
    no_new_floating_search=True,no_actual_signed_response_inputs=True)


def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def bind(base,hashes):
    for n,h in hashes.items():
        if sha(base/n)!=h:raise ValueError('bound primitive-state artifact '+str(base/n))


def source_names():
    pending=['run_primitive_state_localizer_probe','check_primitive_state_localizer_probe_run',*TESTS];seen=set()
    while pending:
        name=pending.pop();path=ROOT/(name+'.py')
        if name in seen or not path.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)


def compare_additions(given,expected):
    if type(given)is not dict or set(given)!=set(expected):raise ValueError('complete added-source schema')
    for key,value in expected.items():
        if key=='construction_operations':
            if type(given[key])is not int or not 0<=given[key]<=200000000:raise ValueError('bounded producer construction proxy')
        elif key=='archive':
            if len(given[key])!=210 or len(value)!=210:raise ValueError('all family-region-atom descriptors')
            for a,b in zip(given[key],value):
                if set(a)!=set(b):raise ValueError('complete source archive fields')
                for name,wanted in b.items():
                    if name=='polynomial_sha256' and a[name]is None:continue
                    if a[name]!=wanted:raise ValueError('independent primitive-state archive '+name)
        elif given[key]!=value:raise ValueError('all primitive/state sources '+key)


def geometry(source,prior):
    if source['scales']!=SCALES or source['horizons']!=[4*X-1 for X in SCALES]+[1] or source['descriptor_sha256']!=L.digest(L.additions()['relation']):
        raise ValueError('complete fixed grid and dictionary')
    if len(source['cases'])!=len(SCALES):raise ValueError('every declared source scale')
    blocks=[];archives=[];instances=[]
    for X,case in zip(SCALES,source['cases']):
        if set(case)!={'X','additions'} or case['X']!=X:raise ValueError('ordered source cases')
        base=L.B.build_blocks(X,**LIMITS)
        expected=L.build_additions(X,blocks=base['blocks'],**LIMITS)
        compare_additions(case['additions'],expected)
        blocks.append(base['blocks']);archives.append(base['archive'])
        instances.append(dict(target='mu',horizon=4*X-1,lhs=[],square_groups=[],relation_groups=expected['relation_groups']))
    blocks.append(dict(full_child=[],full_parent=[]))
    instances.append(dict(target='mu',horizon=1,lhs=[],square_groups=[],relation_groups=[[] for _ in range(210)]))
    metadata=dict(gram_block_hashes=list(map(L.digest,blocks)),gram_archive_hashes=list(map(L.digest,archives)))
    for key,value in metadata.items():
        if source[key]!=value or prior[key]!=value:raise ValueError('unchanged complete full15 source '+key)
    return instances


def audit(directory):
    d=Path(directory).resolve();out=d/'independent_verification.json'
    if out.exists():raise FileExistsError('exclusive independent arithmetic-closure audit')
    source=read(d/'source_seal.json')
    if set(source)!=set(source_names()):raise ValueError('complete frozen source closure')
    bind(ROOT,source);bind(d/'frozen_source',source)
    for n in ['protocol','source_seal','input','tests']:
        if read(d/'seal.json')[n+'_sha256']!=sha(d/(n+'.json')):raise ValueError('frozen preregistration '+n)
    paths=[PARENT/n for n in [PARENT_RESULT,'protocol.json','source_seal.json','receipt.json','independent_verification.json']]
    paths += [PUBLICATION/n for n in ['manifest.json','report.json']]
    paths += [ROOT/n for n in ['primitive_state_localizers_uniform_scope.txt','anchored_storage_resource_authorization.txt']]
    inputs=read(d/'input.json')['input_sha256']
    if set(inputs)!={str(p.relative_to(ROOT)) for p in paths}:raise ValueError('all prior admission and analytic scope inputs')
    bind(ROOT,inputs);bind(ROOT,read(PUBLICATION/'manifest.json')['files'])
    bind(PARENT,read(PARENT/'receipt.json')['files_sha256'])
    parent_source=read(PARENT/'source_seal.json');bind(ROOT,parent_source);bind(PARENT/'frozen_source',parent_source)
    prior_review=read(PARENT/'independent_verification.json');bind(PARENT,prior_review['input_sha256'])
    checks={r['file']:r['proof'] for r in prior_review['checks']}
    if prior_review.get('all_passed')is not True or checks[PARENT_RESULT]['verified']is not True or prior_review['decision']['dual_status']!='exact_separator':
        raise ValueError('complete independently admitted affine separator')
    prior=read(PARENT/PARENT_RESULT)
    if prior['status']!='exact_separator' or prior['program']!=PROGRAM or prior['scales']!=SCALES or prior['synthesis'].get('certified')is not True:
        raise ValueError('fixed complete admitted parent witness')
    protocol=read(d/'protocol.json')
    expected=dict(schema=1,grammar=L.SPEC,diagnostic=DIAGNOSTIC,program=PROGRAM,scales=SCALES,
        per_instance_build_limits=LIMITS,diagnostic_limits=LIMITS,parallel=PARALLEL,cooperative_seconds=360,
        source_json_bytes=67108864,result_json_bytes=8388608,tests=TESTS,descriptor_count=210,all_source_families=True,
        no_new_floating_search=True,no_actual_signed_response_inputs=True,**FLAGS)
    for key,value in expected.items():
        if protocol.get(key)!=value:raise ValueError('known frozen complete localizer protocol '+key)
    if read(d/'tests.json')['returncode']!=0:raise ValueError('prescore calibrations')
    receipt=read(d/'receipt.json')
    actual={str(p.relative_to(d)):sha(p) for p in d.rglob('*.json') if p.name!='receipt.json'}
    if receipt['files_sha256']!=actual or receipt['source_count']!=len(source):raise ValueError('complete terminal evidence')
    if read(d/'run_started.json')!=dict(protocol_sha256=sha(d/'protocol.json')):raise ValueError('single frozen execution')
    execution=read(d/'execution.json');cost=execution['cost']
    for key,value in dict(workers=1,requested_workers=1,worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,
                          worker_memory_limit_enforced=True,numerical_threads_per_worker=1,serial_fallback=False).items():
        if type(cost.get(key))is not type(value) or cost[key]!=value:raise ValueError('actual isolated diagnostic resource '+key)
    if len(execution['results'])!=1 or execution['results'][0]['index']!=0:raise ValueError('complete ordered single job')
    row=execution['results'][0];status=row['status'];proof=None
    if status=='available':
        value=row['value']
        if value['file']!='result.json' or value['sha256']!=sha(d/'result.json'):raise ValueError('isolated result binding')
        result=read(d/'result.json');status=result['status']
        if result['cost']!=value['cost'] or status!=value['status'] or result['probe']['counts']!=value['counts']:
            raise ValueError('actual worker status/cost/counts')
        if result['cost']['elapsed_seconds']>360 or result['cost']['observed_threads_at_completion']!=1:
            raise ValueError('declared diagnostic time/thread envelope')
        if result['program']!=PROGRAM or result['scales']!=SCALES or result['grammar_sha256']!=L.digest(L.SPEC) or result['parent_result_sha256']!=sha(PARENT/PARENT_RESULT) or result['source_sha256']!=sha(d/'source.json'):
            raise ValueError('complete source/grammar/parent result binding')
        if result['no_new_floating_search']is not True or any(result.get(k)is not False for k in FLAGS):raise ValueError('finite exact-witness scope')
        for name,limit in [('source.json',67108864),('result.json',8388608)]:
            if len(json.dumps(read(d/name),sort_keys=True,separators=(',',':')).encode())>limit:raise ValueError('declared artifact size '+name)
        instances=geometry(read(d/'source.json'),prior)
        proof=C.verify(instances,L.additions()['relation'],prior['synthesis'],result['probe'])
        if proof['status']!=status:raise ValueError('independent diagnostic branch')
    elif status not in ['missing_resource','error'] or (d/'result.json').exists():
        raise ValueError('resource failures cannot invent diagnostic evidence')
    review=dict(all_passed=True,result_status=status,proof=proof,source_count=len(source),
                no_new_floating_search=True,input_sha256={n:sha(d/n) for n in ['protocol.json','source_seal.json','input.json','tests.json','seal.json','execution.json','receipt.json']},**FLAGS)
    with out.open('x') as stream:json.dump(review,stream,sort_keys=True,indent=2);stream.write('\n')
    return review


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('directory');r=audit(parser.parse_args().directory)
    print(json.dumps(dict(all_passed=r['all_passed'],result_status=r['result_status'],counts=r['proof']['counts'] if r['proof'] else None)))

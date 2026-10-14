"""Independent immutable-weight, memory-only joint Gram transfer retry audit."""
import hashlib
import json
from pathlib import Path
from fractions import Fraction as F
import check_cancellation_joint_gram_program as B
import check_cancellation_shared_gram as G
ROOT=Path(__file__).resolve().parent
FLAGS=dict(global_bound_proved=False,RH_proved=False)
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())

def verify_fixed_transfer(original,training,result):
    if (original['status']!='missing_resource' or original.get('reason')!='MemoryError' or original.get('phase')!='final' or original.get('index')!=2) or original['scales']!=[13] or original['program']['claim']!='unsigned_calibration':raise ValueError('exact failed X13 unsigned case')
    if training['status']!='finite_PSD_certificate' or training['program']!=original['program']:raise ValueError('same admitted unsigned training program')
    if result['program']!=original['program'] or result['scales']!=[13] or result.get('refitted') is not False:raise ValueError('same transfer case without refit')
    fitted=training['synthesis'];candidate=result['synthesis']
    if candidate.get('weights')!=fitted['weights'] or candidate.get('grams')!=fitted['grams']:raise ValueError('fixed training coefficients and Grams')
    if set(fitted['grams'])!=set(B.gram_specs()) or any(len(fitted['grams'][k])!=n or any(len(row)!=n or any(F(v) for v in row) for row in fitted['grams'][k]) for k,n in B.gram_specs().items()):raise ValueError('four exact zero Grams')
    built=B.build(original['program'],13)
    for key,field in [('ordinary_case_hashes','instance'),('case_hashes','instance'),('factor_archive_hashes','factor_archive'),('divisor_archive_hashes','divisor_archive'),('cell_archive_hashes','cell_archive'),('gram_block_hashes','gram_blocks'),('gram_archive_hashes','gram_archive')]:
        expected=[digest(built[field])]
        if original.get(key)!=expected or result.get(key)!=expected:raise ValueError('same full source '+key)
    if original['dictionary_sha256']!=built['dictionary_sha256'] or result['dictionary_sha256']!=built['dictionary_sha256'] or original['gram_specs']!=B.gram_specs() or result['gram_specs']!=B.gram_specs():raise ValueError('same dictionary and Gram dimensions')
    full=G.verify_primal([built['instance']],[built['gram_blocks']],B.gram_specs(),candidate)
    return dict(verified=True,full_original_formal_identity_verified=True,same_X13_case_verified=True,fixed_training_weights_verified=True,four_zero_Grams_verified=True,finite_signed_upper_bound_proved=False,full_Gram_certificate_check=full,**FLAGS)

def verify_resources(protocol):
    parallel=protocol['parallel'];limits=protocol['limits']
    if parallel['workers']!=1 or parallel['worker_memory_bytes']!=6*1024**3 or parallel['memory_budget_bytes']!=6*1024**3 or parallel['timeout_seconds']!=600:raise ValueError('authorized memory only profile')
    if limits['time_limit']!=180:raise ValueError('unchanged cooperative deadline')
    if (protocol.get('no_new_float_search') is not True or protocol.get('same_candidate') is not True or protocol.get('refitted') is not False) or protocol['scales']!=[13]:raise ValueError('fixed retry declaration')
    return dict(verified=True,one_worker_6GiB_verified=True,unchanged_deadlines_verified=True)

def verify_execution(execution,result,result_sha256):
    cost=execution['cost']
    expected=dict(worker_memory_bytes=6*1024**3,memory_budget_bytes=6*1024**3,workers=1,requested_workers=1,available=1,missing=0,errors=0,worker_memory_limit_enforced=True,serial_fallback=False,numerical_threads_per_worker=1)
    for key,value in expected.items():
        if type(cost.get(key))is not type(value) or cost[key]!=value:raise ValueError('actual execution profile '+key)
    rows=execution['results']
    if type(rows)is not list or len(rows)!=1 or rows[0].get('index')!=0 or rows[0].get('status')!='available':raise ValueError('one ordered available result')
    value=rows[0]['value']
    if value.get('file')!='result.json' or value.get('sha256')!=result_sha256 or value.get('status')!=result['status'] or value.get('cost')!=result['cost']:raise ValueError('runtime result hash/status/cost binding')
    if value.get('global_bound_proved') is not False or value.get('RH_proved') is not False:raise ValueError('runtime finite scope')
    return dict(verified=True,actual_6GiB_worker_and_total_verified=True,memory_limit_enforcement_verified=True,one_ordered_result_verified=True,result_hash_status_cost_verified=True)

def audit(directory):
    d=Path(directory).resolve();target=d/'independent_verification.json'
    if target.exists():raise FileExistsError('exclusive independent verification artifact')
    seal=read(d/'seal.json')
    for key in ['protocol','source_seal','input','candidate']:
        if seal[key+'_sha256']!=sha(d/(key+'.json')):raise ValueError('retry seal '+key)
    for n,h in read(d/'source_seal.json').items():
        if sha(ROOT/n)!=h or sha(d/'frozen_source'/n)!=h:raise ValueError('frozen retry source '+n)
    for n,h in read(d/'input.json')['input_sha256'].items():
        if sha(ROOT/n)!=h:raise ValueError('original retry input '+n)
    for n,h in read(d/'receipt.json')['files_sha256'].items():
        if sha(d/n)!=h:raise ValueError('retry terminal receipt '+n)
    parent=ROOT/'cancellation-arithmetic-results/joint-shared-gram-probe-001';original=read(parent/'jobs/final-002.json');training=read(parent/'jobs/train-001.json');protocol=read(d/'protocol.json');result=read(d/'result.json')
    candidate=read(d/'candidate.json')
    if candidate!=dict(weights=training['synthesis']['weights'],grams=training['synthesis']['grams'],training_sha256=sha(parent/'jobs/train-001.json')):raise ValueError('exact saved training candidate')
    if protocol['weights_sha256']!=digest(candidate['weights']) or protocol['grams_sha256']!=digest(candidate['grams']):raise ValueError('candidate protocol hash')
    if protocol['limits']!=read(parent/'protocol.json')['limits']:raise ValueError('memory is sole computational limit change')
    parent_plan=read(parent/'candidate_seal.json')
    if parent_plan['training_sha256']!=sha(parent/'training.json') or parent_plan['jobs'][2]!=dict(phase='final',program=training['program'],X=13,attempt_file='jobs/train-001.json',attempt_sha256=sha(parent/'jobs/train-001.json')):raise ValueError('same preregistered final candidate')
    for name,h in read(parent/'source_seal.json').items():
        if sha(ROOT/name)!=h or sha(parent/'frozen_source'/name)!=h:raise ValueError('unchanged original source '+name)
    for name,h in read(parent/'receipt.json')['files_sha256'].items():
        if sha(parent/name)!=h:raise ValueError('unchanged original terminal artifact '+name)
    parent_audit=read(parent/'independent_verification.json')
    if parent_audit.get('all_passed') is not True:raise ValueError('admitted original stage')
    for name,h in parent_audit['input_sha256'].items():
        if sha(parent/name)!=h:raise ValueError('original independent audit binding '+name)
    resources=verify_resources(protocol);execution=verify_execution(read(d/'execution.json'),result,sha(d/'result.json'));full=verify_fixed_transfer(original,training,result)
    review=dict(all_passed=True,resources=resources,execution=execution,transfer=full,input_sha256={n:sha(d/n) for n in ['protocol.json','source_seal.json','input.json','seal.json','receipt.json','result.json','execution.json']},**FLAGS)
    with target.open('x') as stream:json.dump(review,stream,sort_keys=True,indent=2);stream.write('\n')
    return review
if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('directory');args=parser.parse_args();print(json.dumps(dict(all_passed=audit(args.directory)['all_passed']),sort_keys=True))

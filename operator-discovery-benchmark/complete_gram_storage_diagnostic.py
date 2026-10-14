"""Exact old-witness diagnostic for an anchored multiscale state extension.

No estimate is assumed: E+S_K is coercive for K PSD, but its proposed uniform
innovation bound is an additional unresolved obligation. The new RHS column
in D-Delta(E)=Q+Delta(S_K) has moment H_child-4*H_parent.
"""
import argparse
import ast
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import check_cancellation_shared_gram as I
from check_complete_gram_moment_probe_v2 import negative_direction
import check_cancellation_complete_gram_program as B
from detector_workflow_guard import require_verified_runtime

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'cancellation-arithmetic-results/complete-gram-search-001'
FLAGS=dict(global_bound_proved=False,RH_proved=False)
SPEC=dict(version='anchored-storage-witness-v1',dimension=14,atoms=B.SPEC['atoms'],
          state='R=e_prefix*e_prefix^T+K with K PSD, shared at every scale',
          increment='S_K(2X)-4*S_K(X)',dual_matrix='H_child-4*H_parent',
          original_lhs='D-(E(2X)-4E(X))',
          proposed_identity='original_lhs=old_proof_terms+storage_increment',
          constant_vector=['0']*5+['-1/2']*9,
          selection='entire anchored PSD state cone; no selected channel restrictions',
          scope='diagnostic only; no primal feasibility or uniform innovation bound')

def read(p):return json.loads(Path(p).read_text())
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False).encode()).hexdigest()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
    with Path(p).open('x') as f:json.dump(x,f,sort_keys=True,indent=2,allow_nan=False);f.write('\n')

def source_names():
    pending=['complete_gram_storage_diagnostic','test_complete_gram_storage_diagnostic'];seen=set()
    while pending:
        name=pending.pop();path=ROOT/(name+'.py')
        if name in seen or not path.is_file():continue
        seen.add(name)
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)

def parent_bindings():
    review=read(PARENT/'independent_verification.json')
    if review.get('all_passed')is not True:raise ValueError('admitted full14 search required')
    for name,h in review['input_sha256'].items():
        if sha(PARENT/name)!=h:raise ValueError('parent audit binding')
    for name,h in read(PARENT/'receipt.json')['files_sha256'].items():
        if sha(PARENT/name)!=h:raise ValueError('parent terminal binding')
    for name,h in read(PARENT/'source_seal.json').items():
        if sha(ROOT/name)!=h or sha(PARENT/'frozen_source'/name)!=h:raise ValueError('parent frozen source')
    result=read(PARENT/'jobs/dual-000.json')
    if result['status']!='exact_separator' or result['independent_check']['verified']is not True:raise ValueError('exact full14 separator')
    return result

def compute(dual):
    if dual['gram_specs']!=B.gram_specs():raise ValueError('exact full14 dimensions')
    parent=dual['gram_duals']['full_parent']['matrix'];child=dual['gram_duals']['full_child']['matrix']
    I.verify_psd(parent);I.verify_psd(child)
    matrix=[[F(child[i][j])-4*F(parent[i][j]) for j in range(14)] for i in range(14)]
    v=negative_direction(matrix)
    out=dict(matrix=[[str(q) for q in row] for row in matrix],input_dual_sha256=digest(dual),
             larger_cone_feasibility_proved=False,uniform_innovation_bound_proved=False,
             recovery_conditional_on_uniform_innovation=True,**FLAGS)
    if v is None:
        out.update(status='witness_extends_to_anchored_storage_cone',PSD_proof=I.verify_psd(matrix))
    else:
        K=[[str(v[i]*v[j]) for j in range(14)] for i in range(14)]
        state=[[str(F(K[i][j])+int(i==j==0)) for j in range(14)] for i in range(14)]
        value=sum((v[i]*matrix[i][j]*v[j] for i in range(14) for j in range(14)),F(0))
        parent_dot=sum((v[i]*F(parent[i][j])*v[j] for i in range(14) for j in range(14)),F(0))
        child_dot=sum((v[i]*F(child[i][j])*v[j] for i in range(14) for j in range(14)),F(0))
        if value>=0 or value!=child_dot-4*parent_dot:raise ValueError('exact increment sign and pairing')
        z=[F(q) for q in SPEC['constant_vector']];constant=sum((a*b for a,b in zip(v,z)),F(0))
        out.update(status='witness_invalid_for_anchored_storage_cone',direction=list(map(str,v)),
                   K=K,state_matrix=state,K_PSD_proof=I.verify_psd(K),state_PSD_proof=I.verify_psd(state),
                   coercivity_remainder_PSD_proof=I.verify_psd(K),quadratic_value=str(value),
                   parent_pairing=str(parent_dot),child_pairing=str(child_dot),
                   increment_formal_constant_per_X=str(-2*constant**2))
    return out

def freeze(directory):
    require_verified_runtime();parent_bindings();d=Path(directory).resolve();d.mkdir(parents=True,exist_ok=False);(d/'frozen_source').mkdir()
    hashes={}
    for name in source_names():(d/'frozen_source'/name).write_bytes((ROOT/name).read_bytes());hashes[name]=sha(ROOT/name)
    names=['protocol.json','source_seal.json','receipt.json','independent_verification.json','jobs/dual-000.json']
    write(d/'protocol.json',dict(spec=SPEC,no_new_float_search=True,new_operator_scores_before_freeze=False,**FLAGS))
    write(d/'source_seal.json',hashes);write(d/'input.json',{n:sha(PARENT/n) for n in names})
    write(d/'seal.json',{n+'_sha256':sha(d/(n+'.json')) for n in ['protocol','source_seal','input']})
    return d

def validate(d):
    d=Path(d)
    for n,h in read(d/'seal.json').items():
        if sha(d/(n.removesuffix('_sha256')+'.json'))!=h:raise ValueError('storage diagnostic seal')
    if read(d/'protocol.json')['spec']!=SPEC:raise ValueError('fixed state extension')
    sources=read(d/'source_seal.json')
    if set(sources)!=set(source_names()):raise ValueError('complete diagnostic sources')
    for n,h in sources.items():
        if sha(ROOT/n)!=h or sha(d/'frozen_source'/n)!=h:raise ValueError('frozen diagnostic source')
    for n,h in read(d/'input.json').items():
        if sha(PARENT/n)!=h:raise ValueError('parent diagnostic input')
    parent_bindings()

def run(directory):
    require_verified_runtime();d=Path(directory);validate(d)
    test=subprocess.run([sys.executable,'-B','-m','unittest','test_complete_gram_storage_diagnostic'],cwd=ROOT,capture_output=True,text=True,timeout=30)
    write(d/'tests.json',dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr))
    if test.returncode:raise ValueError('storage diagnostic calibration')
    out=compute(parent_bindings()['synthesis']);write(d/'result.json',out);validate(d)
    write(d/'receipt.json',{str(p.relative_to(d)):sha(p) for p in sorted(d.rglob('*.json'))})
    print(json.dumps({k:v for k,v in out.items() if k in ['status','direction','increment_formal_constant_per_X']}))

def verify(directory):
    require_verified_runtime();d=Path(directory);validate(d)
    for n,h in read(d/'receipt.json').items():
        if sha(d/n)!=h:raise ValueError('diagnostic terminal artifact')
    expected=compute(parent_bindings()['synthesis'])
    if expected!=read(d/'result.json'):raise ValueError('exact state matrix replay')
    review=dict(all_passed=True,scope='exact moment extension diagnostic; uniform bridge and innovation estimate require separate review',
                input_sha256={n:sha(d/n) for n in ['protocol.json','source_seal.json','input.json','seal.json','tests.json','result.json','receipt.json']},**FLAGS)
    write(d/'verification.json',review);print(json.dumps(dict(all_passed=True,status=expected['status'])))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['freeze','run','verify']);parser.add_argument('directory');args=parser.parse_args()
    {'freeze':freeze,'run':run,'verify':verify}[args.command](args.directory)

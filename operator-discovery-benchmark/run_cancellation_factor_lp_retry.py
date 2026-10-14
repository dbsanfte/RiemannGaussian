"""Separate sealed sparse-LP retry in the fixed-zero-Gram factor subcone."""
import argparse
from pathlib import Path
import subprocess
import sys
import run_cancellation_factor_search as P
import cancellation_arithmetic_synthesis as S
import grouped_arithmetic_synthesis as GS
import check_grouped_arithmetic as G

R=P.R
FLAGS=dict(global_bound_proved=False,RH_proved=False)
OWN=['run_cancellation_factor_lp_retry.py','test_run_cancellation_factor_lp_retry.py','check_cancellation_factor_lp_retry.py','test_check_cancellation_factor_lp_retry.py']
TESTS=['test_run_cancellation_factor_lp_retry','test_check_cancellation_factor_lp_retry']
write=P.write

def inputs(parent):
    parent=Path(parent)
    return {n:parent/n for n in ['protocol.json','seal.json','source_seal.json','training.json','independent_verification.json']} | {'supplied_embedding_audit':R.ROOT/'cancellation_factor_unsigned_embedding_audit.json'}

def freeze(parent):
    parent=Path(parent); P.validate(parent.parent)
    if parent.name!='factor-probe-001':raise ValueError('factor parent required')
    if R.read(parent/'independent_verification.json').get('all_passed') is not True:raise ValueError('verified factor parent required')
    dest=parent/'lp-retry-001'
    if dest.exists():raise FileExistsError('retry destination already exists')
    sources=sorted(set(P.SOURCES+OWN))
    for n in sources:
        if not (R.ROOT/n).is_file():raise FileNotFoundError(n)
    ih={n:R.sha(p) for n,p in inputs(parent).items()}
    previous=R.read(parent/'protocol.json')
    protocol=dict(schema=1,programs=previous['programs'],training_scales=previous['training_scales'],final_scales=[7,11],limits=dict(previous['limits'],time_limit=180),tests=TESTS,inputs_sha256=ih,source_names=sources,runtime=previous['runtime'],dictionary_sha256=R.digest(P.F.descriptors()),grams_fixed_zero=True,scope='same normalized factor dictionary; Gram matrices fixed zero, a strict subcone; failure does not imply full Gram infeasibility',constant_slack_allowed=True,final_refit=False,original_results_preserved=True,no_actual_signed_responses=True,**FLAGS)
    dest.mkdir();(dest/'frozen_source').mkdir()
    for n in sources:(dest/'frozen_source'/n).write_bytes((R.ROOT/n).read_bytes())
    write(dest/'protocol.json',protocol)
    write(dest/'source_seal.json',dict(hashes={n:R.sha(R.ROOT/n) for n in sources}))
    write(dest/'seal.json',dict(protocol_sha256=R.sha(dest/'protocol.json'),source_seal_sha256=R.sha(dest/'source_seal.json')))

def validate(parent):
    parent=Path(parent);P.validate(parent.parent);out=parent/'lp-retry-001';p=R.read(out/'protocol.json')
    if R.read(out/'seal.json')!=dict(protocol_sha256=R.sha(out/'protocol.json'),source_seal_sha256=R.sha(out/'source_seal.json')):raise ValueError('retry seal changed')
    h=R.read(out/'source_seal.json')['hashes']
    if set(h)!=set(P.SOURCES+OWN) or p['source_names']!=sorted(h):raise ValueError('source coverage')
    for n,v in h.items():
        if R.sha(R.ROOT/n)!=v or R.sha(out/'frozen_source'/n)!=v:raise ValueError('retry code changed')
    if p['inputs_sha256']!={n:R.sha(q)for n,q in inputs(parent).items()}:raise ValueError('parent inputs changed')
    expected=R.read(parent/'protocol.json')
    if p['programs']!=expected['programs'] or p['training_scales']!=expected['training_scales'] or p['final_scales']!=[7,11] or p['limits']!=dict(expected['limits'],time_limit=180):raise ValueError('retry protocol mismatch')
    return p

def train(program,scales,limits):
    row=dict(program=program,case_hashes=[],factor_archive_hashes=[],dictionary_sha256=R.digest(P.F.descriptors()),gamma=None,independent_check=None,grams_fixed_zero=True,**FLAGS)
    try:
        built=[P.build(program,X)for X in scales];instances=[b['instance']for b in built]+P.constraints(program)
        row.update(case_hashes=list(map(R.digest,instances)),factor_archive_hashes=[R.digest(b['factor_archive'])for b in built])
        result=S.synthesize(instances,allow_constant_slack=True,**limits)
        row['proposed_synthesis']=result
        checked=G.verify_joint_result(instances,result,allow_constant_slack=True)
        row.update(synthesis=result,independent_check=checked)
        if result['status']=='finite_certificate':row['gamma']=str(P.gate.gamma(result['weights'],P.F.descriptors()))
    except (OverflowError,TimeoutError,MemoryError)as e:row['synthesis']=dict(status='missing_resource',reason=str(e),**FLAGS)
    except (ValueError,TypeError,KeyError)as e:row['synthesis']=dict(status='no_certificate_found',reason='rejected: '+str(e),**FLAGS)
    return row

def transfer(attempt,scales,limits):
    r=attempt['synthesis'];out=dict(status='no_candidate',observations=[],refitted=False,**FLAGS)
    if r['status']!='finite_certificate':return out
    out.update(status='evaluated',weights_sha256=R.digest(r['weights']))
    for X in scales:
        row=dict(X=X,case_sha256=None,factor_archive_sha256=None,**FLAGS)
        try:
            b=P.build(attempt['program'],X);i=b['instance'];scalar=P.budget.extract(i,r['weights'])
            row.update(case_sha256=R.digest(i),factor_archive_sha256=R.digest(b['factor_archive']),scalar_budget=scalar)
            cert=GS.instantiate_certificate(i,r['weights'],allow_constant_slack=True,**limits)
            wrapper=dict(status='finite_certificate',weights=r['weights'],certificates=[cert],constant_slacks=[scalar['scalar_slack']])
            check=G.verify_joint_result([i],wrapper,allow_constant_slack=True)
            row.update(status='finite_certificate',certificate=cert,independent_check=check)
        except (OverflowError,TimeoutError,MemoryError)as e:row.update(status='missing_resource',reason=str(e))
        except (ValueError,TypeError,KeyError)as e:row.update(status='template_mismatch',reason=str(e))
        out['observations'].append(row)
    return out

def run(parent):
    parent=Path(parent);p=validate(parent);out=parent/'lp-retry-001'
    if (out/'tests.json').exists():raise FileExistsError('retry already started')
    tests=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=R.ROOT,capture_output=True,text=True,timeout=180)
    write(out/'tests.json',dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr))
    if tests.returncode:raise ValueError('retry tests failed')
    (out/'attempts').mkdir();attempts=[]
    for j,program in enumerate(p['programs']):
        a=train(program,p['training_scales'],p['limits']);write(out/'attempts'/f'{j:03d}.json',a);attempts.append(a)
        print(a['synthesis']['status'],flush=True)
    write(out/'training.json',dict(attempts=attempts,**FLAGS))
    write(out/'candidate_seal.json',dict(training_sha256=R.sha(out/'training.json'),protocol_sha256=R.sha(out/'protocol.json')))
    write(out/'final.json',dict(results=[transfer(a,p['final_scales'],p['limits'])for a in attempts],refitted=False,**FLAGS))
    validate(parent)
    write(out/'producer_receipt.json',dict(files_sha256={n:R.sha(out/n)for n in ['protocol.json','source_seal.json','seal.json','tests.json','training.json','candidate_seal.json','final.json']},original_results_preserved=True,**FLAGS))

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('command',choices=['freeze','run']);a.add_argument('parent');v=a.parse_args();(freeze if v.command=='freeze'else run)(v.parent)

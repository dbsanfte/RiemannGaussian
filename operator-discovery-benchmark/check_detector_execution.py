"""Independent snapshot/receipt auditor for run_detector outputs.
No producer imports. Optional arithmetic replay uses independent checker builders.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import sys
BASE=Path(__file__).resolve().parent

def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(v):return hashlib.sha256(json.dumps(v,sort_keys=True,separators=(',',':'),allow_nan=False).encode()).hexdigest()
def require(v,msg):
    if not v:raise ValueError(msg)
def safe(root,name):
    require(type(name)is str and name and not Path(name).is_absolute() and '..'not in Path(name).parts,'unsafe artifact path')
    p=root/name;require(p.is_file()and not p.is_symlink()and p.resolve().is_relative_to(root.resolve()),'missing/escaping artifact: '+name);return p

def no_promotion(v):
    if isinstance(v,dict):
        for k,x in v.items():
            if k in ('global_bound_proved','RH_proved','actual_signed_upper_bound_proved','global_signed_upper_bound_proved'):require(x is False,'global promotion prohibited')
            no_promotion(x)
    elif isinstance(v,list):
        for x in v:no_promotion(x)

def audit(directory,*,recheck_math=False,require_live_sources=False):
    root=Path(directory).resolve();receipt_start=sha(root/'receipt.json');p=read(root/'protocol.json');inputs=read(root/'input.json');seal=read(root/'seal.json');sources=read(root/'source_seal.json');receipt=read(root/'receipt.json')
    no_promotion(p);no_promotion(inputs);no_promotion(receipt)
    require(seal==dict(protocol_sha256=sha(root/'protocol.json'),source_seal_sha256=sha(root/'source_seal.json'),input_sha256=sha(root/'input.json')),'protocol/input/source seal')
    require(type(sources)is dict and sources and all(type(n)is str and Path(n).name==n and n.endswith('.py')for n in sources),'source mapping')
    frozen=root/'frozen_source';require(frozen.is_dir()and not frozen.is_symlink(),'snapshot directory');require(set(sources)=={x.name for x in frozen.glob('*.py')},'frozen source coverage')
    live={}
    for n,h in sources.items():
        require(sha(safe(frozen,n))==h,'frozen source hash '+n)
        live[n]=(BASE/n).is_file()and sha(BASE/n)==h
    if require_live_sources:require(all(live.values()),'live source differs from frozen development snapshot')
    # Independently inspect static local-import closure from the saved source text.
    names={n[:-3]for n in sources}
    for n in sources:
        for node in ast.walk(ast.parse((frozen/n).read_text())):
            refs=[a.name.split('.')[0]for a in node.names]if isinstance(node,ast.Import)else [node.module.split('.')[0]]if isinstance(node,ast.ImportFrom)and node.module else[]
            for ref in refs:
                if (BASE/(ref+'.py')).is_file():require(ref in names,'snapshot misses local import '+ref)
    files=receipt['files_sha256'];require(type(files)is dict,'receipt hashes')
    for n,h in files.items():require(sha(safe(root,n))==h,'receipt artifact hash '+n)
    needed={'protocol.json','input.json','source_seal.json','seal.json','started.json','final_receipts.json'}
    require(read(root/'started.json')==dict(protocol_sha256=sha(root/'protocol.json')),'started protocol binding')
    mode=p['mode'];require(mode in ('search','transfer')and receipt['mode']==mode,'mode binding')
    require(p.get('final_refit')is False and p.get('grams_fixed_zero')is True and receipt.get('refitted')is False and receipt.get('grams_fixed_zero')is True and receipt.get('original_results_preserved')is True,'scope/refit flags')
    scales=p['final_scales'];require(type(scales)is list and scales and all(type(x)is int and x>0 for x in scales)and len(set(scales))==len(scales),'final scales')
    records=[];accepted_train=[];math_jobs=[]
    def phase(name,count):
        doc=read(root/('training_receipts.json'if name=='train'else name+'_receipts.json'));rs=doc['results'];require(type(rs)is list and len(rs)==count,'ordered '+name+' coverage')
        available=missing=errors=0
        for idx,r in enumerate(rs):
            require(type(r)is dict and type(r.get('index'))is int and r['index']==idx,'receipt index/order')
            no_promotion(r);st=r['status'];require(st in ('available','missing_resource','error'),'process receipt status')
            if st!='available':
                require('value'not in r,'failed process cannot promote value');missing+=st=='missing_resource';errors+=st=='error';continue
            available+=1;v=r['value'];file=f'jobs/{name}-{idx:04d}.json';require(v['file']==file and file in files,'job file coverage')
            path=safe(root,file);require(sha(path)==v['sha256']==files[file],'job hash binding');job=read(path);no_promotion(job)
            require(job['phase']==name and type(job['index'])is int and job['index']==idx and job['status']==v['status'],'job phase/status/index')
            require(job.get('refitted')is False and job.get('grams_fixed_zero')is True,'job fixed-weight scope')
            require(job.get('cost')==v.get('cost'),'job cost receipt binding')
            if job['status']=='finite_certificate':
                require(job.get('synthesis',{}).get('status')=='finite_certificate'and job.get('independent_check',{}).get('verified')is True,'accepted finite independent audit')
                require(job['independent_check'].get('finite_only')is True,'finite audit scope')
            else:require(job['status']in ('no_certificate_found','missing_resource','rejected'),'nonpromotion job status')
            records.append((name,idx,job,path));
        cost=doc['cost']
        for key,num in [('available',available),('missing',missing),('errors',errors)]:
            if key in cost:require(type(cost[key])is int and cost[key]==num,'process count '+key)
        require(cost.get('serial_fallback')is False,'no hidden serial fallback')
        return doc
    if mode=='search':
        needed|={'training_receipts.json','candidate_seal.json'};programs=inputs['programs'];require(type(programs)is list and programs,'search program inputs')
        tr=phase('train',len(programs))
        for name,idx,j,path in records:
            require(j.get('program',programs[idx])==programs[idx],'training program binding')
            if j['status']=='finite_certificate':
                require(j['scales']==p['training_scales'],'training scale binding');h=j['instance_sha256'];require(j['independent_check'].get('instance_sha256')==h and j['independent_check'].get('source_binding_checked')is True,'training full source hashes')
                require(j['case_sha256']==h[:len(p['training_scales'])]and len(j['factor_archive_sha256'])==len(p['training_scales']),'training domain/archive coverage')
                accepted_train.append((j,path))
        plan=read(root/'candidate_seal.json');require(plan['training_receipts_sha256']==sha(root/'training_receipts.json'),'candidate training seal')
        expected=[dict(attempt_file=str(path.relative_to(root)),attempt_sha256=sha(path),X=X)for j,path in accepted_train for X in scales]
        require(plan['final_jobs']==expected,'exact candidate/no-refit final plan')
        specs=expected
    else:
        require(p['training_scales']==[]and set(inputs)=={'attempt'},'transfer input shape')
        attempt=inputs['attempt'];require(attempt.get('synthesis',{}).get('status')=='finite_certificate'and attempt.get('independent_check',{}).get('verified')is True,'transfer accepted input')
        specs=[dict(X=X)for X in scales]
    final=phase('final',len(specs));accepted_final=0
    for name,idx,j,path in records:
        if name!='final':continue
        spec=specs[idx];attempt=inputs['attempt']if mode=='transfer'else read(root/spec['attempt_file'])
        if j['status']=='finite_certificate':
            require(j['X']==spec['X']and j['program']==attempt['program'],'final program/scale binding')
            require(j['synthesis']['weights']==attempt['synthesis']['weights']and j['weights_sha256']==digest(attempt['synthesis']['weights']),'unchanged candidate weights')
            require(j['independent_check'].get('instance_sha256')==[j['case_sha256']]and j['independent_check'].get('source_binding_checked')is True,'final complete source binding')
            require(type(j['factor_archive_sha256'])is str and len(j['factor_archive_sha256'])==64,'complete factor archive hash');accepted_final+=1;math_jobs.append(j)
    require(type(receipt['final_jobs'])is int and type(receipt['accepted_finite_checks'])is int and receipt['final_jobs']==len(specs)and receipt['accepted_finite_checks']==accepted_final and receipt['final_cost']==final['cost'],'final summary counts/cost')
    require(needed<=set(files),'receipt mandatory artifact coverage')
    require({str(x.relative_to(root))for x in (root/'jobs').glob('*.json')}<=set(files),'retained job file coverage')
    src=Path(p['input_source']);input_external_checked=src.is_file()
    if input_external_checked:
        require(sha(src)==p['input_source_sha256'],'external original input hash')
        v=read(src);require((v==inputs['attempt'])if mode=='transfer'else(v['programs']==inputs['programs']),'external input semantics')
    math=[]
    if recheck_math:
        import check_cancellation_factor_search as B
        import check_grouped_arithmetic_sparse as C
        for n in ('check_cancellation_factor_search.py','check_grouped_arithmetic_sparse.py'):require(live.get(n)is True,'math replay checker differs from snapshot')
        for name,idx,j,path in records:
            if j['status']!='finite_certificate':continue
            xs=j['scales']if name=='train'else[j['X']];built=[B.build(j['program'],X)for X in xs];instances=[b['instance']for b in built]
            if name=='train'and j['program']['constraint']=='zero_cubic':instances.append(B.auxiliary()['instance'])
            hashes=[C.digest(i)for i in instances];archive=[C.digest(b['factor_archive'])for b in built]
            require(archive==j['factor_archive_sha256']if name=='train'else archive==[j['factor_archive_sha256']],'independent factor archive replay')
            expected=j['instance_sha256']if name=='train'else[j['case_sha256']];require(hashes==expected,'independent full domain replay')
            check=C.verify_joint_result(instances,j['synthesis'],allow_constant_slack=j['program']['allow_constant_slack'],expected_instance_sha256=expected,time_limit=p['audit_seconds'],max_operations=p['limits']['max_operations']);math.append(dict(phase=name,index=idx,verified=check['verified']))
        # Check independent local audit imports are snapshot-bound, except this new auditor.
        for m in list(sys.modules.values()):
            f=getattr(m,'__file__',None)
            if f:
                q=Path(f).resolve()
                if q.parent==BASE and q.suffix=='.py'and q.name!=Path(__file__).name:require(q.name in sources and sha(q)==sources[q.name],'math import snapshot binding '+q.name)
    # End hashes guard concurrent mutation; frozen/live driver mismatch is only reported.
    require(sha(root/'receipt.json')==receipt_start,'receipt changed during audit')
    for n,h in files.items():require(sha(safe(root,n))==h,'artifact changed during audit')
    for n,h in sources.items():require(sha(safe(frozen,n))==h,'snapshot changed during audit')
    return dict(schema=1,all_passed=True,input_sha256={n:sha(root/n)for n in sorted(set(files)|{'receipt.json'})},frozen_source_sha256=sources,live_source_matches=live,live_source_match_required=require_live_sources,external_input_checked=input_external_checked,accepted_finite_checks=accepted_final,training_finite_checks=len(accepted_train),math_rechecked=recheck_math,math_checks=math,scope='snapshot and receipt integrity; optional independent finite arithmetic replay, no runtime attestation or all-scale claim',global_bound_proved=False,RH_proved=False)

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('run_dir');a.add_argument('--recheck-math',action='store_true');a.add_argument('--require-live-sources',action='store_true');a.add_argument('--output');v=a.parse_args();result=audit(v.run_dir,recheck_math=v.recheck_math,require_live_sources=v.require_live_sources)
    if v.output:
        with Path(v.output).open('x')as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
    else:print(json.dumps(result,sort_keys=True,indent=2))

"""Independent cancellation dictionary and finite transfer run checker."""
from fractions import Fraction as F
from math import gcd,isqrt
import json,hashlib
from pathlib import Path
import check_grouped_arithmetic_run as B
import check_grouped_arithmetic as G
P=G.P

def require(x,msg):
 if not x:raise ValueError(msg)
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def descriptors():
 d=B.descriptors();atoms=('prefix','half','even','mod3one','prime');mix=[(a,b,s) for i,a in enumerate(atoms) for b in atoms[i+1:] for s in (1,-1)]
 sq=[dict(family='signed_block',region=r,contrast=a,weight='one') for r in ('parent','child') for a in atoms]
 sq +=[dict(family='signed_block',region=r,contrast='mix',left=a,right=b,sign=s,weight='one') for r in ('parent','child') for a,b,s in mix]
 sq +=[dict(family='signed_block',region=r,contrast='growing_prime',root_order=k,weight='one') for r in ('parent','child') for k in (2,3)]
 rel=[dict(family=f,region=r,multiplier=m,weight=w) for f in ('norm_core','gcd_pair','prime_transport') for r in ('all','head','tail') for m in ('product','difference') for w in ('one','defect_kernel')]
 return dict(square=d['square']+[dict(v,id=digest(v)) for v in sq],relation=d['relation']+[dict(v,id=digest(v)) for v in rel])
def contrast(kind,t):
 return {(j,):F(1) for j in range(1,(t//2 if kind=='half' else t)+1) if kind in ('prefix','half') or kind=='even' and j%2==0 or kind=='mod3one' and j%3==1 or kind=='prime' and P.prime(j)}
def floorroot(X,k):
 r=0
 while (r+1)**k<=X:r+=1
 return r
def ast(desc,t,X):
 I=lambda n:['int',n];V=lambda n:['v',n]
 def simple(kind):
  if kind in ('prefix','half'):return ['sum','j',I(1),I(t//2 if kind=='half' else t),['x',V('j')]]
  pred=['eq',['imod',V('j'),I(2)],I(0)] if kind=='even' else ['eq',['imod',V('j'),I(3)],I(1)] if kind=='mod3one' else ['prime',V('j')]
  return ['sum','j',I(1),I(t),['guard',pred,['x',V('j')]]]
 if desc['contrast']=='mix':return ['add',simple(desc['left']),['scale',str(desc['sign']),simple(desc['right'])]]
 if desc['contrast']=='growing_prime':return ['sum','p',I(2),I(B.rootceil(X,desc['root_order'])),['guard',['prime',V('p')],['sum','j',I(1),['idiv',I(t),V('p')],['guard',['eq',['gcd',V('j'),V('p')],I(1)],['x',V('j')]]]]]
 return simple(desc['contrast'])
def build(program,X):
 old=dict(program);old.pop('dictionary_mode',None);b=B.build(old,X)
 if program.get('dictionary_mode')=='baseline':return b
 d=descriptors();N=4*X-1;archive=[]
 for desc in d['square'][52:]:
  group=[]
  for t in (range(X,2*X) if desc['region']=='parent' else range(2*X,4*X)):
   if desc['contrast']=='mix':p=P.add(contrast(desc['left'],t),contrast(desc['right'],t),F(desc['sign']))
   elif desc['contrast']=='growing_prime':
    p={}
    for prime in range(2,B.rootceil(X,desc['root_order'])+1):
     if P.prime(prime):p=P.add(p,{(j,):F(1) for j in range(1,t//prime+1) if gcd(j,prime)==1})
   else:p=contrast(desc['contrast'],t)
   poly=P.canonical(p);group.append(dict(weight='1',poly=poly));archive.append(dict(descriptor_id=desc['id'],t=t,ast=ast(desc,t,X),poly_sha256=digest(poly)))
  b['instance']['square_groups'].append(group)
 factors={n:[[p,e] for p,e in sorted(P.factor(n).items())] for n in range(1,N+1)};pref=[{(j,):F(1) for j in range(1,n+1)} for n in range(N+1)]
 def region(r,n):return r=='all' or r=='head' and n<=2*X or r=='tail' and n>2*X
 def J(n):return sum((w*sum(t>=n for t in range(lo,hi)) for lo,hi,w in ((X,2*X,-4),(2*X,4*X,1))))
 for desc in d['relation'][195:]:
  group=[]
  for a in range(1,N+1):
   for c in range(1 if desc['family']=='prime_transport' else a,N+1):
    anchor=c;family=desc['family']
    if family=='prime_transport':
     if not P.prime(a) or a*c>N or gcd(a,c)!=1:continue
     anchor=a*c;spec=dict(kind='coprime_product',a=a,b=c);poly=P.multiply({(a,):F(1)},{(c,):F(1)}) if desc['multiplier']=='product' else P.multiply({(c,):F(1)},P.add(pref[anchor],pref[c],F(-1)))
    else:
     if family=='norm_core':g=gcd(a,c);u,v=a//g,c//g;spec=dict(kind='norm',n=g,factors=factors[g]);left,right={(u,):F(1)},{(v,):F(1)}
     else:spec=dict(kind='gcd_product',a=a,b=c,factors_a=factors[a],factors_b=factors[c]);left,right={(a,):F(1)},{(c,):F(1)}
     difference=P.add(left,right,F(-1));poly=P.multiply(left,right) if desc['multiplier']=='product' else P.multiply(difference,difference)
    if region(desc['region'],anchor):w=1 if desc['weight']=='one' else J(anchor);group.append(dict(spec=spec,multiplier=P.canonical({m:v*w for m,v in poly.items()})))
  b['instance']['relation_groups'].append(group)
 b.update(square_ids=[v['id'] for v in d['square']],relation_ids=[v['id'] for v in d['relation']],dictionary_sha256=digest(d),ast_archive=archive)
 return b

def auxiliary_constraint(dictionary):
 sq=[[] for _ in dictionary['square']];rel=[];gamma=[]
 for desc in dictionary['relation']:
  coefficient=F(0)
  if desc.get('family')=='norm' and desc.get('weight')=='child_rowmass' and desc.get('multiplier')=='one':coefficient={'all':-F(56,3),'head':-F(12),'tail':-F(20,3)}[desc['region']]
  gamma.append(str(coefficient));rel.append([] if not coefficient else [dict(spec=dict(kind='unit'),multiplier=[dict(m=[],c=str(coefficient))])])
 return dict(instance=dict(target='mu',horizon=1,lhs=[],square_groups=sq,relation_groups=rel),square_ids=[d['id'] for d in dictionary['square']],relation_ids=[d['id'] for d in dictionary['relation']],dictionary_sha256=digest(dictionary),gamma_coefficients=gamma)

def budget(instance,weights):
 ledger=[];H=instance['horizon']
 for j,(w,g) in enumerate(zip(map(F,weights['square_weights']),instance['square_groups'])):
  if w:
   scalar=sum((F(t['weight'])*P.parse(t['poly'],H).get((),F(0))**2 for t in g),F(0));ledger.append(dict(kind='square',index=j,weight=str(w),group_scalar=str(scalar),contribution=str(w*scalar)))
 for j,(w,g) in enumerate(zip(map(F,weights['relation_weights']),instance['relation_groups'])):
  if w:
   scalar=sum((P.parse(t['multiplier'],H).get((),F(0))*G.relation(t['spec'],instance['target'],H).get((),F(0)) for t in g),F(0));ledger.append(dict(kind='relation',index=j,weight=str(w),group_scalar=str(scalar),contribution=str(w*scalar)))
 b=sum((F(t['contribution']) for t in ledger),F(0));D=P.parse(instance['lhs'],H).get((),F(0));return dict(B=str(b),D=str(D),scalar_slack=str(D-b),ledger=ledger,nonconstant_identity_verified=False,global_bound_proved=False,RH_proved=False)
def scalar_audit(instance):
 H=instance['horizon'];sq=rel=0
 for g in instance['square_groups'][52:]:
  for t in g:sq+=1;require(not P.parse(t['poly'],H).get((),F(0)),'added square scalar')
 for g in instance['relation_groups'][195:]:
  for t in g:rel+=1;require(not P.parse(t['multiplier'],H).get((),F(0))*G.relation(t['spec'],instance['target'],H).get((),F(0)),'added relation scalar')
 return dict(all_added_scalars_zero=True,square_atoms=sq,relation_atoms=rel,scope='formal scalar only; full relation admission and nonconstant matching are separate')
def programs():
 import itertools
 return [dict(target='mu',q=q,C=C,claim='critical',allow_constant_slack=True,dictionary_mode=m,constraint=c) for (m,c),q,C in itertools.product((('baseline','none'),('extended','none'),('extended','zero_cubic')),(2,3,6),(2,8,32))]+[dict(target='mu',q=2,C=1,claim='unsigned_calibration',allow_constant_slack=False,dictionary_mode=m,constraint='none') for m in ('baseline','extended')]
CODE=['run_cancellation_arithmetic.py','test_run_cancellation_arithmetic.py','cancellation_arithmetic_templates.py','test_cancellation_arithmetic_templates.py','cancellation_arithmetic_language.py','cancellation_arithmetic_synthesis.py','test_cancellation_arithmetic_synthesis.py','cancellation_cubic_gate.py','test_cancellation_cubic_gate.py','cancellation_budget.py','test_cancellation_budget.py','cancellation_search_analytic_scope.txt','cancellation_cubic_gate_independent_review.txt','check_cancellation_arithmetic_run.py','test_check_cancellation_arithmetic_run.py','grouped_arithmetic_templates.py','grouped_arithmetic_language.py','grouped_arithmetic_synthesis.py','check_grouped_arithmetic.py','run_grouped_arithmetic.py','check_grouped_arithmetic_run.py','arithmetic_cycle_language.py','arithmetic_cycle_synthesis.py','check_arithmetic_cycle_certificate.py','grouped_arithmetic_mu_cubic_budget_review.txt','grouped_arithmetic_proof.txt','critical_defect_proof.txt']
LIMITS=dict(max_columns=1024,max_monomials=30000,max_operations=200000000,max_coefficient_bits=2048,max_horizon=4096,max_degree=12,max_denominator=1000000,time_limit=30)
def verify_external_training(a,scales):
 require(a.get('external_resource_failure') is True and a.get('requested_scales')==scales,'external missing scope')
 require(all(a.get(k)==[] for k in ('case_hashes','ast_hashes','auxiliary_hashes','added_scalar_audits','budgets')) and a.get('gamma') is None,'external missing data shape')
 require(all(a.get(k) is None for k in ('independent_check','dual','independent_dual_check')),'external missing no validation')
 syn=a['synthesis'];require(set(syn)=={'status','reason','scope','global_bound_proved','RH_proved'} and syn['status']=='missing_resource' and bool(syn['reason']) and syn['global_bound_proved'] is False and syn['RH_proved'] is False,'external missing no certificate')
def verify_external_final(o):
 require(o.get('external_resource_failure') is True and o['status']=='missing_resource' and bool(o.get('reason')),'final missing scope')
 require(all(o.get(k) is None for k in ('case_sha256','ast_sha256','scalar_budget','added_scalar_audit')) and 'certificate' not in o and 'independent_check' not in o,'final missing no partial validation')
def audit_run(directory):
 import re
 d=Path(directory);names=['protocol.json','source_seal.json','seal.json','tests.json','training.json','candidate_seal.json','final_cases.json','final.json','producer_receipt.json'];hashes={n:sha(d/n) for n in names};s=read(d/'protocol.json');source=read(d/'source_seal.json');train=read(d/'training.json');final=read(d/'final.json');cs=read(d/'candidate_seal.json');fc=read(d/'final_cases.json');receipt=read(d/'producer_receipt.json');dicts=dict(baseline=B.descriptors(),extended=descriptors())
 require(set(source['hashes'])==set(CODE),'source set');require(read(d/'seal.json')==dict(protocol_sha256=hashes['protocol.json'],source_seal_sha256=hashes['source_seal.json']),'source protocol seal')
 def sources():
  for n,h in source['hashes'].items():require(sha(d/'frozen_source'/n)==h and sha(Path(__file__).parent/n)==h,'source integrity '+n)
 checkpoints={f'{i:03d}.json':sha(d/'attempts'/f'{i:03d}.json') for i in range(29)}
 sources();require(s['programs']==programs() and s['training_scales']==[1,2,3,5] and s['final_fixed_scale']==7 and s['final_odd_choices']==[9,11] and s['limits']==LIMITS and s['dual_time_limit']==10 and s['dictionaries']==dicts,'known protocol');require(s['tests']==[Path(n).stem for n in CODE if n.startswith('test_')],'tests coverage');test=read(d/'tests.json');require(test['returncode']==0 and re.search(r'Ran \d+ tests? in .*\n\s*OK\s*$',test['stdout']+test['stderr']),'tests passed')
 selection=digest(dict(programs=programs(),dictionaries=dicts,training_scales=[1,2,3,5]));require(cs==dict(training_sha256=hashes['training.json'],protocol_sha256=hashes['protocol.json'],selection_sha256=selection),'candidate seal');scales=[7,[9,11][int(selection,16)%2]];require(fc==dict(scales=scales,candidate_seal_sha256=hashes['candidate_seal.json'],no_refitting=True),'final selection');require([a['program'] for a in train['attempts']]==programs() and [f['program'] for f in final['results']]==programs(),'all29 attempts');require({p.name for p in (d/'attempts').iterdir()}=={f'{i:03d}.json' for i in range(29)},'checkpoint coverage');diagnostics=[];outcomes=[]
 for i,(a,f) in enumerate(zip(train['attempts'],final['results'])):
  require(read(d/'attempts'/f'{i:03d}.json')==a,'checkpoint match');p=a['program']
  if a.get('external_resource_failure'):
   verify_external_training(a,s['training_scales']);require(f['program']==p and f['status']=='no_candidate' and f['observations']==[] and f['refitted'] is False,'external missing no candidate');outcomes.append('no_candidate');continue
  built=[build(p,X) for X in s['training_scales']];ordinary=[b['instance'] for b in built];aux=[] if p['constraint']=='none' else [auxiliary_constraint(dicts[p['dictionary_mode']])['instance']];require(a['case_hashes']==list(map(digest,ordinary)) and a['ast_hashes']==[digest(b.get('ast_archive',[])) for b in built] and a['auxiliary_hashes']==list(map(digest,aux)),'case/AST/aux hashes');require(a['added_scalar_audits']==list(map(scalar_audit,ordinary)),'zero addedscalar');result=a['synthesis'];G.verify_joint_result(ordinary+aux,result,allow_constant_slack=p['allow_constant_slack'])
  if a['dual'] is not None and a['dual'].get('certified'):G.verify_joint_dual(ordinary+aux,a['dual'],allow_constant_slack=p['allow_constant_slack'])
  diagnostics.extend(dict(phase='training',program=p,**B.truth(b)) for b in built)
  if result['status']=='finite_certificate':
   require(a['budgets']==[budget(x,result['weights']) for x in ordinary],'training budgets');coef=auxiliary_constraint(dicts[p['dictionary_mode']])['gamma_coefficients'];gamma=sum((F(x)*F(y) for x,y in zip(coef,result['weights']['relation_weights'])),F(0));require(a['gamma']==str(gamma),'gamma');require(p['constraint']!='zero_cubic' or gamma==0,'zero cubic constraint')
  else:require(a['budgets']==[] and a['gamma'] is None,'missing no budgets')
  require(f['program']==p and f['refitted'] is False,'fixed final program')
  if result['status']!='finite_certificate':require(f['status']=='no_candidate' and f['observations']==[],'no candidate not pass');outcomes.append('no_candidate');continue
  require(f['status']=='evaluated' and f['weights_sha256']==digest(result['weights']) and [o['X'] for o in f['observations']]==scales,'weight transfer')
  for o in f['observations']:
   if o.get('external_resource_failure'):
    verify_external_final(o);outcomes.append('missing_resource');continue
   b=build(p,o['X']);inst=b['instance'];require(o['case_sha256']==digest(inst) and o['ast_sha256']==digest(b.get('ast_archive',[])) and o['scalar_budget']==budget(inst,result['weights']) and o['added_scalar_audit']==scalar_audit(inst),'final reconstruction');r=B.residual(inst,result['weights']);valid=not any(m for m in r) and (r.get((),F(0))>=0 if p['allow_constant_slack'] else not r)
   if o['status']=='finite_certificate':require(valid,'full target mismatch');G.verify_joint_result([inst],dict(status='finite_certificate',weights=result['weights'],constant_slacks=[str(r.get((),F(0)))],certificates=[o['certificate']]),allow_constant_slack=p['allow_constant_slack'])
   elif o['status']=='template_mismatch':require(not valid,'mismatch exact witness')
   else:require(o['status']=='missing_resource' and bool(o.get('reason')),'resource status')
   outcomes.append(o['status']);diagnostics.append(dict(phase='final',program=p,exact_residual=P.canonical(r),**B.truth(b)))
 require(receipt['all_programs_retained']==29 and all(receipt[n+'_sha256']==hashes[n+'.json'] for n in ('training','final','tests','source_seal')),'receipt');require(s['historical_coefficient_overlap'] is True and s['unseen_prime_holdout'] is False,'overlap');require({n:sha(d/n) for n in names}==hashes,'inputs changed');require({n:sha(d/'attempts'/n) for n in checkpoints}==checkpoints,'checkpoints changed');sources()
 def no_promotions(x):
  if isinstance(x,dict):
   for k,v in x.items():
    if k in ('RH_proved','global_bound_proved','global_critical_bound_proved'):require(v is False,'global promotion')
    no_promotions(v)
  elif isinstance(x,list):
   for v in x:no_promotions(v)
 for x in (s,train,final,receipt):no_promotions(x)
 return dict(schema=1,all_passed=True,input_sha256=hashes,code_sha256=source['hashes'],all29_programs_retained=True,outcomes=outcomes,actual_post_search_diagnostics=diagnostics,producer_math_imported=False,global_critical_bound_proved=False,RH_proved=False)
if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('run');args=p.parse_args();out=Path(args.run)/'independent_verification.json'
 if out.exists():raise FileExistsError('verification exists')
 result=audit_run(args.run)
 with out.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')

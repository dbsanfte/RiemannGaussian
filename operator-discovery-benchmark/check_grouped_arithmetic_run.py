"""Independent grouped-template run audit, no producer imports."""
import json,hashlib,itertools,re
from pathlib import Path
from fractions import Fraction as F
from math import gcd
import check_grouped_arithmetic as G
def rootceil(X,q):
 if X==1:return 1
 lo,hi=1,X
 while lo<hi:
  m=(lo+hi)//2
  if m**q>=X:hi=m
  else:lo=m+1
 return lo
P=G.P

def require(x,msg):
 if not x:raise ValueError(msg)
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def descriptors():
 s=[dict(family='constant',region='all',weight='critical_normalizer')]
 s +=[dict(family='coordinate',region=r,weight=w) for r in ('all','head','tail') for w in ('one','X','X2')]
 s +=[dict(family='prefix',region=r,weight=w) for r in ('all','initial','parent','child') for w in ('one','X')]
 s +=[dict(family='pair',domain=d,sign=v,weight=w) for d in ('all','coprime','noncoprime','divides') for v in (1,-1) for w in ('one','child_kernel','abs_defect_kernel')]
 s +=[dict(family='divisor_row',region=r,weight=w) for r in ('all','head','tail') for w in ('one','X')]
 s +=[dict(family='product',domain=d,weight=w) for d in ('all','coprime') for w in ('one','child_kernel')]
 r=[dict(family=f,region=r,weight=w,multiplier=m) for f in ('norm','prime_power','squarefree_zero','inverse_row','coprime_product') for r in ('all','head','tail') for w in ('one','X','defect_kernel','child_rowmass') for m in ('one','anchor','prefix')]
 r +=[dict(family='gcd_product',region=a,weight=w,multiplier='one') for a in ('all','head','tail') for w in ('one','X','defect_kernel','child_rowmass')]
 r +=[dict(family='unit',region='all',weight='one',multiplier=m) for m in ('one','anchor','global_prefix')]
 return dict(square=[dict(d,id=digest(d)) for d in s],relation=[dict(d,id=digest(d)) for d in r])
def build(program,X):
 target=program['target'];q=program['q'];C=F(program['C']);N=4*X-1;dictionary=descriptors();pref=[{(i,):F(1) for i in range(1,n+1)} for n in range(N+1)];fac={i:[[p,e] for p,e in sorted(P.factor(i).items())] for i in range(1,N+1)}
 def K(Y,t):return sum(n>=t for n in range(Y,2*Y))
 def J(t):return K(2*X,t)-4*K(X,t)
 def mass(i):return sum(n for n in range(2*X,4*X) if n>=i)
 def region(r,i):return r=='all' or r=='head' and i<=2*X or r=='tail' and i>2*X or r=='initial' and i<X or r=='parent' and X<=i<2*X or r=='child' and 2*X<=i<4*X
 sq=[]
 for d in dictionary['square']:
  f=d['family'];group=[]
  if f=='constant':group=[dict(weight=str(X*X*rootceil(X,q)),poly=[dict(m=[],c='1')])]
  elif f in ('coordinate','prefix','divisor_row'):
   for i in range(2 if f=='divisor_row' else 1,N+1):
    if not region(d['region'],i):continue
    p={(i,):F(1)} if f=='coordinate' else pref[i] if f=='prefix' else {(j,):F(1) for j in range(1,i+1) if i%j==0};w=1 if d['weight']=='one' else X if d['weight']=='X' else X*X;group.append(dict(weight=str(w),poly=P.canonical(p)))
  else:
   for a in range(1,N+1):
    for b in range(a+1,N+1):
     domain=d['domain']
     if domain=='coprime' and gcd(a,b)!=1 or domain=='noncoprime' and gcd(a,b)==1 or domain=='divides' and b%a:continue
     p=P.add({(a,):F(1)},{(b,):F(d['sign'])}) if f=='pair' else {(a,b):F(1)};w=1 if d['weight']=='one' else K(2*X,b) if d['weight']=='child_kernel' else abs(J(b));group.append(dict(weight=str(w),poly=P.canonical(p)))
  sq.append(group)
 specs={f:[] for f in ('norm','prime_power','squarefree_zero','inverse_row','coprime_product','gcd_product','unit')};specs['unit']=[dict(kind='unit')]
 for i in range(1,N+1):
  specs['norm'].append(dict(kind='norm',n=i,factors=fac[i]))
  if len(fac[i])==1:p,e=fac[i][0];specs['prime_power'].append(dict(kind='prime_power',p=p,e=e))
  if target=='mu' and any(e>1 for p,e in fac[i]):specs['squarefree_zero'].append(dict(kind='squarefree_zero',n=i))
  if target=='mu' and i>=2:specs['inverse_row'].append(dict(kind='inverse_row',n=i))
 for a in range(1,N+1):
  for b in range(a,N+1):
   specs['gcd_product'].append(dict(kind='gcd_product',a=a,b=b,factors_a=fac[a],factors_b=fac[b]))
   if a>=2 and a*b<=N and gcd(a,b)==1:specs['coprime_product'].append(dict(kind='coprime_product',a=a,b=b))
 rel=[]
 for d in dictionary['relation']:
  group=[]
  for s in specs[d['family']]:
   k=s['kind'];i=s['a']*s['b'] if k=='coprime_product' else max(s['a'],s['b']) if k=='gcd_product' else s['p']**s['e'] if k=='prime_power' else s.get('n',1)
   if not region(d['region'],i):continue
   w=1 if d['weight']=='one' else X if d['weight']=='X' else J(i) if d['weight']=='defect_kernel' else mass(i);m=d['multiplier'];p={():F(1)} if m=='one' else {(i,):F(1)} if m=='anchor' else pref[-1] if m=='global_prefix' else pref[i];group.append(dict(spec=s,multiplier=P.canonical({m:v*w for m,v in p.items()})))
  rel.append(group)
 critical=C*X*X*rootceil(X,q);unsigned=sum(mass(i)*(int(all(e==1 for p,e in fac[i])) if target=='mu' else 4**len(fac[i])) for i in range(1,N+1));D=critical if program['claim']=='critical' else unsigned;lhs=P.canonical(P.add({():F(D)},P.parse(P.complete_defect(X),N),F(-1)))
 return dict(instance=dict(target=target,horizon=N,lhs=lhs,square_groups=sq,relation_groups=rel),square_ids=[d['id'] for d in dictionary['square']],relation_ids=[d['id'] for d in dictionary['relation']],D=str(D),critical_budget=str(critical),unsigned_bound=str(unsigned),X=X,q=q,C=str(C),claim=program['claim'],dictionary_sha256=digest(dictionary))
def residual(instance,weights):
 lhs,sq,rel=G.columns(instance);rhs={}
 for w,c in zip(map(F,weights['square_weights']),sq):rhs=P.add(rhs,c,w)
 for w,c in zip(map(F,weights['relation_weights']),rel):rhs=P.add(rhs,c,w)
 return P.add(lhs,rhs,F(-1))
def truth(b):
 X=b['X'];N=4*X-1;t=b['instance']['target'];a=[0]*(N+1);a[1]=1
 for n in range(2,N+1):
  f=P.factor(n);a[n]=(0 if any(e>1 for e in f.values()) else (-1)**len(f)) if t=='mu' else 2**len(f)*(-1)**sum(f.values())
 pref=[sum(a[:i+1]) for i in range(N+1)];delta=sum(pref[i]**2 for i in range(2*X,4*X))-4*sum(pref[i]**2 for i in range(X,2*X));return dict(X=X,target=t,Delta=delta,D=b['D'],slack=str(F(b['D'])-delta),bound_true=F(b['D'])>=delta,verifier_only=True)

CODE=['grouped_arithmetic_language.py','test_grouped_arithmetic_language.py','grouped_arithmetic_proof.txt','grouped_arithmetic_synthesis.py','test_grouped_arithmetic_synthesis.py','grouped_arithmetic_templates.py','test_grouped_arithmetic_templates.py','check_grouped_arithmetic.py','test_check_grouped_arithmetic.py','run_grouped_arithmetic.py','test_run_grouped_arithmetic.py','check_grouped_arithmetic_run.py','test_check_grouped_arithmetic_run.py','arithmetic_cycle_language.py','arithmetic_cycle_synthesis.py','check_arithmetic_cycle_certificate.py','arithmetic_cycle_uniform_extension_design.txt','critical_defect_proof.txt','signed_arithmetic_proof.txt','arithmetic_cycle_synthesis_scope.txt']
LIMITS=dict(max_columns=1024,max_monomials=20000,max_operations=200000000,max_coefficient_bits=2048,max_horizon=4096,max_degree=12,max_denominator=1000000,time_limit=30)
def programs():return [dict(target=t,q=q,C=c,claim='critical',allow_constant_slack=True) for t,q,c in itertools.product(('mu','c'),(2,6),(8,32))]+[dict(target=t,q=2,C=1,claim='unsigned_calibration',allow_constant_slack=False) for t in ('mu','c')]
def check_built(actual,expected):
 for k,v in expected.items():require(actual[k]==v,'independent template '+k)
def audit_run(directory):
 d=Path(directory);names=['protocol.json','source_seal.json','seal.json','tests.json','training.json','candidate_seal.json','final_cases.json','final.json','producer_receipt.json'];initial={n:sha(d/n) for n in names};spec=read(d/'protocol.json');source=read(d/'source_seal.json');seal=read(d/'seal.json');training=read(d/'training.json');final=read(d/'final.json');cs=read(d/'candidate_seal.json');fc=read(d/'final_cases.json');receipt=read(d/'producer_receipt.json')
 require(set(source['hashes'])==set(CODE),'exact source manifest');require(seal==dict(protocol_sha256=initial['protocol.json'],source_seal_sha256=initial['source_seal.json']),'source/protocol seal')
 for n,h in source['hashes'].items():require(sha(d/'frozen_source'/n)==h and sha(Path(__file__).parent/n)==h,'source binding '+n)
 require(spec['programs']==programs() and spec['training_scales']==[1,2,4,5] and spec['final_fixed_scale']==8 and spec['final_odd_choices']==[9,11] and spec['limits']==LIMITS and spec['dictionary']==descriptors(),'fixed protocol contract');require(spec['tests']==[Path(n).stem for n in CODE if n.startswith('test_')],'test coverage')
 prior=spec['prior_verification'];require(prior['path']=='arithmetic-cycle-results/pilot-001/independent_verification.json' and sha(Path(__file__).parent/prior['path'])==prior['sha256'],'prior binding');tests=read(d/'tests.json');require(tests['returncode']==0 and re.search(r'Ran \d+ tests? in .*\n\s*OK\s*$',tests['stdout']+tests['stderr']),'successful contracts')
 selection=digest(dict(programs=programs(),dictionary=descriptors(),training_scales=[1,2,4,5]));require(cs==dict(training_sha256=initial['training.json'],protocol_sha256=initial['protocol.json'],selection_sha256=selection),'candidate seal');scales=[8,[9,11][int(selection,16)%2]];require(fc==dict(scales=scales,candidate_seal_sha256=initial['candidate_seal.json'],no_refitting=True),'final derived cases')
 require([a['program'] for a in training['attempts']]==programs() and [a['program'] for a in final['results']]==programs(),'all programs retained');diagnostics=[];counts={}
 for a,f in zip(training['attempts'],final['results']):
  program=a['program'];flag=program['allow_constant_slack'];expected=[build(program,X) for X in [1,2,4,5]]
  require(len(a['instances'])==4,'training instance coverage')
  for b,e in zip(a['instances'],expected):check_built(b,e);diagnostics.append(dict(phase='training',program=program,**truth(e)))
  result=a['synthesis'];G.verify_joint_result([e['instance'] for e in expected],result,allow_constant_slack=flag)
  if a['dual'] is not None and a['dual'].get('certified'):G.verify_joint_dual([e['instance'] for e in expected],a['dual'],allow_constant_slack=flag)
  require(f['refitted'] is False,'no final refitting')
  if result['status']!='finite_certificate':require(f['status']=='no_candidate' and f['observations']==[],'no candidate never pass');counts['no_candidate']=counts.get('no_candidate',0)+1;continue
  require(f['status']=='evaluated' and f['weights_sha256']==digest(result['weights']) and [o['X'] for o in f['observations']]==scales,'fixed transferred weight binding')
  for o in f['observations']:
   e=build(program,o['X']);check_built(o['instance'],e);diagnostics.append(dict(phase='final',program=program,**truth(e)));r=residual(e['instance'],result['weights']);valid=not any(m for m in r) and (r.get((),F(0))>=0 if flag else not r);status=o['status']
   if status=='finite_certificate':
    require(valid,'invalid transferred polynomial');G.verify_joint([e['instance']],**result['weights'],allow_constant_slack=flag);G.verify_joint_result([e['instance']],dict(status='finite_certificate',weights=result['weights'],certificates=[o['certificate']],constant_slacks=[str(r.get((),F(0)))]),allow_constant_slack=flag)
   elif status=='template_mismatch':require(not valid,'mismatch without exact residual witness')
   elif status=='missing_resource':require(isinstance(o.get('reason'),str) and bool(o['reason']),'missing resource reason')
   else:raise ValueError('final outcome status')
   counts[status]=counts.get(status,0)+1
 require(receipt['training_sha256']==initial['training.json'] and receipt['final_sha256']==initial['final.json'] and receipt['tests_sha256']==initial['tests.json'] and receipt['source_seal_sha256']==initial['source_seal.json'] and receipt['all_programs_retained']==10,'producer receipt')
 require(spec['historical_coefficient_overlap'] is True and spec['unseen_prime_holdout'] is False,'overlap provenance')
 def unproved(x):
  if isinstance(x,dict):
   for k,v in x.items():
    if k in ('RH_proved','global_critical_bound_proved','global_bound_proved'):require(v is False,'global promotion')
    unproved(v)
  elif isinstance(x,list):
   for v in x:unproved(v)
 for x in (spec,training,final,receipt):unproved(x)
 require({n:sha(d/n) for n in names}==initial,'inputs changed')
 for n,h in source['hashes'].items():require(sha(d/'frozen_source'/n)==h and sha(Path(__file__).parent/n)==h,'source changed')
 return dict(schema=1,all_passed=True,input_sha256=initial,code_sha256=source['hashes'],outcome_counts=counts,actual_post_search_diagnostics=diagnostics,independent_templates_reconstructed=True,actual_responses_supplied_to_learner=False,finite_only=True,global_critical_bound_proved=False,RH_proved=False)
if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('run');args=p.parse_args();out=Path(args.run)/'independent_verification.json'
 if out.exists():raise FileExistsError('independent verification exists')
 r=audit_run(args.run)
 with out.open('x') as f:json.dump(r,f,indent=2,sort_keys=True);f.write('\n')

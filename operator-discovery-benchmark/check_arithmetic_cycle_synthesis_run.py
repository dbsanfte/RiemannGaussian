"""Independent finite cycle synthesis artifact checks; no producer imports."""
import hashlib,json,argparse
from pathlib import Path
from fractions import Fraction as F
import check_arithmetic_cycle_certificate as mathcheck

CODE=['arithmetic_cycle_language.py','test_arithmetic_cycle_language.py','check_arithmetic_cycle_certificate.py','test_check_arithmetic_cycle_certificate.py','arithmetic_cycle_synthesis.py','test_arithmetic_cycle_synthesis.py','arithmetic_cycle_controls.py','test_arithmetic_cycle_controls.py','run_arithmetic_cycle_synthesis.py','test_run_arithmetic_cycle_synthesis.py','check_arithmetic_cycle_synthesis_run.py','test_check_arithmetic_cycle_synthesis_run.py','arithmetic_cycle_synthesis_scope.txt','prime_pair_forcing_next_certificate_scope.txt','prime_pair_forcing_next_certificate_review.txt','critical_defect_proof.txt','signed_arithmetic_proof.txt']
LIMITS=dict(max_columns=1024,max_monomials=10000,max_operations=200000000,max_horizon=4096,max_coefficient_bits=2048,max_denominator=1000000,time_limit=10)
def verify_template_solution(template,syn,target,H):
 M=mathcheck;lhs=M.parse(template['lhs'],H);squares=[M.parse(p,H) for p in template['square_basis']];groups=template['relation_columns'];columns=[M.multiply(p,p) for p in squares]
 for group in groups:
  col={}
  for term in group:col=M.add(col,M.multiply(M.parse(term['multiplier'],H),M.relation(term['spec'],target,H)))
  columns.extend([col,{m:-v for m,v in col.items()}])
 cert=syn['certificate'];require(cert['target']==target and cert['horizon']==H and cert['lhs']==template['lhs'],'solution target binding');M.verify_certificate(cert)
 weights=list(map(M.rational,syn['solver_diagnostics']['exact_lp_weights']));require(len(weights)==len(columns) and all(w>=0 for w in weights),'nonnegative exact template weights');rhs={}
 for w,col in zip(weights,columns):rhs=M.add(rhs,col,w)
 require(rhs==lhs,'solution exact template columns');signed=[weights[len(squares)+2*i]-weights[len(squares)+2*i+1] for i in range(len(groups))];require(list(map(str,signed))==syn['solver_diagnostics']['signed_relation_weights'],'signed solution weights')
 ss=[dict(weight=str(w),poly=p) for w,p in zip(weights,template['square_basis']) if w];rr=[]
 for w,g in zip(signed,groups):
  if w:
   for t in g:rr.append(dict(spec=t['spec'],multiplier=M.canonical({m:w*v for m,v in M.parse(t['multiplier'],H).items()})))
 require(cert['squares']==ss and cert['relations']==rr,'exact certificate template reconstruction')
def verify_calibration(cal):
 M=mathcheck;basis=[[dict(m=[],c='1')],[dict(m=[2],c='1')],[dict(m=[3],c='1')],[dict(m=[6],c='1')],[dict(m=[2,3],c='1')]];groups=[[dict(spec=dict(kind='coprime_product',a=2,b=3),multiplier=p)] for p in basis];lhs=[dict(m=[2,3,6],c='1')]
 require(cal['lhs']==lhs and cal['square_basis']==basis and cal['relation_columns']==groups,'supplied calibration template')
 if cal['synthesis']['status']=='finite_certificate':verify_template_solution(dict(lhs=lhs,square_basis=basis,relation_columns=groups),cal['synthesis'],'mu',6)
 else:require(cal['synthesis']['status'] in ('no_certificate_found','missing_resource'),'calibration status')
def require(x,msg):
 if not x:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def rootceil(X,q):
 mathcheck.integer(X);mathcheck.integer(q)
 if X==1:return 1
 if q>=X.bit_length():return 2
 lo,hi=1,X
 while hi-lo>1:
  m=(lo+hi)//2
  if m**q>=X:hi=m
  else:lo=m
 return hi

def verify_attempt(attempt):
 case=attempt['case'];template=attempt['template'];syn=attempt['synthesis'];target=case['target'];X=case['X'];q=case['q'];C=F(case['C']) if type(case['C'])is int else mathcheck.rational(case['C']);D=C*X*X*rootceil(X,q)
 require(C>=0,'negative bound');N=4*X-1;H=template.get('horizon',N*N)
 lhs=mathcheck.parse(template['lhs'],H);expected=mathcheck.add({():D},mathcheck.parse(mathcheck.complete_defect(X),H),F(-1));require(lhs==expected,'template full defect mismatch')
 squares=[mathcheck.parse(p,H) for p in template['square_basis']];groups=template['relation_columns'];columns=[mathcheck.multiply(p,p) for p in squares]
 for group in groups:
  require(type(group)is list and len(group)>0,'nonempty grouped relation');col={}
  for term in group:col=mathcheck.add(col,mathcheck.multiply(mathcheck.parse(term['multiplier'],H),mathcheck.relation(term['spec'],target,H)))
  columns.extend([col,{m:-v for m,v in col.items()}])
 status=syn['status'];require(status in ('finite_certificate','no_certificate_found','missing_resource'),'synthesis status')
 if status=='finite_certificate':
  cert=syn['certificate'];require(cert['horizon']==H and cert['target']==target,'certificate target/horizon')
  checked=mathcheck.verify_defect_certificate(cert,X,str(D));diag=syn['solver_diagnostics'];weights=list(map(mathcheck.rational,diag['exact_lp_weights']))
  require(len(weights)==len(columns) and all(w>=0 for w in weights),'exact nonnegative LP columns');rhs={}
  for w,col in zip(weights,columns):rhs=mathcheck.add(rhs,col,w)
  require(rhs==lhs,'template column match');signed=[weights[len(squares)+2*i]-weights[len(squares)+2*i+1] for i in range(len(groups))]
  require(list(map(str,signed))==diag['signed_relation_weights'],'signed relation weights')
  expected_squares=[dict(weight=str(w),poly=p) for w,p in zip(weights,template['square_basis']) if w]
  expected_relations=[]
  for w,group in zip(signed,groups):
   if w:
    for term in group:expected_relations.append(dict(spec=term['spec'],multiplier=mathcheck.canonical({m:w*v for m,v in mathcheck.parse(term['multiplier'],H).items()})))
  require(cert['squares']==expected_squares and cert['relations']==expected_relations,'certificate uses exact declared template')
  return dict(status=status,finite_verified=True,target_horizon=N,product_horizon=H,global_bound_proved=False)
 require('certificate' not in syn,'failed solve carries certificate');return dict(status=status,finite_verified=False,global_bound_proved=False)

def no_promotions(x):
 if isinstance(x,dict):
  for k,v in x.items():
   if k in ('RH_proved','global_bound_proved','actual_all_scale_signed_bound_proved'):require(v is False,'global promotion')
   no_promotions(v)
 elif isinstance(x,list):
  for v in x:no_promotions(v)

def counterfeit(N,P):
 require(type(P)is list and len(set(P))==len(P),'prime subset');require(all(mathcheck.prime(p) for p in P),'actual prime subset');P=set(P);out=[0]*(N+1);out[1]=1
 for n in range(2,N+1):
  factors=mathcheck.factor(n);out[n]=0 if any(e>1 for e in factors.values()) else (-1)**sum(p in P for p in factors)
 return out

def independent_template(case):
 X=case['X'];N=4*X-1;target=case['target'];D=F(case['C'])*X*X*rootceil(X,case['q']);M=mathcheck
 lhs=M.canonical(M.add({():D},M.parse(M.complete_defect(X),N),F(-1)));prefixes=[{(i,):F(1) for i in range(1,n+1)} for n in range(1,N+1)]
 basis=[{():F(1)}]+[{(i,):F(1)} for i in range(1,N+1)]+prefixes+[M.add({(i,):F(1)},{(i+1,):F(sign)}) for i in range(1,N) for sign in (1,-1)]
 seen={};square_archive=[]
 for poly in basis:
  serial=M.canonical(poly);key=digest(serial);alias=key in seen;square_archive.append(dict(sha256=key,alias_of=key if alias else None))
  if not alias:seen[key]=serial
 squares=list(seen.values());specs=[dict(kind='unit')]
 for p in range(2,N+1):
  if not M.prime(p):continue
  e=1;k=p
  while k<=N:specs.append(dict(kind='prime_power',p=p,e=e));e+=1;k*=p
 if target=='mu':specs +=[dict(kind='squarefree_zero',n=n) for n in range(2,N+1) if any(e>1 for e in M.factor(n).values())]
 from math import gcd
 specs +=[dict(kind='coprime_product',a=a,b=b) for a in range(2,N+1) for b in range(a,N+1) if a*b<=N and gcd(a,b)==1]
 if target=='mu':specs +=[dict(kind='inverse_row',n=n) for n in range(2,N+1)]
 def anchor(s):
  if s['kind']=='unit':return 1
  if 'n' in s:return s['n']
  if s['kind']=='coprime_product':return s['a']*s['b']
  return s['p']**s['e']
 raw=[]
 if case['mode']=='atomic_local':
  for spec in specs:
   for mult in ({():F(1)},{(anchor(spec),):F(1)},prefixes[-1]):raw.append([dict(spec=spec,multiplier=M.canonical(mult))])
 elif case['mode']=='grouped_cycles':
  groups={}
  for spec in specs:groups.setdefault(spec['kind'],[]).append(spec)
  for group in groups.values():
   for weight_kind in ('one','index','kernel'):
    for mk in ('one','anchor','prefix'):
     col=[]
     for spec in group:
      idx=anchor(spec)
      J=sum((w*sum(1 for n in range(lo,hi) if n>=idx) for lo,hi,w in ((X,2*X,-4),(2*X,4*X,1))))
      weight=F(1) if weight_kind=='one' else F(idx,N) if weight_kind=='index' else F(J,X)
      mult={():F(1)} if mk=='one' else {(idx,):F(1)} if mk=='anchor' else prefixes[idx-1]
      col.append(dict(spec=spec,multiplier=M.canonical({m:v*weight for m,v in mult.items()})))
     raw.append(col)
 else:raise ValueError('unsupported mode')
 seen={};archive=[]
 for col in raw:
  expanded={}
  for t in col:expanded=M.add(expanded,M.multiply(M.parse(t['multiplier'],N),M.relation(t['spec'],target,N)))
  key=digest(M.canonical(expanded));alias=key in seen;archive.append(dict(sha256=key,alias_of=key if alias else None,zero=not expanded))
  if not alias:seen[key]=col
 return dict(lhs=lhs,square_basis=squares,relation_columns=list(seen.values()),square_generation_archive=square_archive,column_generation_archive=archive,relations=specs,horizon=N,D=str(D))

def verify_controls(audit,spec):
 from math import gcd
 H=max(spec['pair_limit']**2,spec['row_limit'],max(4*X-1 for X in spec['scales']));f=counterfeit(H,spec['P']);P=set(spec['P']);pairs=zeros=0
 for a in range(1,spec['pair_limit']+1):
  for b in range(1,spec['pair_limit']+1):
   if gcd(a,b)!=1:continue
   pairs+=1;zeros+=f[a]*f[b]==0;require(f[a]*f[b]==f[a*b],'counterfeit coprime premise')
 powers=sum(1 for p in P for e in range(1,H.bit_length()+1) if p**e<=H)
 inverse=[n for n in range(1,spec['row_limit']+1) if any(n%p==0 for p in P)]
 require(all(sum(f[d] for d in range(1,n+1) if n%d==0)==0 for n in inverse),'partial inverse')
 mismatch=[dict(prime=p,counterfeit=f[p],actual_mu=-1) for p in range(2,H+1) if mathcheck.prime(p) and p not in P]
 energies=[]
 for X in spec['scales']:
  pref=[sum(f[:n+1]) for n in range(4*X)];AX=sum(pref[n]**2 for n in range(X,2*X));A2=sum(pref[n]**2 for n in range(2*X,4*X));energies.append(dict(X=X,A_X=AX,A_2X=A2,Delta=A2-4*AX,complete_horizon=4*X-1))
 expected=dict(P=sorted(P),pair_limit=spec['pair_limit'],row_limit=spec['row_limit'],horizon=H,coefficients_sha256=digest(f),ordered_coprime_pairs_checked=pairs,zero_cycle_pairs_checked=zeros,all_support_indices_checked=H,normalized_prime_powers_checked=powers,inverse_rows_checked=inverse,normalization_mismatches=mismatch,energies=energies)
 for k,v in expected.items():require(audit[k]==v,'counterfeit field '+k)
 require(audit['all_finite_premise_checks_passed'] is True and audit['scope']=='generic partial-prime premises, not actual mu','counterfeit scope')
 return dict(verified=True,nonactual_prime_mismatches=len(mismatch),horizon=H)

def cases(scales,protocol):return [dict(target=t,X=X,q=q,C=C,mode=m) for X in scales for t in protocol['targets'] for q in protocol['levels'] for C in protocol['constants'] for m in protocol['modes']]
def actual_truth(case):
 N=4*case['X']-1;f=[0]*(N+1);f[1]=1
 for n in range(2,N+1):
  fac=mathcheck.factor(n)
  if case['target']=='mu':f[n]=0 if any(e>1 for e in fac.values()) else (-1)**len(fac)
  else:f[n]=2**len(fac)*(-1)**sum(fac.values())
 X=case['X'];pref=[sum(f[:n+1]) for n in range(N+1)];AX=sum(pref[n]**2 for n in range(X,2*X));A2=sum(pref[n]**2 for n in range(2*X,4*X));delta=A2-4*AX;D=F(case['C'])*X*X*rootceil(X,case['q']);slack=D-delta
 return dict(target=case['target'],X=X,q=case['q'],C=case['C'],A_X=AX,A_2X=A2,Delta=delta,D=str(D),slack=str(slack),bound_true=slack>=0,finite_stored_bound_only=True)
def audit_run(run):
 d=Path(run);names=['protocol.json','source_seal.json','seal.json','development.json','candidate_seal.json','final_cases.json','final.json','verification.json','report.json'];initial={n:sha(d/n) for n in names}
 protocol=read(d/'protocol.json');source=read(d/'source_seal.json');seal=read(d/'seal.json');dev=read(d/'development.json');candidate=read(d/'candidate_seal.json');fc=read(d/'final_cases.json');final=read(d/'final.json');receipt=read(d/'verification.json')
 require(seal['protocol_sha256']==initial['protocol.json'] and seal['source_seal_sha256']==initial['source_seal.json'] and seal['sources_frozen_before_outcomes'] is True,'source/protocol seal')
 require(set(source['hashes'])==set(CODE),'exact frozen source manifest')
 expected=dict(development_scales=[1,2],final_fixed_scale=4,final_odd_choices=[5,7],targets=['mu','c'],levels=[2,6],constants=[1,4],modes=['atomic_local','grouped_cycles'],limits=LIMITS,controls=dict(P=[2],pair_limit=8,row_limit=64,scales=[1,2,4,8,16]))
 for k,value in expected.items():require(protocol[k]==value,'known frozen protocol '+k)
 for n in ('check_arithmetic_cycle_synthesis_run.py','check_arithmetic_cycle_certificate.py'):require(sha(Path(__file__).parent/n)==source['hashes'][n],'executed checker source binding')
 for n,h in source['hashes'].items():require(sha(d/'frozen_source'/n)==h,'frozen source '+n)
 require(candidate['development_sha256']==initial['development.json'] and candidate['parent_seal_sha256']==initial['seal.json'] and candidate['frozen_template_protocol_sha256']==initial['protocol.json'],'candidate seal')
 payload=[dict(case=a['case'],template_sha256=digest(a['template'])) for a in dev['attempts']];selection=digest(payload)
 require(candidate['selection_payload_sha256']==selection and candidate['selection_rule']=='canonical development case+template hashes, excludes solver outcomes/diagnostics/time' and candidate['byte_replay_guaranteed'] is False,'deterministic selection payload')
 require(protocol['final_selection_rule']=='canonical ordered development case+template hashes; solver diagnostics/outcomes/time excluded' and protocol['byte_replay_guaranteed'] is False,'selection protocol semantics')
 odd=protocol['final_odd_choices'][int(selection,16)%2];require(fc['selection_payload_sha256']==selection,'final selection binding');expected_final=cases([protocol['final_fixed_scale'],odd],protocol)
 require(fc['scales']==[4,odd] and fc['cases']==expected_final and fc['candidate_seal_sha256']==initial['candidate_seal.json'] and fc['generated_after_candidate_seal'] is True and fc['evaluation_mode']==protocol['final_semantics'],'postseal final derivation')
 require(protocol['development_cases']==cases(protocol['development_scales'],protocol),'development grid')
 audits=[];actual=[];groupcounts={}
 for phase,data,expected in (('development',dev,protocol['development_cases']),('final',final,expected_final)):
  require([a['case'] for a in data['attempts']]==expected,'completed attempts coverage')
  for a in data['attempts']:
   generated=independent_template(a['case'])
   for k,v in generated.items():require(a['template'][k]==v,'template generation '+k)
   result=verify_attempt(a);audits.append(result);truth=actual_truth(a['case']);truth.update(phase=phase,mode=a['case']['mode'],synthesis_status=result['status']);actual.append(truth)
   if result['finite_verified']:require(F(truth['slack'])>=0,'actual finite certificate contradiction')
   key=phase+':'+a['case']['target']+':'+a['case']['mode'];g=groupcounts.setdefault(key,dict(attempts=0,actual_bound_true=0,actual_bound_false=0,finite_certificates=0,true_bound_no_certificate=0));g['attempts']+=1;g['actual_bound_true']+=truth['bound_true'];g['actual_bound_false']+=not truth['bound_true'];g['finite_certificates']+=result['finite_verified'];g['true_bound_no_certificate']+=truth['bound_true'] and not result['finite_verified']
 require(final['fresh_template_synthesis'] is True and final['learned_coefficients_transferred'] is False,'final synthesis scope')
 require(dev['tests']['returncode']==0 and 'OK' in dev['tests']['stderr'],'frozen contract tests')
 control=verify_controls(dev['controls'],protocol['controls']);cal=dev['calibration']
 verify_calibration(cal)
 counts={s:sum(a['status']==s for a in audits) for s in ('finite_certificate','no_certificate_found','missing_resource')}
 require(receipt['source_seal_sha256']==initial['source_seal.json'] and receipt['protocol_sha256']==initial['protocol.json'] and receipt['candidate_seal_sha256']==initial['candidate_seal.json'] and receipt['end_source_hashes_verified'] is True,'producer source/input receipt')
 require(receipt['development_sha256']==initial['development.json'] and receipt['final_sha256']==initial['final.json'] and receipt['final_cases_sha256']==initial['final_cases.json'],'producer receipt bindings')
 require(receipt['counts']==counts and receipt['complete_attempts']==len(audits),'producer receipt counts')
 report=read(d/'report.json');require(report['counts']==counts and report['development_attempts']==len(dev['attempts']) and report['final_attempts']==len(final['attempts']),'report counts')
 for x in (protocol,dev,final,receipt,report):no_promotions(x)
 require({n:sha(d/n) for n in names}==initial,'inputs changed during audit')
 for n,h in source['hashes'].items():require(sha(d/'frozen_source'/n)==h,'source changed during audit')
 for n in ('check_arithmetic_cycle_synthesis_run.py','check_arithmetic_cycle_certificate.py'):require(sha(Path(__file__).parent/n)==source['hashes'][n],'executed checker changed')
 return dict(schema=1,all_passed=True,input_sha256=initial,code_sha256=source['hashes'],counts=counts,complete_attempts=len(audits),actual_post_synthesis_diagnostics=actual,grouped_actual_truth_counts=groupcounts,actual_truth_not_supplied_to_synthesis=True,finite_counterexamples_not_global_refutations=True,controls=control,template_generation_independently_reconstructed=True,exact_template_columns_independently_checked=True,producer_math_imported=False,LP_rerun=False,finite_only=True,global_bound_proved=False,RH_proved=False)
def main():
 p=argparse.ArgumentParser();p.add_argument('run');args=p.parse_args();d=Path(args.run);out=d/'independent_verification.json'
 if out.exists():raise FileExistsError('independent receipt exists')
 result=audit_run(d)
 with out.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
if __name__=='__main__':main()

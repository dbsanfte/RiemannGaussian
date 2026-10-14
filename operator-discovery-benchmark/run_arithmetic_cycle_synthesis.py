"""Bounded frozen finite cycle synthesis pilot. No global estimate admission."""
import argparse,hashlib,itertools,json,math,subprocess,sys,time
from pathlib import Path
from fractions import Fraction as F
import arithmetic_cycle_language as L
import arithmetic_cycle_synthesis as S
import arithmetic_cycle_controls as controls
import check_arithmetic_cycle_certificate as checker
ROOT=Path(__file__).resolve().parent
CODE=['arithmetic_cycle_language.py','test_arithmetic_cycle_language.py','check_arithmetic_cycle_certificate.py','test_check_arithmetic_cycle_certificate.py','arithmetic_cycle_synthesis.py','test_arithmetic_cycle_synthesis.py','arithmetic_cycle_controls.py','test_arithmetic_cycle_controls.py','run_arithmetic_cycle_synthesis.py','test_run_arithmetic_cycle_synthesis.py','check_arithmetic_cycle_synthesis_run.py','test_check_arithmetic_cycle_synthesis_run.py','arithmetic_cycle_synthesis_scope.txt','prime_pair_forcing_next_certificate_scope.txt','prime_pair_forcing_next_certificate_review.txt','critical_defect_proof.txt','signed_arithmetic_proof.txt']
LIMITS=dict(max_columns=1024,max_monomials=10000,max_operations=200000000,max_horizon=4096,max_coefficient_bits=2048,max_denominator=1000000,time_limit=10)
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def filehash(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,x):
 with p.open('x') as stream:stream.write(json.dumps(x,indent=2,sort_keys=True)+'\n')
def rootceil(X,q):
 if type(X)is not int or type(q)is not int or X<1 or q<1:raise ValueError('positive root domain')
 if X==1:return 1
 if q>=X.bit_length():return 2
 n=1
 while n**q<X:n+=1
 return n
def cases(scales):return [dict(target=t,X=X,q=q,C=C,mode=m) for X in scales for t in ('mu','c') for q in (2,6) for C in (1,4) for m in ('atomic_local','grouped_cycles')]
def template(case):
 if type(case)is not dict or set(case)!={'target','X','q','C','mode'} or case['target'] not in ('mu','c') or case['mode'] not in ('atomic_local','grouped_cycles') or any(type(case[k])is not int or case[k]<1 for k in ('X','q','C')):raise ValueError('exact template case domain')
 if case['X']>1024:raise OverflowError('bounded template source horizon')
 X=case['X'];N=4*X-1;target=case['target'];D=case['C']*X*X*rootceil(X,case['q']);lhs=L.add(L.constant(D),L.scale(L.complete_defect(X,max_terms=10000,max_operations=200000000),-1));prefix={};prefixes=[]
 for i in range(1,N+1):prefix=L.add(prefix,L.variable(i));prefixes.append(prefix)
 basis=[L.constant(1)]+[L.variable(i) for i in range(1,N+1)]+prefixes+[L.add(L.variable(i),L.scale(L.variable(i+1),sign)) for i in range(1,N) for sign in (1,-1)]
 def dedup(polys):
  seen={};archive=[]
  for p in polys:
   serial=L.dump_poly(p);key=digest(serial);alias=key in seen;archive.append(dict(sha256=key,alias_of=key if alias else None))
   if not alias:seen[key]=serial
  return list(seen.values()),archive
 square_basis,square_archive=dedup(basis);specs=[dict(kind='unit')]
 for p in range(2,N+1):
  if any(p%d==0 for d in range(2,math.isqrt(p)+1)):continue
  e=1;k=p
  while k<=N:specs.append(dict(kind='prime_power',p=p,e=e));e+=1;k*=p
 if target=='mu':
  specs +=[dict(kind='squarefree_zero',n=n) for n in range(2,N+1) if any(n%(d*d)==0 for d in range(2,math.isqrt(n)+1))]
 specs +=[dict(kind='coprime_product',a=a,b=b) for a in range(2,N+1) for b in range(a,N+1) if a*b<=N and math.gcd(a,b)==1]
 if target=='mu':specs +=[dict(kind='inverse_row',n=n) for n in range(2,N+1)]
 def anchor(s):return s.get('n',s['a']*s['b'] if s['kind']=='coprime_product' else s['p']**s['e'] if s['kind']=='prime_power' else 1)
 raw=[]
 if case['mode']=='atomic_local':
  for spec in specs:
   idx=anchor(spec)
   for multiplier in (L.constant(1),L.variable(idx),prefixes[-1]):raw.append([dict(spec=spec,multiplier=L.dump_poly(multiplier))])
 else:
  groups={}
  for spec in specs:groups.setdefault(spec['kind'],[]).append(spec)
  for kind,group in groups.items():
   for weight_kind in ('one','index','kernel'):
    for multiplier_kind in ('one','anchor','prefix'):
     column=[]
     for spec in group:
      idx=anchor(spec);weight=F(1) if weight_kind=='one' else F(idx,N) if weight_kind=='index' else F(max(0,4*X-max(2*X,idx))-4*max(0,2*X-max(X,idx)),X)
      multiplier=L.constant(1) if multiplier_kind=='one' else L.variable(idx) if multiplier_kind=='anchor' else prefixes[idx-1]
      column.append(dict(spec=spec,multiplier=L.dump_poly(L.scale(multiplier,weight))))
     raw.append(column)
 seen={};column_archive=[]
 for column in raw:
  expanded={}
  for term in column:expanded=L.add(expanded,L.mul(L.load_poly(term['multiplier']),L.relation(term['spec'],target,N),max_terms=10000,max_operations=200000000))
  key=digest(L.dump_poly(expanded));alias=key in seen;column_archive.append(dict(sha256=key,alias_of=key if alias else None,zero=not expanded))
  if not alias:seen[key]=column
 return dict(lhs=L.dump_poly(lhs),square_basis=square_basis,relation_columns=list(seen.values()),square_generation_archive=square_archive,column_generation_archive=column_archive,relations=specs,horizon=N,D=str(D),scope='Full original D-Delta retained; coprime relations ab<=N are a subset, not complete ordered cycle domain. Atomic local per-row relation coefficients are a calibration. Grouped relation columns share coefficients, but square weights remain index-specific. Finite representation search only, no uniform operator claim.')
def freeze(directory):
 directory=Path(directory)
 if directory.exists():raise ValueError('freeze directory must be new')
 missing=[name for name in CODE if not (ROOT/name).is_file()]
 if missing:raise ValueError('missing freeze sources '+str(missing))
 directory.mkdir(parents=True);(directory/'frozen_source').mkdir()
 hashes={}
 for name in CODE:
  data=(ROOT/name).read_bytes();(directory/'frozen_source'/name).write_bytes(data);hashes[name]=filehash(ROOT/name)
 protocol=dict(schema=1,development_scales=[1,2],final_fixed_scale=4,final_odd_choices=[5,7],targets=['mu','c'],levels=[2,6],constants=[1,4],modes=['atomic_local','grouped_cycles'],limits=LIMITS,development_cases=cases([1,2]),template_generator='complete symbolic D-Delta; all original coefficient variables, no actual response arrays',final_selection_rule='canonical ordered development case+template hashes; solver diagnostics/outcomes/time excluded',byte_replay_guaranteed=False,final_semantics='fresh synthesis learns new weights from a frozen template generator at new horizons; new-instance finite feasibility ONLY, not learned-coefficient transfer or all-scale generalization',calibration='supplied coprime cycle x2*x3*x6; generic basis and synthesis',controls=dict(P=[2],pair_limit=8,row_limit=64,scales=[1,2,4,8,16]),global_bound_proved=False,RH_proved=False)
 write(directory/'protocol.json',protocol);write(directory/'source_seal.json',dict(schema=1,hashes=hashes));write(directory/'seal.json',dict(protocol_sha256=filehash(directory/'protocol.json'),source_seal_sha256=filehash(directory/'source_seal.json'),sources_frozen_before_outcomes=True))
 return directory
def attempt(case,limits):
 t=template(case);result=S.synthesize(case['target'],t['horizon'],t['lhs'],t['square_basis'],t['relation_columns'],**limits);check=None
 diagnostics=result.get('solver_diagnostics',{})
 if diagnostics.get('float_weights') is not None:
  weights=diagnostics.pop('float_weights');diagnostics['float_weight_count']=len(weights);diagnostics['float_weights_sha256']=digest(weights);diagnostics['float_proposed_nonzero']=[dict(index=i,weight=v) for i,v in enumerate(weights) if v>1e-9]
 if result['status']=='finite_certificate':check=checker.verify_defect_certificate(result['certificate'],case['X'],t['D'])
 return dict(case=case,template=t,synthesis=result,independent_check=check,global_bound_proved=False)
def calibration(limits):
 basis=[L.constant(1),L.variable(2),L.variable(3),L.variable(6),L.mul(L.variable(2),L.variable(3))];lhs=L.dump_poly(L.mul(L.mul(L.variable(2),L.variable(3)),L.variable(6)));spec=dict(kind='coprime_product',a=2,b=3);columns=[[dict(spec=spec,multiplier=L.dump_poly(p))] for p in basis];result=S.synthesize('mu',6,lhs,[L.dump_poly(p) for p in basis],columns,**limits)
 return dict(scope='supplied calibration target, not discovered arithmetic estimate',lhs=lhs,square_basis=[L.dump_poly(p) for p in basis],relation_columns=columns,synthesis=result,independent_check=checker.verify_certificate(result['certificate']) if result['status']=='finite_certificate' else None)
def run(directory):
 directory=Path(directory);protocol=json.loads((directory/'protocol.json').read_text());seal=json.loads((directory/'seal.json').read_text());sources=json.loads((directory/'source_seal.json').read_text())
 if (directory/'development.json').exists():raise ValueError('run outputs already exist')
 if seal['protocol_sha256']!=filehash(directory/'protocol.json') or seal['source_seal_sha256']!=filehash(directory/'source_seal.json'):raise ValueError('seal mismatch')
 for name,h in sources['hashes'].items():
  if filehash(ROOT/name)!=h or filehash(directory/'frozen_source'/name)!=h:raise ValueError('frozen source mismatch '+name)
 tests=subprocess.run([sys.executable,'-m','unittest','test_arithmetic_cycle_language','test_check_arithmetic_cycle_certificate','test_arithmetic_cycle_synthesis','test_arithmetic_cycle_controls','test_run_arithmetic_cycle_synthesis','test_check_arithmetic_cycle_synthesis_run'],cwd=ROOT,capture_output=True,text=True,timeout=120)
 if tests.returncode:raise ValueError('frozen tests failed '+tests.stdout+tests.stderr)
 dev=dict(schema=1,attempts=[attempt(case,protocol['limits']) for case in protocol['development_cases']],calibration=calibration(protocol['limits']),controls=controls.audit_counterfeit(**protocol['controls']),tests=dict(returncode=tests.returncode,stdout=tests.stdout,stderr=tests.stderr),global_bound_proved=False,RH_proved=False)
 write(directory/'development.json',dev);print('development phase completed: '+str(len(dev['attempts']))+' attempts',flush=True)
 selection_payload=[dict(case=a['case'],template_sha256=digest(a['template'])) for a in dev['attempts']];selection_digest=digest(selection_payload)
 write(directory/'candidate_seal.json',dict(development_sha256=filehash(directory/'development.json'),parent_seal_sha256=filehash(directory/'seal.json'),frozen_template_protocol_sha256=filehash(directory/'protocol.json'),selection_payload_sha256=selection_digest,selection_rule='canonical development case+template hashes, excludes solver outcomes/diagnostics/time',byte_replay_guaranteed=False))
 odd=protocol['final_odd_choices'][int(selection_digest,16)%2];final_cases=dict(scales=[4,odd],cases=cases([4,odd]),candidate_seal_sha256=filehash(directory/'candidate_seal.json'),generated_after_candidate_seal=True,selection_payload_sha256=selection_digest,evaluation_mode=protocol['final_semantics']);write(directory/'final_cases.json',final_cases)
 final=dict(schema=1,attempts=[attempt(case,protocol['limits']) for case in final_cases['cases']],fresh_template_synthesis=True,learned_coefficients_transferred=False,global_bound_proved=False,RH_proved=False);write(directory/'final.json',final);print('final phase completed: '+str(len(final['attempts']))+' attempts',flush=True)
 if seal['protocol_sha256']!=filehash(directory/'protocol.json') or seal['source_seal_sha256']!=filehash(directory/'source_seal.json'):raise ValueError('end-of-run seal mismatch')
 for name,h in sources['hashes'].items():
  if filehash(ROOT/name)!=h or filehash(directory/'frozen_source'/name)!=h:raise ValueError('end-of-run source mismatch '+name)
 all_attempts=dev['attempts']+final['attempts'];counts={s:sum(a['synthesis']['status']==s for a in all_attempts) for s in ('finite_certificate','no_certificate_found','missing_resource')};write(directory/'verification.json',dict(end_source_hashes_verified=True,source_seal_sha256=filehash(directory/'source_seal.json'),protocol_sha256=filehash(directory/'protocol.json'),candidate_seal_sha256=filehash(directory/'candidate_seal.json'),finite_certificates_independently_checked=all(a['independent_check'] is not None for a in all_attempts if a['synthesis']['status']=='finite_certificate'),counts=counts,complete_attempts=len(all_attempts),development_sha256=filehash(directory/'development.json'),final_sha256=filehash(directory/'final.json'),final_cases_sha256=filehash(directory/'final_cases.json'),global_bound_proved=False,RH_proved=False));write(directory/'report.json',dict(schema=1,status='completed',counts=counts,development_attempts=len(dev['attempts']),final_attempts=len(final['attempts']),scope='finite symbolic certificates only; atomic coefficient encoding control, grouped representation search; no uniform template or RH proof',global_bound_proved=False,RH_proved=False))
 return counts
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('command',choices=['freeze','run']);parser.add_argument('directory');args=parser.parse_args();print(freeze(args.directory) if args.command=='freeze' else run(args.directory))

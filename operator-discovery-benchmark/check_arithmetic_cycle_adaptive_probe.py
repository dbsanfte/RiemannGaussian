"""Independent adaptive finite-cone trajectory checker, no producer imports."""
import json,hashlib,itertools
from pathlib import Path
from fractions import Fraction as F
import check_arithmetic_cycle_certificate as M
from check_arithmetic_cycle_separation import verify_separator,dot
from check_arithmetic_cycle_synthesis_run import verify_template_solution

def require(x,msg):
 if not x:raise ValueError(msg)
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def enumerated(template,y):
 N=template['horizon'];out=[]
 def emit(kind,p,payload,cost):
  missing=sorted(set(p)-set(y));v=None if missing else dot(p,y)
  out.append(dict(kind=kind,payload=payload,expanded=M.canonical(p),cost=cost,unsupported_monomials=[list(m) for m in missing],status='missing_dual_coordinates' if missing else 'evaluated',dual_score=None if v is None else str(v),witness=v is not None and (v<0 if kind=='square' else v!=0)))
 for degree in (1,2):
  for spec in template['relations']:
   r=M.relation(spec,'mu',N)
   for indices in itertools.combinations_with_replacement(range(1,N+1),degree):
    p=M.multiply({indices:F(1)},r);emit('relation',p,dict(spec=spec,multiplier=M.canonical({indices:F(1)})),dict(degree=degree,terms=len(p),index_sum=sum(indices)))
 for count in (1,2,3):
  for indices in itertools.combinations(range(1,N+1),count):
   for signs in itertools.product((-1,1),repeat=count-1):
    p={(i,):F(v) for i,v in zip(indices,(1,)+signs)};s=M.multiply(p,p);emit('square',s,dict(poly=M.canonical(p)),dict(degree=2,terms=len(s),index_sum=sum(indices)))
 return out
def ranking(rows):
 return sorted([r for r in rows if r['witness']],key=lambda r:(r['cost']['degree'],r['cost']['terms'],r['cost']['index_sum'],json.dumps(r['payload'],sort_keys=True,separators=(',',':'))))
def extend(t,chosen):
 t=json.loads(json.dumps(t))
 if chosen['kind']=='square':t['square_basis'].append(chosen['payload']['poly'])
 else:t['relation_columns'].append([chosen['payload']])
 return t

def audit_probe(directory,pilot):
 d=Path(directory);pilot=Path(pilot);spec=read(d/'spec.json');seal=read(d/'seal.json');results=read(d/'results.json');initial={n:sha(d/n) for n in ['spec.json','seal.json','results.json']}
 require(spec['max_promotions']==16 and spec['no_actual_coefficient_response'] is True,'predeclared adaptive budget/scope');require(initial['spec.json']==seal['spec_sha256'] and initial['seal.json']==results['seal_sha256'],'adaptive seal')
 for n,h in seal['source_hashes'].items():require(sha(d/'frozen_source'/n)==h,'frozen probe source')
 require(sha(pilot/'development.json')==spec['development_sha256'],'pilot binding');dev=read(pilot/'development.json');require([t['case'] for t in results['trajectories']]==spec['cases'],'trajectory case coverage');summaries=[]
 for trajectory,case,original_hash in zip(results['trajectories'],spec['cases'],spec['initial_template_sha256']):
  require(case==dict(target='mu',X=2,q=2,C=1,mode=case['mode']) and case['mode'] in ('atomic_local','grouped_cycles'),'exact finite calibration case')
  original=next(a['template'] for a in dev['attempts'] if a['case']==case);require(digest(original)==original_hash==trajectory['initial_template_sha256'],'initial template');current=original;steps=trajectory['iterations'];require(0<len(steps)<=16,'nonempty bounded iterations');stop=None;promotions=0
  for j,it in enumerate(steps):
   require(it['step']==j and it['current_template_sha256']==digest(current),'contiguous template transitions');require(stop is None,'iteration after terminal state');dual=it['dual']
   if not dual['certified']:
    require(it['chosen'] is None and it['resynthesis'] is None and not it['extension_tests'],'uncertified dual does not promote');stop='no_exact_separator';continue
   w=dict(dual);w['b_dot_y']=w['lhs_dot_y'];proof=verify_separator(current,'mu',w);rows=enumerated(original,proof['y']);ranked=ranking(rows)
   require(rows==it['extension_tests'] and ranked==it['ranked_witnesses'],'complete adaptive candidate enumeration')
   if not ranked:
    require(it['chosen'] is None and it['resynthesis'] is None,'no supported witness transition');stop='no_supported_witness';continue
   chosen=ranked[0];require(it['chosen']==chosen,'first deterministic supported witness');current=extend(current,chosen);promotions+=1;require(digest(current)==it['next_template_sha256'],'next template digest');syn=it['resynthesis'];require(syn['status'] in ('finite_certificate','missing_resource','no_certificate_found'),'primal status')
   if syn['status']=='finite_certificate':
    verify_template_solution(current,syn,'mu',7);M.verify_defect_certificate(syn['certificate'],2,'8');stop='finite_certificate'
   elif syn['status']=='missing_resource':stop='missing_resource'
  if stop is None:
   require(len(steps)==16,'unexplained early termination');stop='promotion_limit'
  require(trajectory['stop_reason']==stop and trajectory['promotions']==promotions and trajectory['final_template']==current and trajectory['final_template_sha256']==digest(current),'terminal trajectory')
  file=case['mode']+'-trajectory.json';require(read(d/file)==trajectory and sha(d/file)==results['trajectory_hashes'][case['mode']],'trajectory file binding')
  summaries.append(dict(mode=case['mode'],iterations=len(steps),promotions=promotions,terminal=stop,finite_bound_verified=stop=='finite_certificate',uniform_bound_proved=False))
 require(results['global_bound_proved'] is False and results['RH_proved'] is False,'no global promotion');require({n:sha(d/n) for n in initial}==initial,'artifacts changed during audit')
 for n,h in seal['source_hashes'].items():require(sha(d/'frozen_source'/n)==h,'probe source changed during audit')
 return dict(verified=True,trajectories=summaries,input_sha256=initial,finite_calibration_only=True,global_bound_proved=False,RH_proved=False)

"""Posthoc exact finite cone separator audit; no producer imports."""
from fractions import Fraction as F
import check_arithmetic_cycle_certificate as M

def require(x,msg):
 if not x:raise ValueError(msg)
def dot(poly,y):
 require(set(poly)<=set(y),'unsupported monomial; no implicit zero extension')
 return sum((v*y[m] for m,v in poly.items()),F(0))
def template_columns(template,target):
 H=template['horizon'];squares=[M.multiply(M.parse(p,H),M.parse(p,H)) for p in template['square_basis']];relations=[]
 for group in template['relation_columns']:
  r={}
  for t in group:r=M.add(r,M.multiply(M.parse(t['multiplier'],H),M.relation(t['spec'],target,H)))
  relations.append(r)
 return squares,relations

def verify_separator(template,target,witness):
 squares,relations=template_columns(template,target);lhs=M.parse(template['lhs'],template['horizon']);mons=[tuple(m) for m in witness['monomials']]
 require(mons==sorted(set(mons)),'canonical dual monomials');require(len(mons)==len(witness['weights']),'dual dimension')
 full=set(lhs)|{m for p in squares+relations for m in p};require(set(mons)==full,'complete dual domain')
 y=dict(zip(mons,map(M.rational,witness['weights'])));sd=[dot(p,y) for p in squares];rd=[dot(p,y) for p in relations];b=dot(lhs,y)
 require(all(v>=0 for v in sd) and all(v==0 for v in rd) and b<0,'exact cone separation')
 if 'b_dot_y' in witness:require(F(witness['b_dot_y'])==b,'recorded lhs dot')
 if 'columns_dot_y' in witness:
  expected=sd+[v for r in rd for v in (r,-r)];require(list(map(F,witness['columns_dot_y']))==expected,'recorded column dots')
 return dict(verified=True,y=y,square_dots=list(map(str,sd)),relation_dots=list(map(str,rd)),lhs_dot=str(b),scope='infeasibility of this exact finite supplied cone only',global_bound_proved=False,RH_proved=False)
def verify_candidate(poly,y,record,H):
 p=M.parse(poly,H);new=sorted(set(p)-set(y));require(record['newmonomials']==[list(m) for m in new],'new monomial record')
 if new:
  require(record['status'] in ('missing','unsupported_new_monomials'),'unsupported extension status');return None
 value=dot(p,y);require(F(record['dot'])==value,'candidate exact dual dot');return value

def audit_probe(directory,pilot):
 import json,hashlib,itertools
 from pathlib import Path
 def read(p):return json.loads(p.read_text())
 def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
 def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
 d=Path(directory);p=Path(pilot);spec=read(d/'spec.json');seal=read(d/'seal.json');results=read(d/'results.json');dev=read(p/'development.json');initial=sha(d/'results.json')
 require(sha(d/'spec.json')==seal['spec_sha256'] and sha(p/'development.json')==spec['development_sha256'],'probe spec/pilot binding');require(results['seal_sha256']==sha(d/'seal.json'),'results seal')
 for name,h in seal['source_hashes'].items():require(sha(d/'frozen_source'/name)==h,'probe frozen source')
 require([r['case'] for r in results['cases']]==spec['cases'],'case coverage');summaries=[]
 for rec,th in zip(results['cases'],spec['selected_template_sha256']):
  t=next(a['template'] for a in dev['attempts'] if a['case']==rec['case']);require(digest(t)==th==rec['template_sha256'],'template binding');w=dict(rec['dual']);w['b_dot_y']=w['lhs_dot_y'];checked=verify_separator(t,'mu',w);y=checked['y'];expected=[];N=t['horizon']
  def emit(kind,poly,payload,cost):
   new=sorted(set(poly)-set(y));v=None if new else dot(poly,y);witness=v is not None and (v<0 if kind=='square' else v!=0)
   expected.append(dict(kind=kind,payload=payload,expanded=M.canonical(poly),cost=cost,unsupported_monomials=[list(m) for m in new],status='missing_dual_coordinates' if new else 'evaluated',dual_score=None if v is None else str(v),witness=witness))
  for degree in (1,2):
   for rel in t['relations']:
    r=M.relation(rel,'mu',N)
    for indices in itertools.combinations_with_replacement(range(1,N+1),degree):
     mult={indices:F(1)};expanded=M.multiply(mult,r);emit('relation',expanded,dict(spec=rel,multiplier=M.canonical(mult)),dict(degree=degree,terms=len(expanded),index_sum=sum(indices)))
  for count in (1,2,3):
   for indices in itertools.combinations(range(1,N+1),count):
    for signs in itertools.product((-1,1),repeat=count-1):
     poly={(i,):F(v) for i,v in zip(indices,(1,)+signs)};expanded=M.multiply(poly,poly);emit('square',expanded,dict(poly=M.canonical(poly)),dict(degree=2,terms=len(expanded),index_sum=sum(indices)))
  require(expected==rec['extension_tests'],'complete candidate enumeration/expansion/dots')
  def key(r):return(r['cost']['degree'],r['cost']['terms'],r['cost']['index_sum'],json.dumps(r['payload'],sort_keys=True,separators=(',',':')))
  ranked=sorted([r for r in expected if r['witness']],key=key);require(ranked==rec['ranked_witnesses'] and rec['chosen']==(ranked[0] if ranked else None),'exact selection')
  syn=rec['resynthesis'];require(syn is not None and syn['status']=='no_certificate_found','expected extension outcome; no infeasibility assertion')
  summaries.append(dict(mode=rec['case']['mode'],lhs_dual_dot=checked['lhs_dot'],attempts=len(expected),unsupported=sum(r['status']=='missing_dual_coordinates' for r in expected),chosen=rec['chosen'],extension_status=syn['status']))
 require(sha(d/'results.json')==initial,'probe changed during audit')
 return dict(verified=True,cases=summaries,result_sha256=initial,finite_cone_only=True,global_bound_proved=False,RH_proved=False)

"""Posthoc cone-separation diagnosis; frozen before probe execution.
A dual separates a DECLARED finite certificate cone, not actual arithmetic truth.
"""
import argparse,hashlib,itertools,json,sys
from pathlib import Path
from fractions import Fraction as F
import arithmetic_cycle_language as L
import arithmetic_cycle_synthesis as S
import check_arithmetic_cycle_certificate as checker
ROOT=Path(__file__).resolve().parent
PILOT=ROOT/'arithmetic-cycle-results/pilot-001'
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def hashfile(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,x):
 with p.open('x') as f:f.write(json.dumps(x,indent=2,sort_keys=True)+'\n')
def expanded_columns(template):
 columns=[L.mul(L.load_poly(p),L.load_poly(p)) for p in template['square_basis']]
 for group in template['relation_columns']:
  p={}
  for term in group:p=L.add(p,L.mul(L.load_poly(term['multiplier']),L.relation(term['spec'],'mu',7)))
  columns.extend([p,L.scale(p,-1)])
 return columns

def dual(template):
 from scipy.optimize import linprog
 b=L.load_poly(template['lhs']);columns=expanded_columns(template);monomials=sorted(set(b)|{m for p in columns for m in p});result=linprog([float(b.get(m,F(0))) for m in monomials],A_ub=[[-float(p.get(m,F(0))) for m in monomials] for p in columns],b_ub=[0.0]*len(columns),bounds=[(-1,1)]*len(monomials),method='highs',options={'time_limit':10});record=dict(solver_status=int(result.status),message=str(result.message),float_objective=None if result.fun is None else float(result.fun),float_weights=None if result.x is None else list(map(float,result.x)),certified=False)
 if not result.success:return record
 for bound in (1,16,256,1000000):
  y={m:F(float(v)).limit_denominator(bound) for m,v in zip(monomials,result.x)};dots=[sum(y[m]*v for m,v in p.items()) for p in columns];bdot=sum(y[m]*v for m,v in b.items())
  if all(v>=0 for v in dots) and bdot<0:
   record.update(certified=True,monomials=[list(m) for m in monomials],weights=[str(y[m]) for m in monomials],columns_dot_y=list(map(str,dots)),lhs_dot_y=str(bdot),denominator_limit=bound,scope='exact separation of declared finite cone only; no arithmetic-bound refutation');return record
 return record

def candidate_extensions(template,y,spec):
 N=7;candidates=[];tests=[]
 def score(kind,p,payload,cost):
  unsupported=sorted(set(p)-set(y));value=None if unsupported else sum(y[m]*q for m,q in p.items());witness=value is not None and (value<0 if kind=='square' else value!=0)
  record=dict(kind=kind,payload=payload,expanded=L.dump_poly(p),cost=cost,unsupported_monomials=[list(m) for m in unsupported],status='missing_dual_coordinates' if unsupported else 'evaluated',dual_score=None if value is None else str(value),witness=witness);tests.append(record)
  if witness:candidates.append(record)
 relations=template['relations']
 for degree in (1,2):
  for rho in relations:
   for indices in itertools.combinations_with_replacement(range(1,N+1),degree):
    multiplier={indices:F(1)};p=L.mul(multiplier,L.relation(rho,'mu',N));score('relation',p,dict(spec=rho,multiplier=L.dump_poly(multiplier)),dict(degree=degree,terms=len(p),index_sum=sum(indices)))
 for count in (1,2,3):
  for indices in itertools.combinations(range(1,N+1),count):
   for signs in itertools.product((-1,1),repeat=count-1):
    coeffs=(1,)+signs;p={tuple([i]):F(c) for i,c in zip(indices,coeffs)};square=L.mul(p,p);score('square',square,dict(poly=L.dump_poly(p)),dict(degree=2,terms=len(square),index_sum=sum(indices)))
 def rank(r):return (r['cost']['degree'],r['cost']['terms'],r['cost']['index_sum'],json.dumps(r['payload'],sort_keys=True,separators=(',',':')))
 ranked=sorted(candidates,key=rank);return tests,ranked

def freeze(directory):
 directory=Path(directory)
 if directory.exists():raise ValueError('new unique probe directory required')
 dev=json.loads((PILOT/'development.json').read_text());selected=[a for a in dev['attempts'] if a['case']==dict(target='mu',X=2,q=2,C=1,mode=a['case']['mode'])];assert len(selected)==2
 directory.mkdir(parents=True);code=['arithmetic_cycle_separation_probe.py','arithmetic_cycle_language.py','arithmetic_cycle_synthesis.py','check_arithmetic_cycle_certificate.py'];(directory/'frozen_source').mkdir();hashes={}
 for name in code:(directory/'frozen_source'/name).write_bytes((ROOT/name).read_bytes());hashes[name]=hashfile(ROOT/name)
 spec=dict(schema=1,cases=[a['case'] for a in selected],development_sha256=hashfile(PILOT/'development.json'),selected_template_sha256=[digest(a['template']) for a in selected],extension_order='all declared whitelisted relation instances times every variable, then every degree2 monomial; sparse signed variable squares with1..3terms',ranking='degree,expandedtermcount,indexsum,canonicalpayload',max_denominator=1000000,dual_time_limit=10,posthoc=True,no_actual_coefficient_response=True,scope='development-conditioned cone diagnosis only; new finite coefficients never imply reusable global bound')
 write(directory/'spec.json',spec);write(directory/'seal.json',dict(spec_sha256=hashfile(directory/'spec.json'),source_hashes=hashes));return directory

def run(directory):
 directory=Path(directory);spec=json.loads((directory/'spec.json').read_text());seal=json.loads((directory/'seal.json').read_text());assert hashfile(directory/'spec.json')==seal['spec_sha256'] and hashfile(PILOT/'development.json')==spec['development_sha256']
 for name,h in seal['source_hashes'].items():assert hashfile(ROOT/name)==h==hashfile(directory/'frozen_source'/name)
 dev=json.loads((PILOT/'development.json').read_text());out=[]
 for case,template_hash in zip(spec['cases'],spec['selected_template_sha256']):
  t=next(a['template'] for a in dev['attempts'] if a['case']==case);assert digest(t)==template_hash;d=dual(t);record=dict(case=case,template_sha256=template_hash,dual=d,extension_tests=[],ranked_witnesses=[],chosen=None,resynthesis=None,independent_check=None)
  if d['certified']:
   y={tuple(m):F(v) for m,v in zip(d['monomials'],d['weights'])};tests,ranked=candidate_extensions(t,y,spec);record.update(extension_tests=tests,ranked_witnesses=ranked)
   if ranked:
    chosen=ranked[0];record['chosen']=chosen;squares=list(t['square_basis']);relations=list(t['relation_columns'])
    if chosen['kind']=='square':squares.append(chosen['payload']['poly'])
    else:relations.append([chosen['payload']])
    result=S.synthesize('mu',7,t['lhs'],squares,relations,max_columns=1024,max_monomials=10000,max_operations=200000000,max_coefficient_bits=2048,max_denominator=1000000,time_limit=10);record['resynthesis']=result
    if result['status']=='finite_certificate':record['independent_check']=checker.verify_defect_certificate(result['certificate'],2,'8')
  out.append(record);print(case['mode']+' dualcertified='+str(d['certified'])+' witnesses='+str(len(record['ranked_witnesses']))+' resynthesis='+str(None if record['resynthesis'] is None else record['resynthesis']['status']),flush=True)
 for name,h in seal['source_hashes'].items():assert hashfile(ROOT/name)==h==hashfile(directory/'frozen_source'/name)
 write(directory/'results.json',dict(schema=1,cases=out,seal_sha256=hashfile(directory/'seal.json'),posthoc=True,global_bound_proved=False,RH_proved=False));return out
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('command',choices=['freeze','run']);p.add_argument('directory');args=p.parse_args();freeze(args.directory) if args.command=='freeze' else run(args.directory)

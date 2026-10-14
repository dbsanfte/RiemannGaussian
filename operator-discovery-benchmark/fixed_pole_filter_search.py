"""Fixed pole-budget filter proposals. No run orchestration or global estimate.
All Gram moments are complete. Fitted coefficients/finite passes prove no bound.
"""
from fractions import Fraction as F
from itertools import combinations,product
import hashlib,json
import arithmetic_filter_pole_budget as arithmetic
from detector_safe_evaluation import rational_ceiling
DIVISORS=[1,2,3,4,5,6,7,8,9,12,16]
TARGETS=[dict(r=r,l=k-r) for k in (1,2,3) for r in range(k+1)]
LEVELS=[2,3,6,12]
TWO_WEIGHTS=['-4','-3','-2','-1','-1/2','1/2','1','2','3','4']
THREE_WEIGHTS=['-2','-1','1','2']
BOX=F(8)
QUANTIZATION_DENOMINATOR=64
DICTIONARY=dict(targets=TARGETS,divisors=DIVISORS,leading_divisor=1,leading_weight='1',two_weights=TWO_WEIGHTS,three_weights=THREE_WEIGHTS,support_limit='r+l',inference='one pooled normalized Gram constrained least-squares minimizer per one/two nonleading divisor support; exact interior/edges/corners; singular missing with explicit grid fallback',box='8',quantization_denominator=64,composition='for each d>1 with d^2 in dictionary and each two-weight w, square (1+w D_d): weights1,2w,w^2 at1,d,d^2; retain exact pole support admission')
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
DICTIONARY_SHA256=digest(DICTIONARY)
def _exact(x):
 if isinstance(x,(bool,float)):raise ValueError('exact rational required')
 return F(x)
def _scales(scales):
 scales=list(scales)
 if not scales or any(type(x) is not int or x<1 for x in scales):raise ValueError('positive integer scales required')
 return sorted(set(scales))
def _target(t):
 if not isinstance(t,dict) or set(t)!={'r','l'} or any(type(t[k]) is not int or t[k]<0 for k in ('r','l')) or not 1<=t['r']+t['l']<=3:raise ValueError('target requires exact nonnegative r,l with total arity1..3')
 return dict(r=t['r'],l=t['l'])
def covariance_table(prefix,scales,*,work_budget=100000000,use_numpy=True):
 cost=0
 try:
  scales=_scales(scales)
  if type(work_budget) is not int or work_budget<0 or type(use_numpy) is not bool:raise ValueError('invalid resource options')
  if any(type(x) is not int for x in prefix):raise ValueError('complete integer prefix required')
  if not prefix or prefix[0]:raise ValueError('zero prefix sentinel required')
  if len(prefix)<=2*max(scales)-1:raise ValueError('complete prefix lookahead required')
  cost+=len(prefix);maximum=max(map(abs,prefix));np=None
  if use_numpy:
   try:import numpy as np
   except ImportError:pass
  rows=[]
  for X in scales:
   charge=(len(DIVISORS)*(len(DIVISORS)+1)//2+len(DIVISORS))*X
   if cost+charge>work_budget:return dict(status='missing',value=None,cost=cost,reason='work budget exceeded; no truncated moments returned')
   cost+=charge
   fast=np is not None and maximum*maximum*X<2**63
   matrix=[[None]*len(DIVISORS) for _ in DIVISORS]
   if fast:
    a=np.array(prefix,dtype=np.int64);indices=np.arange(X,2*X,dtype=np.int64)
    columns=[a[indices//d] for d in DIVISORS]
   else:columns=[[prefix[n//d] for n in range(X,2*X)] for d in DIVISORS]
   for i in range(len(DIVISORS)):
    for j in range(i,len(DIVISORS)):
     z=int(np.dot(columns[i],columns[j])) if fast else sum(a*b for a,b in zip(columns[i],columns[j]))
     matrix[i][j]=matrix[j][i]=str(F(z,X*X))
   rows.append(dict(X=X,matrix=matrix,backend='numpy_int64_proved_safe' if fast else 'python_integer',int64_absolute_sum_bound=str(maximum*maximum*X),complete_block=True))
  return dict(status='available',value=dict(divisors=DIVISORS,moments=rows),cost=cost,reason=None,cost_scope='scalar products and allocation proxy; not bit complexity or serialization')
 except (ValueError,TypeError,OverflowError) as e:return dict(status='invalid',value=None,cost=cost,reason=str(e))
def build_dataset(base_scales,*,targets=TARGETS,work_budget=100000000,max_n=1048575,use_numpy=True):
 cost=0
 try:
  bases=_scales(base_scales);scales=sorted(set(bases)|{2*x for x in bases});N=4*max(bases)-1
  if type(work_budget) is not int or work_budget<0 or type(max_n) is not int or max_n<1:raise ValueError('invalid resource limits')
  if N>max_n:return dict(status='missing',value=None,cost=0,reason='lookahead limit',lookahead=N)
  records=[]
  for t in targets:
   t=_target(t);out=arithmetic.actual_coefficients(N,t['r'],t['l'],work_budget=work_budget-cost);cost+=out['cost']
   if out['status']!='available':return dict(status=out['status'],value=None,cost=cost,reason=out.get('reason'),lookahead=N)
   prefix=[0]
   if cost+N>work_budget:return dict(status='missing',value=None,cost=cost,reason='prefix work budget',lookahead=N)
   cost+=N
   for v in out['coefficients'][1:]:prefix.append(prefix[-1]+v)
   cov=covariance_table(prefix,scales,work_budget=work_budget-cost,use_numpy=use_numpy);cost+=cov['cost']
   if cov['status']!='available':return dict(status=cov['status'],value=None,cost=cost,reason=cov.get('reason'),lookahead=N)
   records.append(dict(target=t,coefficients=out['coefficients'],prefix=prefix,**cov['value']))
  return dict(status='available',value=dict(base_scales=bases,scales=scales,targets=records,dictionary_sha256=DICTIONARY_SHA256,provenance='complete actual mu/lambda prime sieve and generic full Dirichlet convolution; no new historical coefficient holdout',global_bound_proved=False),cost=cost,lookahead=N,reason=None)
 except (ValueError,TypeError) as e:return dict(status='invalid',value=None,cost=cost,reason=str(e))
def _records(data):
 if 'status' in data:
  if data['status']!='available':return {}
  data=data['value']
 return {(t['target']['r'],t['target']['l']):t for t in data['targets']}
def energy(matrix,terms):
 indices={d:i for i,d in enumerate(DIVISORS)};terms=arithmetic.canonical_filter(terms)
 return sum(_exact(a['weight'])*_exact(b['weight'])*_exact(matrix[indices[a['divisor']]][indices[b['divisor']]]) for a in terms for b in terms)
def _observed(program,data,X,mode):
 record=_records(data).get((program['target']['r'],program['target']['l']))
 if record is None:return None,'target_missing'
 rows={r['X']:r for r in record['moments']}
 if X not in rows or (mode=='innovation' and 2*X not in rows):return None,'complete_scale_missing'
 z=energy(rows[X]['matrix'],program['filter'])
 if mode=='innovation':z=energy(rows[2*X]['matrix'],program['filter'])-z
 return z,None
def _evaluation_cache(program,data,scales,levels,bit_budget):
 scales=list(scales);levels=list(levels)
 if any(type(q) is not int or q<1 for q in levels):raise ValueError('positive integer levels required')
 record=_records(data).get((program['target']['r'],program['target']['l']))
 rows={} if record is None else {r['X']:r for r in record['moments']}
 terms=arithmetic.canonical_filter(program['filter']);indices={d:i for i,d in enumerate(DIVISORS)}
 weights=[(indices[t['divisor']],_exact(t['weight'])) for t in terms]
 energies={}
 for X in set(scales)|{2*x for x in scales}:
  if X in rows:
   matrix=rows[X]['matrix']
   energies[X]=sum(a*b*_exact(matrix[i][j]) for i,a in weights for j,b in weights)
 observed={}
 for X in scales:
  reason='target_missing' if record is None else 'complete_scale_missing'
  observed[('direct',X)]=(energies[X],None) if X in energies else (None,reason)
  observed[('innovation',X)]=(energies[2*X]-energies[X],None) if X in energies and 2*X in energies else (None,reason)
 roots={(q,X):rational_ceiling(X,F(1,q),bit_budget=bit_budget) for q in levels for X in scales}
 return scales,levels,observed,roots

def fit_constants(program,data,scales,levels=LEVELS,*,bit_budget=1000000):
 scales,levels,observed,roots=_evaluation_cache(program,data,scales,levels,bit_budget)
 constants={};observations=[]
 for mode in ('direct','innovation'):
  constants[mode]={}
  for q in levels:
   if type(q) is not int or q<1:raise ValueError('positive integer levels required')
   maximum=F(0);complete=True
   for X in scales:
    z,reason=observed[(mode,X)];root=roots[(q,X)]
    if z is None or not root.available:complete=False;observations.append(dict(mode=mode,X=X,level=q,missing=True,reason=reason or root.reason));continue
    maximum=max(maximum,z/root.value);observations.append(dict(mode=mode,X=X,level=q,observed=str(z),root=root.value,missing=False))
   constants[mode][str(q)]=str(maximum) if complete else None
 return constants,observations
def score(program,data,scales,levels=LEVELS,*,bit_budget=1000000):
 scales,levels,observed,roots=_evaluation_cache(program,data,scales,levels,bit_budget)
 modes={}
 for mode in ('direct','innovation'):
  obs=[]
  for X in scales:
   for q in levels:
    if type(q) is not int or q<1:raise ValueError('positive integer levels required')
    z,reason=observed[(mode,X)];root=roots[(q,X)];C=program['constants'][mode].get(str(q));missing=z is None or not root.available or C is None
    bound=None if missing else _exact(C)*root.value
    obs.append(dict(X=X,level=q,observed=None if z is None else str(z),bound=None if bound is None else str(bound),margin=None if bound is None else str(bound-z),missing=missing,reason=(reason or ('unknown_level_constant' if C is None else root.reason)) if missing else None,finite_pass=None if missing else z<=bound,global_bound_proved=False))
  modes[mode]=dict(observations=obs,finite_passes=sum(o['finite_pass'] is True for o in obs),finite_failures=sum(o['finite_pass'] is False for o in obs),missing_cases=sum(o['missing'] for o in obs),finite_cases=len(obs))
 return dict(modes=modes,global_bound_proved=False)
def least_squares(matrix,support):
 """Exact box quadratic minimizer: interior, all edges/corners; singular unsupported."""
 support=list(support)
 if len(support) not in (1,2) or len(set(support))!=len(support) or any(d not in DIVISORS[1:] for d in support):raise ValueError('one/two distinct nonleading dictionary divisors required')
 idx=[DIVISORS.index(d) for d in support];H=[[_exact(matrix[i][j]) for j in idx] for i in idx];g=[_exact(matrix[0][i]) for i in idx];a=_exact(matrix[0][0]);choices=[]
 if H[0][0]<=0 or (len(idx)==2 and (H[1][1]<=0 or H[0][0]*H[1][1]-H[0][1]**2<=0)):
  return dict(status='missing',reason='singular_or_nonpositive_support; explicit enumerated grid fallback retained',support=support,choices=[])
 clip=lambda x:max(-BOX,min(BOX,x))
 if len(idx)==1:choices=[dict(kind='clipped_exact_stationary',weights=[clip(-g[0]/H[0][0])])]
 else:
  det=H[0][0]*H[1][1]-H[0][1]**2
  x=(-g[0]*H[1][1]+g[1]*H[0][1])/det;y=(-g[1]*H[0][0]+g[0]*H[0][1])/det
  if abs(x)<=BOX and abs(y)<=BOX:choices.append(dict(kind='interior',weights=[x,y]))
  for x in (-BOX,BOX):choices.append(dict(kind='edge_first',weights=[x,clip(-(g[1]+H[0][1]*x)/H[1][1])]))
  for y in (-BOX,BOX):choices.append(dict(kind='edge_second',weights=[clip(-(g[0]+H[0][1]*y)/H[0][0]),y]))
  for x,y in product((-BOX,BOX),repeat=2):choices.append(dict(kind='corner',weights=[x,y]))
 def objective(w):return a+2*sum(g[i]*w[i] for i in range(len(w)))+sum(H[i][j]*w[i]*w[j] for i in range(len(w)) for j in range(len(w)))
 best=min(choices,key=lambda c:(objective(c['weights']),tuple(c['weights']),c['kind']))
 return dict(status='available',support=support,pooled_matrix=[[str(v) for v in row] for row in H],linear=[str(v) for v in g],constant=str(a),choices=[dict(kind=c['kind'],weights=list(map(str,c['weights'])),objective=str(objective(c['weights']))) for c in choices],exact_weights=list(map(str,best['weights'])),objective=str(objective(best['weights'])),quantized_weights=[str(w.limit_denominator(QUANTIZATION_DENOMINATOR)) for w in best['weights']],solver='exact constrained quadratic interior/edges/corners; no floating solver')
def candidate_factory(data,training_scales,levels=LEVELS,*,bit_budget=1000000):
 scales=_scales(training_scales);records=_records(data);archive=[];candidates={}
 def add(t,terms,origin):
  terms=arithmetic.canonical_filter(terms);admission=arithmetic.certify(t['r'],t['l'],terms)
  if not any(x['divisor']==1 and x['weight']=='1' for x in terms):raise ValueError('leading coefficient normalization failed')
  base=dict(target=t,filter=terms);constants,fitobs=fit_constants(base,data,scales,levels,bit_budget=bit_budget);program=dict(base,constants=constants);pid=digest(program)
  alias=pid in candidates
  archive.append(dict(origin=origin,program_id=pid,exact_program=program,fit_observations=fitobs,alias_of=pid if alias else None,discarded=alias))
  if alias:candidates[pid]['origins'].append(origin)
  else:candidates[pid]=dict(program_id=pid,program=program,admission=admission,origins=[origin],training_score=score(program,data,scales,levels,bit_budget=bit_budget))
 for t in TARGETS:
  k=t['r']+t['l'];base=[(1,1)];add(t,base,dict(kind='baseline',target=t))
  if k>=2:
   for d,w in product(DIVISORS[1:],TWO_WEIGHTS):add(t,base+[(d,w)],dict(kind='grid_two',target=t,divisor=d,weight=w))
  if k>=3:
   for ds in combinations(DIVISORS[1:],2):
    for ws in product(THREE_WEIGHTS,repeat=2):add(t,base+list(zip(ds,ws)),dict(kind='grid_three',target=t,divisors=list(ds),weights=list(ws)))
  if k>=3:
   for d in DIVISORS[1:]:
    if d*d in DIVISORS:
     for w in TWO_WEIGHTS:
      wq=_exact(w)
      add(t,base+[(d,2*wq),(d*d,wq*wq)],dict(kind='composition_square',target=t,divisor=d,source_weight=w,formula='(1+w D_d)^2'))
  record=records.get((t['r'],t['l']));rowmap={} if record is None else {r['X']:r for r in record['moments']}
  pooled=None if any(X not in rowmap for X in scales) else [[sum(_exact(rowmap[X]['matrix'][i][j]) for X in scales) for j in range(len(DIVISORS))] for i in range(len(DIVISORS))]
  for size in range(1,k):
   for support in combinations(DIVISORS[1:],size):
    origin=dict(kind='inferred',target=t,support=list(support))
    if pooled is None:archive.append(dict(origin=origin,status='missing',reason='training moments missing',discarded=True));continue
    solver=least_squares(pooled,support);origin['solver']=solver
    if solver['status']!='available':archive.append(dict(origin=origin,status='missing',reason=solver['reason'],discarded=True));continue
    add(t,base+list(zip(support,solver['quantized_weights'])),origin)
 return dict(schema=1,dictionary_sha256=DICTIONARY_SHA256,candidates=list(candidates.values()),proposal_archive=archive,training_scales=scales,levels=list(levels),global_bound_proved=False)

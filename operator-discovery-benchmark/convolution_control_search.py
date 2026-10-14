"""Unfrozen complete signed-potential proposal language. No global bound claimed.
LP solutions are numerical proposals only; all reported constants are exact refits.
"""
import hashlib
import json
from fractions import Fraction as F
from detector_safe_evaluation import rational_ceiling

LEVELS=[2,3,6,12]
SINGLETON_WEIGHTS=['1/4','1','4']
LP_GROUPS=['gram','fixed','root','three','all']
LP_PENALTIES=['0','1/1024','1/64']
FEATURE_DICTIONARY=[]
for base in ('R_h','R_diff'):
 for eta in ('0','1/6','1/3'):
  FEATURE_DICTIONARY.append(dict(kind='gram',base=base,eta=eta))
for kind,values in (('fixed',(2,3,5,6)),('root',(2,3,6))):
 for d in values:
  for k in ('-2','-1','-1/2','1/2','1','2'):
   FEATURE_DICTIONARY.append(dict(kind=kind,divisor=d,weight=k))
for a,b in (('-1','-1'),('-1','1'),('1','-1'),('1','1'),('2/5','3/5'),('-2/5','-3/5')):
 FEATURE_DICTIONARY.append(dict(kind='three',weights=[a,b],divisors=[2,3]))

def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
for f in FEATURE_DICTIONARY:f['feature_id']=digest(f)
FEATURE_DICTIONARY_SHA256=digest(FEATURE_DICTIONARY)

def _q(x):
 if isinstance(x,(bool,float)):raise ValueError('exact rational required')
 return F(x)

def integer_root(n,k):
 if type(n) is not int or n<1 or type(k) is not int or k<1:raise ValueError('positive integer root arguments required')
 if k>=n.bit_length():return 1
 lo,hi=1,n
 while lo<hi:
  m=(lo+hi+1)//2
  if m**k<=n:lo=m
  else:hi=m-1
 return lo

def featuretable(profile,scales,*,work_budget=10000000,bit_budget=1000000):
 cost=0
 try:
  if type(work_budget) is not int or work_budget<0:raise ValueError('nonnegative integer work budget required')
  if type(bit_budget) is not int or bit_budget<1:raise ValueError('positive integer bit budget required')
  if 'status' in profile:
   if profile['status']!='available':return dict(status=profile['status'],value=None,reason=profile.get('reason'),cost=0)
   profile=profile['value']
  scales=list(scales)
  if not scales or any(type(x) is not int or x<1 for x in scales):raise ValueError('positive integer scales required')
  scales=sorted(set(scales))
  C=list(map(_q,profile['prefix'])); cost+=len(C)
  def blocks(source):
   result={}
   for r in source['rows']:
    X=r['X']
    for scale,suffix in ((X,'_X'),(2*X,'_2X')):
     if 'A'+suffix not in r or 'S'+suffix not in r:continue
     item=dict(X=scale,A_X=r['A'+suffix],S_X=r['S'+suffix])
     if scale in result:
      if any(_q(result[scale][key])!=_q(item[key]) for key in ('A_X','S_X')):raise ValueError('duplicate child block disagreement')
     else:result[scale]=item
   return result
  hrows=blocks(profile.get('actual_h_profile',profile))
  trows=blocks(profile['tau_profile'])
  rows=[]
  for X in scales:
   if 2*X-1>=len(C) or X not in hrows or X not in trows:
    rows.append(dict(X=X,E=None,features={},feature_metadata={},missing=True,reason='complete_profile_scale_missing'));continue
   values={}; meta={}; A=_q(hrows[X]['A_X'])
   for f in FEATURE_DICTIONARY:
    fid=f['feature_id']; kind=f['kind']; reason=None; value=None
    if kind=='gram':
     norm=rational_ceiling(X,f['eta'],bit_budget=bit_budget)
     if cost+4>work_budget:reason='work_budget_exceeded'
     elif not norm.available:reason=norm.reason
     else:
      R=_q(hrows[X]['S_X'])-A if f['base']=='R_h' else _q(trows[X]['S_X'])-_q(hrows[X]['S_X'])
      if R<0:raise ValueError('nonnegative Gram feature premise failed')
      value=R/(X*X*norm.value);cost+=4
     md=dict(normalizer_eta=f['eta'],complete_divisor_diagonal=True)
    else:
     d=max(2,integer_root(X,f['divisor'])) if kind=='root' else f.get('divisor')
     md=dict(divisor_at_scale=d) if kind!='three' else dict(divisors=[2,3])
     if cost+8*X>work_budget:reason='work_budget_exceeded'
     else:
      total=F(0)
      for n in range(X,2*X):
       z=C[n]
       if kind=='three':z+=_q(f['weights'][0])*C[n//2]+_q(f['weights'][1])*C[n//3]
       else:z+=_q(f['weight'])*C[n//d]
       total+=z*z
      cost+=8*X;value=total/(X*X)
    values[fid]=str(value) if value is not None else None
    meta[fid]=dict(md,missing=value is None,reason=reason)
   rows.append(dict(X=X,E=str(A/(X*X)),features=values,feature_metadata=meta,missing=False))
  return dict(status='available',value=dict(rows=rows,dictionary_sha256=FEATURE_DICTIONARY_SHA256,full_child_cutoff_recomputed=True,global_bound_proved=False),reason=None,cost=cost,cost_scope='scalar/list work proxy; not bit complexity')
 except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError) as e:return dict(status='invalid',value=None,reason=str(e),cost=cost)

def _rows(table):
 if 'status' in table:
  if table['status']!='available':return {}
  table=table['value']
 return {r['X']:r for r in table['rows']}

def _innovation(terms,rows,X):
 if X not in rows or 2*X not in rows:return None,'child_scale_missing'
 a,b=rows[X],rows[2*X]
 if a.get('E') is None or b.get('E') is None:return None,'energy_missing'
 z=_q(b['E'])-_q(a['E'])
 for term in terms:
  w=_q(term['weight'])
  if w<0:raise ValueError('nonnegative potential weights required')
  if not w:continue
  fid=term['feature_id'];f=a['features'].get(fid);g=b['features'].get(fid)
  if f is None or g is None:return None,'feature_or_child_missing'
  z+=w*(_q(g)-_q(f))
 return z,None

def refit(terms,table,scales,levels=LEVELS,*,bit_budget=1000000):
 rows=_rows(table); constants={}; observations=[]
 for q in levels:
  if type(q) is not int or q<1:raise ValueError('positive integer levels required')
  maximum=F(0); complete=True
  for X in scales:
   z,reason=_innovation(terms,rows,X);root=rational_ceiling(X,F(1,q),bit_budget=bit_budget)
   if z is None or not root.available:complete=False;observations.append(dict(X=X,level=q,missing=True,reason=reason or root.reason));continue
   maximum=max(maximum,z/root.value)
   observations.append(dict(X=X,level=q,signed_innovation=str(z),root=root.value,missing=False))
  constants[str(q)]=str(maximum) if complete else None
 return constants,observations

def score(program,table,scales,levels=LEVELS,*,bit_budget=1000000):
 rows=_rows(table);obs=[]
 for X in scales:
  for q in levels:
   if type(q) is not int or q<1:raise ValueError('positive integer levels required')
   z,reason=_innovation(program['terms'],rows,X);C=program['constants'].get(str(q));root=rational_ceiling(X,F(1,q),bit_budget=bit_budget)
   missing=z is None or C is None or not root.available
   bound=None if missing else _q(C)*root.value
   obs.append(dict(X=X,level=q,signed_innovation=None if z is None else str(z),bound=None if bound is None else str(bound),margin=None if bound is None else str(bound-z),missing=missing,reason=(reason or ('unknown_level_constant' if C is None else root.reason)) if missing else None,finite_pass=None if missing else z<=bound,global_bound_proved=False))
 return dict(observations=obs,finite_passes=sum(o['finite_pass'] is True for o in obs),finite_failures=sum(o['finite_pass'] is False for o in obs),missing_cases=sum(o['missing'] for o in obs),finite_cases=len(obs),global_bound_proved=False)

def candidate_factory(table,training_scales,levels=LEVELS,*,use_lp=True,bit_budget=1000000):
 """Archive every proposal, including numerical failures; exact alias dedup only."""
 rows=_rows(table); proposals=[]; candidates={}
 def add(terms,origin,solver=None):
  terms=[dict(feature_id=t['feature_id'],weight=str(_q(t['weight']))) for t in terms if _q(t['weight'])]
  terms.sort(key=lambda t:t['feature_id'])
  constants,fitobs=refit(terms,table,training_scales,levels,bit_budget=bit_budget)
  program=dict(terms=terms,constants=constants);pid=digest(program)
  proposal=dict(origin=origin,program_id=pid,exact_program=program,fit_observations=fitobs,solver=solver,discarded=False,alias_of=None)
  if pid in candidates:proposal['alias_of']=pid;proposal['discarded']=True;candidates[pid]['origins'].append(origin)
  else:candidates[pid]=dict(program_id=pid,program=program,origins=[origin],training_score=score(program,table,training_scales,levels,bit_budget=bit_budget))
  proposals.append(proposal)
 add([],dict(kind='baseline'))
 for f in FEATURE_DICTIONARY:
  for w in SINGLETON_WEIGHTS:add([dict(feature_id=f['feature_id'],weight=w)],dict(kind='singleton',feature_id=f['feature_id'],weight=w))
 if use_lp:
  try:
   from scipy.optimize import linprog
  except ImportError:
   linprog=None
  for group in LP_GROUPS:
   fs=[f for f in FEATURE_DICTIONARY if group=='all' or f['kind']==group]
   for penalty in LP_PENALTIES:
    origin=dict(kind='lp',group=group,penalty=penalty)
    if linprog is None:proposals.append(dict(origin=origin,status='missing',reason='scipy_unavailable',discarded=True));continue
    matrix=[];rhs=[];reason=None
    for X in training_scales:
     z,reason=_innovation([],rows,X)
     if z is None:break
     differences=[]
     for f in fs:
      a=rows[X]['features'].get(f['feature_id']);b=rows[2*X]['features'].get(f['feature_id'])
      if a is None or b is None:reason='lp_feature_missing';break
      differences.append(float(_q(b)-_q(a)))
     if reason:break
     for qi,q in enumerate(levels):
      root=rational_ceiling(X,F(1,q),bit_budget=bit_budget)
      if not root.available:reason=root.reason;break
      row=differences+[0.0]*len(levels);row[len(fs)+qi]=-root.value
      matrix.append(row);rhs.append(-float(z))
     if reason:break
    if reason:proposals.append(dict(origin=origin,status='missing',reason=reason,discarded=True));continue
    try:
     sol=linprog([float(_q(penalty))]*len(fs)+[1.0]*len(levels),A_ub=matrix,b_ub=rhs,bounds=[(0,8)]*len(fs)+[(0,None)]*len(levels),method='highs')
     solver=dict(success=bool(sol.success),status=int(sol.status),message=str(sol.message),float_solution=None if sol.x is None else [float(x) for x in sol.x],float_objective=None if sol.fun is None else float(sol.fun),role='numerical proposal only; exact full refit authoritative')
     if not sol.success:proposals.append(dict(origin=origin,status='failed',solver=solver,discarded=True));continue
     weights=[F(float(x)).limit_denominator(64) for x in sol.x[:len(fs)]]
     solver['rationalized_weights']=[str(x) for x in weights]
     add([dict(feature_id=f['feature_id'],weight=str(w)) for f,w in zip(fs,weights)],origin,solver)
    except (ValueError,OverflowError,RuntimeError) as e:proposals.append(dict(origin=origin,status='failed',reason=str(e),discarded=True))
 return dict(schema=1,dictionary_sha256=FEATURE_DICTIONARY_SHA256,candidates=list(candidates.values()),proposal_archive=proposals,selection_used_scales=list(training_scales),levels=list(levels),global_bound_proved=False)

# Conventional spelling alias; both names have identical semantics.
feature_table=featuretable

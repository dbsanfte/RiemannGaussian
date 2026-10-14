"""Anchored signed correction discovery with exact box KKT certificates.
Float optimization proposes a face only. Critical correction bounds are supplied
by the arithmetic grammar's theorem, not inferred from these finite fits.
"""
from fractions import Fraction as F
from itertools import product
import hashlib,json,math
from arithmetic_filter_pole_budget import canonical_filter,certify
from detector_safe_evaluation import rational_ceiling
LEVELS=[2,3,6,12]
DEPTHS=[1,2,3,5]
THETAS=['1/6','1/3','1/2']
RIDGES=['1/1024','1/64','1']
SINGLETON_WEIGHTS=['-4','-1','-1/4','1/4','1','4']
BOX=F(8)
QUANTIZATION_DENOMINATOR=64
MAX_EXACT_ITERATIONS=512

def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def exact(x):
 if isinstance(x,(bool,float)) or not isinstance(x,(int,str,F)):raise ValueError('exact rational required')
 return F(x)
def target_spec(t):
 if not isinstance(t,dict) or set(t)!={'r','l','filter'}:raise ValueError('actual target schema required')
 terms=canonical_filter(t['filter']);admission=certify(t['r'],t['l'],terms)
 if not admission['conditional_bridge_admitted']:raise ValueError('target lacks sufficient conditional pole admission')
 return dict(r=t['r'],l=t['l'],filter=terms)
def feature_spec(f):
 if not isinstance(f,dict) or set(f) not in ({'theta','core_depth'},{'theta','core_depth','feature_id'}):raise ValueError('critical correction descriptor required')
 if type(f['core_depth']) is not int or f['core_depth'] not in DEPTHS:raise ValueError('undeclared core depth')
 theta=str(exact(f['theta']))
 if theta not in THETAS:raise ValueError('undeclared theta')
 spec=dict(theta=theta,core_depth=f['core_depth']);fid=digest(spec)
 if 'feature_id' in f and f['feature_id']!=fid:raise ValueError('feature digest mismatch')
 return dict(spec,feature_id=fid)
FEATURES=[feature_spec(dict(core_depth=h,theta=t)) for h in DEPTHS for t in THETAS]
LANGUAGE=dict(features=FEATURES,leading_G_coefficient='1',singleton_weights=SINGLETON_WEIGHTS,ridges=RIDGES,box='8',quantization_denominator=64,max_exact_iterations=MAX_EXACT_ITERATIONS,objective='sum training normalized complete corrected energies plus ridge sum signed weights squared',groups='each core_depth, each theta, all',correction_semantics='actual c even-smallest-prime source, retain core1 or Omega(core)>h, core<=sqrtX, p<=floorX^theta, same fixed target filter, divide byceil(X^(1/[2(h+1)]))',global_bound_proved=False)

def _records(profile,features):
 features=[feature_spec(f) for f in features]
 if len({f['feature_id'] for f in features})!=len(features):raise ValueError('duplicate correction descriptors')
 if isinstance(profile,dict) and 'status' in profile:
  if profile['status']!='available':return {},features
  profile=profile['value']
 if isinstance(profile,dict):
  if 'features' in profile and profile['features']!=features:raise ValueError('profile feature order mismatch')
  rows=profile['rows']
 else:rows=profile
 records={};size=1+len(features);ids=['base_G']+[f['feature_id'] for f in features]
 for r in rows:
  X=r['X'];key=(r['target_id'],X)
  if type(X) is not int or X<1 or key in records:raise ValueError('invalid or duplicate profile scale')
  G=r['gram_numerators'];D=r['gram_base_denominator'];ds=r['correction_denominators']
  if r['feature_ids']!=ids or len(G)!=size or any(len(a)!=size for a in G) or any(type(v) is not int for a in G for v in a):raise ValueError('complete ordered integer Gram required')
  if type(D) is not int or D<1 or len(ds)!=size or ds[0]!=1 or any(type(v) is not int or v<1 for v in ds):raise ValueError('positive exact Gram normalizers required')
  if any(G[i][j]!=G[j][i] for i in range(size) for j in range(size)):raise ValueError('Gram symmetry required')
  records[key]=[[F(G[i][j],D*ds[i]*ds[j]) for j in range(size)] for i in range(size)]
 return records,features

def solve_linear(A,b):
 n=len(b)
 if len(A)!=n or any(len(r)!=n for r in A):raise ValueError('square linear system required')
 rows=[[exact(x) for x in r]+[exact(y)] for r,y in zip(A,b)]
 for j in range(n):
  pivot=next((i for i in range(j,n) if rows[i][j]),None)
  if pivot is None:raise ValueError('singular exact system')
  rows[j],rows[pivot]=rows[pivot],rows[j];v=rows[j][j];rows[j]=[x/v for x in rows[j]]
  for i in range(n):
   if i!=j and rows[i][j]:
    v=rows[i][j];rows[i]=[x-v*y for x,y in zip(rows[i],rows[j])]
 return [r[-1] for r in rows]

def _positive_definite(Q):
 # Exact symmetric Schur complements certify the ridge normal matrix.
 n=len(Q)
 if any(Q[i][j]!=Q[j][i] for i in range(n) for j in range(n)):return False
 A=[r[:] for r in Q]
 for k in range(n):
  if A[k][k]<=0:return False
  for i in range(k+1,n):
   for j in range(i,n):A[j][i]=A[i][j]=A[i][j]-A[i][k]*A[j][k]/A[k][k]
 return True

def objective(Q,g,c,w):return c+2*sum(a*b for a,b in zip(g,w))+sum(w[i]*Q[i][j]*w[j] for i in range(len(w)) for j in range(len(w)))
def _face(Q,g,active):
 n=len(g);free=[i for i in range(n) if i not in active];w=[active.get(i,F(0)) for i in range(n)]
 if free:
  rhs=[-g[i]-sum(Q[i][j]*w[j] for j in active) for i in free]
  solved=solve_linear([[Q[i][j] for j in free] for i in free],rhs)
  for i,x in zip(free,solved):w[i]=x
 return w

def kkt(Q,g,w):
 gradient=[g[i]+sum(Q[i][j]*w[j] for j in range(len(w))) for i in range(len(w))]
 feasible=all(-BOX<=x<=BOX for x in w)
 signs=[v>=0 if x==-BOX else v<=0 if x==BOX else v==0 for x,v in zip(w,gradient)]
 return dict(feasible=feasible,half_gradients=list(map(str,gradient)),coordinate_conditions=signs,all_KKT_verified=feasible and all(signs),normal_equation='Q*w+g=half_gradient; free=0, lower>=0, upper<=0')

def box_fit(pooled,support,ridge,*,use_float=True,max_iterations=MAX_EXACT_ITERATIONS):
 """Return an optimum only after full exact KKT; failure has no fitted vector."""
 try:
  ridge=exact(ridge);support=list(support)
  if ridge<=0 or not support or len(set(support))!=len(support) or any(type(i) is not int or i<1 or i>=len(pooled) for i in support):raise ValueError('positive ridge and distinct correction indices required')
  if type(max_iterations) is not int or max_iterations<0:raise ValueError('nonnegative iteration budget required')
  Q=[[exact(pooled[i][j])+(ridge if i==j else 0) for j in support] for i in support];g=[exact(pooled[0][i]) for i in support];c=exact(pooled[0][0]);n=len(g)
  if not _positive_definite(Q):raise ValueError('ridge normal matrix not certified positive definite')
  log=[];float_record=dict(status='disabled');answer=None;method=None
  if use_float:
   try:
    from scipy.optimize import minimize
    Qf=[[float(x) for x in row] for row in Q];gf=list(map(float,g));cf=float(c)
    def fun(w):return cf+2*sum(a*b for a,b in zip(gf,w))+sum(w[i]*Qf[i][j]*w[j] for i in range(n) for j in range(n))
    def jac(w):return [2*(gf[i]+sum(Qf[i][j]*w[j] for j in range(n))) for i in range(n)]
    result=minimize(fun,[0.0]*n,jac=jac,bounds=[(-8,8)]*n,method='L-BFGS-B')
    floats=[float(x) for x in result.x]
    if not all(math.isfinite(x) for x in floats):raise ValueError('nonfinite float proposal')
    face={i:(-BOX if x<-8+1e-7 else BOX) for i,x in enumerate(floats) if x<-8+1e-7 or x>8-1e-7}
    float_record=dict(status='available',success=bool(result.success),solver_status=int(result.status),message=str(result.message),weights=floats,objective=float(result.fun),proposed_face={str(i):str(v) for i,v in face.items()},role='face proposal only; float success not an optimality certificate')
    polished=_face(Q,g,face);certificate=kkt(Q,g,polished);log.append(dict(method='float_face_exact_polish',face={str(i):str(v) for i,v in face.items()},weights=list(map(str,polished)),objective=str(objective(Q,g,c,polished)),certificate=certificate))
    if certificate['all_KKT_verified']:answer=polished;method='float_face_exact_KKT'
   except ImportError:float_record=dict(status='missing',reason='scipy unavailable; exact solver still attempted')
   except (ValueError,OverflowError,RuntimeError) as e:float_record=dict(status='failed',reason=str(e))
  if answer is None:
   w=[F(0)]*n;active={};seen=set()
   for iteration in range(max_iterations):
    state=(tuple(w),tuple(sorted(active.items())))
    if state in seen:log.append(dict(method='exact_active_set',iteration=iteration,reason='repeated exact state'));break
    seen.add(state);y=_face(Q,g,active);certificate=kkt(Q,g,y)
    entry=dict(method='exact_active_set',iteration=iteration,face={str(i):str(v) for i,v in active.items()},stationary_weights=list(map(str,y)),stationary_certificate=certificate);log.append(entry)
    if certificate['feasible']:
     w=y
     if certificate['all_KKT_verified']:answer=w;method='exact_primal_active_set';break
     gradient=list(map(F,certificate['half_gradients']))
     bad=[i for i in sorted(active) if (w[i]==-BOX and gradient[i]<0) or (w[i]==BOX and gradient[i]>0)]
     if not bad:break
     removed=bad[0];del active[removed];entry['released_coordinate']=removed
    else:
     direction=[a-b for a,b in zip(y,w)];ratios=[]
     for i in range(n):
      if y[i]>BOX:ratios.append(((BOX-w[i])/direction[i],i,BOX))
      elif y[i]<-BOX:ratios.append(((-BOX-w[i])/direction[i],i,-BOX))
     alpha=min(r[0] for r in ratios)
     if not 0<=alpha<=1:raise ValueError('invalid exact feasible step')
     previous=objective(Q,g,c,w);w=[x+alpha*d for x,d in zip(w,direction)]
     if objective(Q,g,c,w)>previous:raise ValueError('exact active step increased objective')
     blocking=[(i,v) for a,i,v in ratios if a==alpha]
     for i,v in blocking:active[i]=v
     entry.update(step=str(alpha),feasible_weights=list(map(str,w)),blocking_coordinates=[i for i,v in blocking])
  if answer is None and n<=4:
   for state in product((-1,0,1),repeat=n):
    face={i:BOX*s for i,s in enumerate(state) if s};y=_face(Q,g,face);certificate=kkt(Q,g,y)
    log.append(dict(method='finite_face_fallback',face={str(i):str(v) for i,v in face.items()},weights=list(map(str,y)),certificate=certificate))
    if certificate['all_KKT_verified']:answer=y;method='finite_face_fallback';break
  record=dict(support_indices=support,ridge=str(ridge),box='8',quadratic_matrix=[[str(exact(pooled[i][j])) for j in support] for i in support],normal_matrix=[[str(x) for x in row] for row in Q],linear=list(map(str,g)),constant=str(c),positive_definite_verified=True,float_proposal=float_record,attempts=log,solver_method=method,optimality_scope='exact strictly-convex training quadratic only; no global arithmetic estimate')
  if answer is None:return dict(record,status='failed',reason='no exact KKT optimum within declared solver budget',exact_weights=None,quantized_weights=None)
  return dict(record,status='available',reason=None,exact_weights=list(map(str,answer)),quantized_weights=[str(x.limit_denominator(QUANTIZATION_DENOMINATOR)) for x in answer],objective=str(objective(Q,g,c,answer)),KKT_certificate=kkt(Q,g,answer))
 except (ValueError,TypeError,IndexError,ZeroDivisionError) as e:return dict(status='invalid',reason=str(e),exact_weights=None,quantized_weights=None)

def _corrections(terms,features):
 declared={f['feature_id']:f for f in features};weights={}
 for t in terms:
  f=feature_spec(t['feature']);fid=f['feature_id']
  if fid not in declared or declared[fid]!=f:raise ValueError('undeclared correction feature')
  weights[fid]=weights.get(fid,F(0))+exact(t['weight'])
 return [dict(feature=declared[k],weight=str(w)) for k,w in sorted(weights.items()) if w]
def _observations(program,records,features,scales):
 tid=digest(target_spec(program['target']));index={f['feature_id']:i+1 for i,f in enumerate(features)};terms=_corrections(program['corrections'],features);vector=[(0,F(1))]+[(index[t['feature']['feature_id']],exact(t['weight'])) for t in terms];energies={}
 for X in set(scales)|{2*x for x in scales}:
  M=records.get((tid,X))
  if M is not None:
   energies[X]=sum(a*b*M[i][j] for i,a in vector for j,b in vector)
   if energies[X]<0:raise ValueError('negative complete corrected Gram square')
 result={}
 for X in scales:
  result[('direct',X)]=(energies[X],None) if X in energies else (None,'complete_target_scale_missing')
  result[('innovation',X)]=(energies[2*X]-energies[X],None) if X in energies and 2*X in energies else (None,'complete_child_scale_missing')
 return result

def _fit(program,records,features,scales,levels,bit_budget):
 observed=_observations(program,records,features,scales);roots={};constants={};evidence=[]
 for q in levels:
  if type(q) is not int or q<1:raise ValueError('positive integer levels required')
  for X in scales:roots[q,X]=rational_ceiling(X,F(1,q),bit_budget=bit_budget)
 for mode in ('direct','innovation'):
  constants[mode]={}
  for q in levels:
   maximum=F(0);complete=True
   for X in scales:
    value,reason=observed[mode,X];root=roots[q,X]
    if value is None or not root.available:complete=False;evidence.append(dict(mode=mode,X=X,level=q,missing=True,reason=reason or root.reason));continue
    maximum=max(maximum,value/root.value);evidence.append(dict(mode=mode,X=X,level=q,observed=str(value),root=root.value,missing=False))
   constants[mode][str(q)]=str(maximum) if complete else None
 return constants,evidence

def fit_constants(program,profile,features,scales,levels=LEVELS,*,bit_budget=1000000):
 records,features=_records(profile,features);return _fit(program,records,features,list(scales),list(levels),bit_budget)
def _score(program,records,features,scales,levels,bit_budget):
 observed=_observations(program,records,features,scales);roots={};modes={}
 for q in levels:
  if type(q) is not int or q<1:raise ValueError('positive integer levels required')
  for X in scales:roots[q,X]=rational_ceiling(X,F(1,q),bit_budget=bit_budget)
 for mode in ('direct','innovation'):
  out=[]
  for X in scales:
   for q in levels:
    value,reason=observed[mode,X];root=roots[q,X];C=program['constants'][mode].get(str(q));missing=value is None or not root.available or C is None;bound=None if missing else exact(C)*root.value
    out.append(dict(X=X,level=q,observed=None if value is None else str(value),bound=None if bound is None else str(bound),margin=None if bound is None else str(bound-value),missing=missing,reason=(reason or ('unknown_level_constant' if C is None else root.reason)) if missing else None,finite_pass=None if missing else value<=bound,global_bound_proved=False))
  modes[mode]=dict(observations=out,finite_passes=sum(o['finite_pass'] is True for o in out),finite_failures=sum(o['finite_pass'] is False for o in out),missing_cases=sum(o['missing'] for o in out),finite_cases=len(out))
 return dict(modes=modes,global_bound_proved=False)
def score(program,profile,features,scales,levels=LEVELS,*,bit_budget=1000000):
 records,features=_records(profile,features);return _score(program,records,features,list(scales),list(levels),bit_budget)
def groups(features):
 result=[]
 for h in DEPTHS:result.append(dict(group_id='depth_'+str(h),indices=[i+1 for i,f in enumerate(features) if f['core_depth']==h]))
 for theta in THETAS:result.append(dict(group_id='theta_'+theta,indices=[i+1 for i,f in enumerate(features) if f['theta']==theta]))
 result.append(dict(group_id='all',indices=list(range(1,len(features)+1))))
 return [g for g in result if g['indices']]
def candidate_factory(profile,target,features,training_scales,levels=LEVELS,*,bit_budget=1000000,use_float=True,max_iterations=MAX_EXACT_ITERATIONS):
 target=target_spec(target);records,features=_records(profile,features);scales=list(training_scales);levels=list(levels)
 if not scales or any(type(x) is not int or x<1 for x in scales):raise ValueError('positive nonempty training scales required')
 tid=digest(target);archive=[];candidates={}
 def add(corrections,origin):
  corrections=_corrections(corrections,features);base=dict(target=target,corrections=corrections);constants,evidence=_fit(base,records,features,scales,levels,bit_budget);program=dict(base,constants=constants);pid=digest(program);alias=pid in candidates
  archive.append(dict(origin=origin,program_id=pid,exact_program=program,fit_observations=evidence,alias_of=pid if alias else None,discarded=alias))
  if alias:candidates[pid]['origins'].append(origin)
  else:candidates[pid]=dict(program_id=pid,program=program,origins=[origin],training_score=_score(program,records,features,scales,levels,bit_budget),conditional_correction_bridge=True,global_bound_proved=False)
 add([],dict(kind='baseline'))
 for f in features:
  for w in SINGLETON_WEIGHTS:add([dict(feature=f,weight=w)],dict(kind='singleton',feature_id=f['feature_id'],weight=w))
 pooled=None
 if all((tid,X) in records for X in scales):
  size=len(features)+1;pooled=[[sum(records[tid,X][i][j] for X in scales) for j in range(size)] for i in range(size)]
 for group in groups(features):
  for ridge in RIDGES:
   origin=dict(kind='ridge_fit',group=group['group_id'],ridge=ridge)
   if pooled is None:
    for variant in ('exact','quantized'):archive.append(dict(origin=dict(origin,variant=variant),status='missing',reason='complete training moments missing',discarded=True))
    continue
   solver=box_fit(pooled,group['indices'],ridge,use_float=use_float,max_iterations=max_iterations)
   for variant,key in (('exact','exact_weights'),('quantized','quantized_weights')):
    o=dict(origin,variant=variant,solver=solver)
    if solver['status']!='available':archive.append(dict(origin=o,status=solver['status'],reason=solver['reason'],discarded=True));continue
    weights=solver[key];add([dict(feature=features[i-1],weight=w) for i,w in zip(group['indices'],weights)],o)
 return dict(schema=1,target=target,target_id=tid,features=features,dictionary_sha256=digest(features),candidates=list(candidates.values()),proposal_archive=archive,training_scales=scales,levels=levels,global_bound_proved=False)

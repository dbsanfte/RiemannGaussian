"""Unfrozen finite signed Gram potential language for complete factor regions.
Nonnegative potentials preserve the conditional base-energy bridge; no complete
signed innovation estimate, LP optimality certificate, or RH proof is supplied.
"""
from fractions import Fraction as F
import hashlib,json
from detector_safe_evaluation import rational_ceiling
from arithmetic_filter_pole_budget import canonical_filter, certify
LEVELS=[2,3,6,12]
ETAS=['0','1/3']
SINGLETON_WEIGHTS=['1/4','1','4']
LP_PENALTIES=['0','1/1024']
BOX=8
QUANTIZATION_DENOMINATOR=64
COMPONENT_ORDER=['unit','prime_small/core_small/odd','prime_small/core_small/even','prime_small/core_large/odd','prime_small/core_large/even','prime_large/core_small/odd','prime_large/core_small/even','prime_large/core_large/odd','prime_large/core_large/even']
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def exact(x):
 if isinstance(x,(float,bool)) or not isinstance(x,(int,str,F)):raise ValueError('exact rational required')
 return F(x)
def target_spec(t):
 if not isinstance(t,dict) or set(t)!={'r','l','filter'}:raise ValueError('exact target r,l,filter required')
 if any(type(t[k]) is not int or t[k]<0 for k in ('r','l')) or t['r']+t['l']<1:raise ValueError('positive target arity required')
 terms=canonical_filter(t['filter'])
 if not certify(t['r'],t['l'],terms)['conditional_bridge_admitted']:raise ValueError('target filter lacks supported conditional pole-budget admission')
 return dict(r=t['r'],l=t['l'],filter=terms)
def scheme_spec(s):
 if not isinstance(s,dict) or set(s)!={'prime_power','core_power'}:raise ValueError('prime_power/core_power scheme required')
 s={k:str(exact(s[k])) for k in ('prime_power','core_power')}
 if any(exact(v)<=0 for v in s.values()):raise ValueError('positive scheme exponents required')
 return s
def dictionary(schemes):
 vectors=[]
 for i in range(9):
  b=[0]*9;b[i]=1;vectors.append(b)
 for pairs in (((1,2),(3,4),(5,6),(7,8)),((1,5),(2,6),(3,7),(4,8)),((1,3),(2,4),(5,7),(6,8))):
  for i,j in pairs:
   b=[0]*9;b[i]=1;b[j]=-1;vectors.append(b)
 vectors.extend([[0]+[1]*8,[0,1,-1,1,-1,1,-1,1,-1],[0,1,1,1,1,-1,-1,-1,-1]])
 seen=set();features=[]
 for raw in schemes:
  scheme=scheme_spec(raw);sid=digest(scheme)
  for b in vectors:
   for eta in ETAS:
    spec=dict(scheme=scheme,scheme_id=sid,vector=b,eta=eta);fid=digest(spec)
    if fid not in seen:seen.add(fid);features.append(dict(spec,feature_id=fid))
 return features
LANGUAGE=dict(component_order=COMPONENT_ORDER,eta=ETAS,singleton_weights=SINGLETON_WEIGHTS,lp_penalties=LP_PENALTIES,box=BOX,quantization_denominator=QUANTIZATION_DENOMINATOR,vector_productions='9unit basis,4parity differences,4prime differences,4core differences,all_nonunit,odd_minus_even,prime_small_minus_large',base_energy_mandatory=True,conditional_bridge='V>=0; cofinal all-dyadic bound on E(2X)+V(2X)-E(X)-V(X) implies critical base filtered energy; no estimate proved')
def feature_table(profile,targets,schemes,*,scales=None,work_budget=100000000,bit_budget=1000000):
 cost=0
 try:
  if type(work_budget) is not int or work_budget<0 or type(bit_budget) is not int or bit_budget<1:raise ValueError('invalid budgets')
  targets=[target_spec(t) for t in targets];specs=[dict(target_id=digest(t),target=t) for t in targets]
  if len({t['target_id'] for t in specs})!=len(specs):raise ValueError('duplicate target')
  features=dictionary(schemes);sids={f['scheme_id'] for f in features};tids={t['target_id'] for t in specs}
  if isinstance(profile,dict) and 'status' in profile:
   if profile['status']!='available':return dict(status=profile['status'],value=None,reason=profile.get('reason'),cost=0)
   profile=profile['value']
  rawrows=profile['rows'] if isinstance(profile,dict) else profile;records={};energies={}
  for row in rawrows:
   X=row['X'];tid=row['target_id'];sid=row['scheme_id']
   if type(X) is not int or X<1 or tid not in tids or sid not in sids:raise ValueError('undeclared target/scheme or invalid scale')
   key=(tid,X,sid)
   if key in records:raise ValueError('duplicate profile row')
   D=row['gram_denominator'];G=row['gram_numerators']
   if type(D) is not int or D<1 or len(G)!=9 or any(len(a)!=9 for a in G) or any(type(v) is not int for a in G for v in a):raise ValueError('complete integer9x9 Gram and positive denominator required')
   if any(G[i][j]!=G[j][i] for i in range(9) for j in range(9)):raise ValueError('Gram symmetry required')
   E=exact(row['E']);old=energies.get((tid,X))
   if E<0 or (old is not None and E!=old):raise ValueError('base energy nonnegative/agreement required')
   if sum(v for a in G for v in a)!=E*D:raise ValueError('complete partition Gram sum must equal base energy')
   energies[(tid,X)]=E;records[key]=(G,D)
  scales=sorted({r['X'] for r in rawrows}) if scales is None else list(scales)
  if any(type(x) is not int or x<1 for x in scales):raise ValueError('positive integer scales required')
  rows=[];roots={}
  for t in specs:
   tid=t['target_id']
   for X in sorted(set(scales)):
    values={};missing={}
    for f in features:
     fid=f['feature_id'];record=records.get((tid,X,f['scheme_id']))
     if record is None:values[fid]=None;missing[fid]='complete_scheme_row_missing';continue
     b=f['vector'];indices=[i for i in range(9) if b[i]];charge=len(indices)**2
     if cost+charge>work_budget:values[fid]=None;missing[fid]='work_budget_exceeded';continue
     cost+=charge;G,D=record;z=sum(b[i]*b[j]*G[i][j] for i in indices for j in indices)
     if z<0:raise ValueError('negative exact squared Gram form')
     k=(X,f['eta'])
     if k not in roots:roots[k]=rational_ceiling(X,f['eta'],bit_budget=bit_budget)
     norm=roots[k]
     if not norm.available:values[fid]=None;missing[fid]=norm.reason;continue
     values[fid]=str(F(z,D*norm.value))
    E=energies.get((tid,X));rows.append(dict(target_id=tid,X=X,E=None if E is None else str(E),features=values,feature_missing=missing))
  return dict(status='available',value=dict(targets=specs,features=features,rows=rows,dictionary_sha256=digest(features),full_signed_Gram_retained=True,global_bound_proved=False),reason=None,cost=cost,cost_scope='nonzero quadratic scalar products only; not bit complexity, parsing or physical allocations')
 except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError) as e:return dict(status='invalid',value=None,reason=str(e),cost=cost)
def _table(table):
 if 'status' in table:
  if table['status']!='available':return dict(rows=[],features=[])
  table=table['value']
 return table
def feature_spec(f):
 if not isinstance(f,dict) or set(f)!={'scheme','scheme_id','vector','eta','feature_id'}:raise ValueError('complete declared feature schema required')
 if not isinstance(f['vector'],list) or len(f['vector'])!=9 or any(type(x) is not int for x in f['vector']):raise ValueError('exact nine-integer feature vector required')
 if f not in dictionary([scheme_spec(f['scheme'])]):raise ValueError('feature is outside fixed vector/eta dictionary or has invalid digest')
 return f

def _terms(terms):
 weights={};specs={}
 for t in terms:
  f=feature_spec(t['feature']);fid=f['feature_id'];payload={k:v for k,v in f.items() if k!='feature_id'}
  if digest(payload)!=fid:raise ValueError('feature digest mismatch')
  w=exact(t['weight'])
  if w<0:raise ValueError('nonnegative potential weights required')
  weights[fid]=weights.get(fid,F(0))+w;specs[fid]=f
 return [dict(feature=specs[k],weight=str(w)) for k,w in sorted(weights.items()) if w]
def _cache(program,table,scales,levels,bit_budget):
 target=target_spec(program['target']);tid=digest(target);tab=_table(table);rows={r['X']:r for r in tab['rows'] if r['target_id']==tid};terms=_terms(program['terms']);obs={};roots={}
 if ('status' not in table or table['status']=='available') and any(t['feature'] not in tab['features'] for t in terms):raise ValueError('potential feature not declared in table')
 for X in scales:
  if type(X) is not int or X<1:raise ValueError('positive integer scales required')
  if X not in rows or 2*X not in rows or rows[X]['E'] is None or rows[2*X]['E'] is None:obs[X]=(None,'base_or_child_energy_missing');continue
  z=exact(rows[2*X]['E'])-exact(rows[X]['E']);reason=None
  for t in terms:
   fid=t['feature']['feature_id'];a=rows[X]['features'].get(fid);b=rows[2*X]['features'].get(fid)
   if a is None or b is None:reason='feature_or_child_missing';break
   z+=exact(t['weight'])*(exact(b)-exact(a))
  obs[X]=(None,reason) if reason else (z,None)
 for q in levels:
  if type(q) is not int or q<1:raise ValueError('positive integer levels required')
  for X in scales:roots[(q,X)]=rational_ceiling(X,F(1,q),bit_budget=bit_budget)
 return obs,roots
def refit(program,table,scales,levels=LEVELS,*,bit_budget=1000000):
 scales=list(scales);levels=list(levels);obs,roots=_cache(program,table,scales,levels,bit_budget);constants={};evidence=[]
 for q in levels:
  largest=F(0);complete=True
  for X in scales:
   z,reason=obs[X];root=roots[(q,X)];missing=z is None or not root.available
   if missing:complete=False;evidence.append(dict(X=X,level=q,missing=True,reason=reason or root.reason));continue
   largest=max(largest,z/root.value);evidence.append(dict(X=X,level=q,signed_innovation=str(z),root=root.value,missing=False))
  constants[str(q)]=str(largest) if complete else None
 return constants,evidence
def score(program,table,scales,levels=LEVELS,*,bit_budget=1000000):
 scales=list(scales);levels=list(levels);obs,roots=_cache(program,table,scales,levels,bit_budget);out=[]
 for X in scales:
  for q in levels:
   z,reason=obs[X];root=roots[(q,X)];C=program['constants'].get(str(q));missing=z is None or not root.available or C is None;bound=None if missing else exact(C)*root.value
   out.append(dict(X=X,level=q,signed_innovation=None if z is None else str(z),bound=None if bound is None else str(bound),margin=None if bound is None else str(bound-z),missing=missing,reason=(reason or ('unknown_level_constant' if C is None else root.reason)) if missing else None,finite_pass=None if missing else z<=bound,global_bound_proved=False))
 return dict(observations=out,finite_passes=sum(o['finite_pass'] is True for o in out),finite_failures=sum(o['finite_pass'] is False for o in out),missing_cases=sum(o['missing'] for o in out),finite_cases=len(out),global_bound_proved=False)
def candidate_factory(table,target,features,training_scales,levels=LEVELS,*,bit_budget=1000000,use_lp=True):
 target=target_spec(target);scales=list(training_scales);levels=list(levels);features=list(features);archive=[];candidates={};tab=_table(table);tid=digest(target);rows={r['X']:r for r in tab['rows'] if r['target_id']==tid}
 for f in features:feature_spec(f)
 if ('status' not in table or table['status']=='available') and any(f not in tab['features'] for f in features):raise ValueError('candidate features must be declared in sealed table')
 def add(terms,origin,solver=None):
  terms=_terms(terms);base=dict(target=target,terms=terms);constants,evidence=refit(base,table,scales,levels,bit_budget=bit_budget);program=dict(base,constants=constants);pid=digest(program);alias=pid in candidates
  archive.append(dict(origin=origin,solver=solver,program_id=pid,exact_program=program,fit_observations=evidence,alias_of=pid if alias else None,discarded=alias))
  if alias:candidates[pid]['origins'].append(origin)
  else:candidates[pid]=dict(program_id=pid,program=program,origins=[origin],training_score=score(program,table,scales,levels,bit_budget=bit_budget))
 add([],dict(kind='baseline'))
 for f in features:
  for w in SINGLETON_WEIGHTS:add([dict(feature=f,weight=w)],dict(kind='singleton',feature_id=f['feature_id'],scheme_id=f['scheme_id'],weight=w))
 if use_lp:
  try:from scipy.optimize import linprog
  except ImportError:linprog=None
  groups=sorted({f['scheme_id'] for f in features})+['all']
  base=dict(target=target,terms=[]);obs,roots=_cache(base,table,scales,levels,bit_budget)
  for group in groups:
   fs=[f for f in features if group=='all' or f['scheme_id']==group]
   for penalty in LP_PENALTIES:
    origin=dict(kind='lp',group=group,penalty=penalty)
    if linprog is None:archive.append(dict(origin=origin,status='missing',reason='scipy_unavailable',discarded=True));continue
    try:
     matrix=[];rhs=[];reason=None
     for X in scales:
      z,reason=obs[X]
      if z is None:break
      differences=[]
      for f in fs:
       a=rows[X]['features'].get(f['feature_id']);b=rows[2*X]['features'].get(f['feature_id'])
       if a is None or b is None:reason='lp_complete_feature_missing';break
       differences.append(float(exact(b)-exact(a)))
      if reason:break
      for qi,q in enumerate(levels):
       root=roots[(q,X)]
       if not root.available:reason=root.reason;break
       row=differences+[0.0]*len(levels);row[len(fs)+qi]=-root.value;matrix.append(row);rhs.append(-float(z))
      if reason:break
     if reason:archive.append(dict(origin=origin,status='missing',reason=reason,discarded=True));continue
     result=linprog([float(exact(penalty))]*len(fs)+[1.0]*len(levels),A_ub=matrix,b_ub=rhs,bounds=[(0,BOX)]*len(fs)+[(0,None)]*len(levels),method='highs')
     solver=dict(success=bool(result.success),status=int(result.status),message=str(result.message),float_solution=None if result.x is None else [float(x) for x in result.x],float_objective=None if result.fun is None else float(result.fun),role='proposal only; no LP optimality certificate; exact refit authoritative')
     if not result.success:archive.append(dict(origin=origin,status='failed',solver=solver,discarded=True));continue
     weights=[F(float(x)).limit_denominator(QUANTIZATION_DENOMINATOR) for x in result.x[:len(fs)]]
     if any(w<0 or w>BOX for w in weights):raise ValueError('quantized weight outside nonnegative box')
     solver['rationalized_weights']=list(map(str,weights));add([dict(feature=f,weight=str(w)) for f,w in zip(fs,weights)],origin,solver)
    except (ValueError,RuntimeError,OverflowError) as e:archive.append(dict(origin=origin,status='failed',reason=str(e),discarded=True))
 return dict(schema=1,target=target,target_id=tid,dictionary_sha256=digest(features),candidates=list(candidates.values()),proposal_archive=archive,training_scales=scales,levels=levels,global_bound_proved=False)

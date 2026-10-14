"""Exact interval selection for complete signed prime-pair forcing splits.
No finite fit is a uniform arithmetic bound. Positive power splits exploratory.
"""
import hashlib,json
from fractions import Fraction as F
import math
from detector_safe_evaluation import rational_ceiling
LEVELS=[2,3,6,12]
CUTOFFS=[{'kind':'fixed','value':v} for v in (0,1,2,3,4,8)]+[{'kind':'power','power':v} for v in ('1/12','1/6','1/3','1/2')]+[{'kind':'bit_length_power','power':v} for v in ('1/2','1','3/2','2')]
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def exact(x):
 if isinstance(x,(bool,float)):raise TypeError('exact rational required')
 return F(x)
def cutoff_spec(c):
 if not isinstance(c,dict):raise TypeError('cutoff dictionary required')
 kind=c.get('kind')
 if kind=='fixed':
  if set(c)!={'kind','value'} or type(c['value']) is not int or c['value']<0:raise ValueError('nonnegative fixed cutoff required')
  return dict(kind=kind,value=c['value'])
 if kind in ('power','bit_length_power') and set(c)=={'kind','power'}:
  p=exact(c['power'])
  if p<0:raise ValueError('nonnegative power required')
  return dict(kind=kind,power=str(p))
 raise ValueError('unsupported cutoff')
def admission(c):
 c=cutoff_spec(c);ok=c['kind']!='power' or exact(c['power'])==0
 return dict(status='conditional' if ok else 'exploratory',auxiliary_bound_admitted=ok,certificate_reference='prime_pair_forcing_proof.txt: uniform S_B bound; fixed/polylog cutoff',remainder_bound_proved=False,RH_proved=False)
def auxiliary_certificate(target,c):
 if target not in ('mu','c'):raise ValueError('actual target mu/c')
 c=cutoff_spec(c);kind=c['kind'];gamma=exact(c.get('power','0'));s,r=(1,1) if target=='mu' else (3,4)
 if kind=='fixed':
  B=c['value'];scalar=F(8*B*(1+B.bit_length())**s);degree=r;loss=F(0)
 elif kind=='bit_length_power':
  m=-((-gamma.numerator)//gamma.denominator);scalar=8*2**m*(1+2*gamma)**s;degree=m+s+r;loss=F(0)
 else:scalar=8*(1+gamma)**s;degree=s+r;loss=gamma
 return dict(admitted_component_bound=True,cofinal_critical_component_bound=loss==0,scalar=str(scalar),ordinary_X_power=str(2+loss),log_4X_power=degree,cofinal_conversion=dict(log_definition='L=1+log(4X)',integer_degree=degree,outer=2**(degree-1),constant_term=3**degree,q_power=degree,q_coefficient=math.factorial(degree),inequality='L^d <= 2^(d-1)*(3^d+d!*q^d)*ceil(X^(1/q)), q integer>=1'),bound='|S_prefix| <= scalar*X^ordinary_X_power*(1+log(4X))^log_4X_power',full_signed_bound_proved=False,RH_proved=False)
def auxiliary_cost(target,cutoff,X):
 cert=auxiliary_certificate(target,cutoff)
 if not cert['cofinal_critical_component_bound']:return None
 # For b>=2, log2<=3/4 gives 1+log(4X)<=b+2; b=1 means X=1.
 return exact(cert['scalar'])*(X.bit_length()+2)**cert['log_4X_power']
def _rows(profile):
 if isinstance(profile,dict) and 'status' in profile:
  if profile['status']!='available':return []
  profile=profile['value']
 return profile['rows'] if isinstance(profile,dict) else profile
def _index(profile):
 result={}
 for r in _rows(profile):
  key=(r['target'],digest(cutoff_spec(r['cutoff'])),r['X'])
  if key in result:raise ValueError('duplicate response row')
  result[key]=r
 return result
def interval(raw):
 if raw is None:return None
 if isinstance(raw,dict):a,b=exact(raw['lower']),exact(raw['upper'])
 else:a,b=map(exact,raw)
 if a>b:raise ValueError('reversed interval')
 return a,b
def _observed(program,index,X):
 row=index.get((program['target'],digest(cutoff_spec(program['cutoff'])),X))
 if row is None:return None,'missing_response',None
 if row.get('status','available')!='available':return None,row.get('reason','response_unavailable'),row
 value=interval(row.get('normalized_negative_remainder'))
 if value is None:return None,'missing_remainder_interval',row
 return value,None,row

def fit_constants(program,profile,scales,levels=LEVELS,*,bit_budget=1000000):
 index=_index(profile);constants={};evidence=[]
 for q in levels:
  if type(q) is not int or q<1:raise ValueError('positive integer q')
  maximum=F(0);complete=True
  for X in scales:
   v,reason,row=_observed(program,index,X);root=rational_ceiling(X,F(1,q),bit_budget=bit_budget)
   missing=v is None or not root.available
   if missing:complete=False
   else:maximum=max(maximum,v[1]/root.value)
   evidence.append(dict(X=X,level=q,interval=None if v is None else list(map(str,v)),root=root.value if root.available else None,missing=missing,reason=reason or (root.reason if not root.available else None)))
  constants[str(q)]=str(maximum) if complete else None
 return constants,evidence

def score(program,profile,scales,levels=LEVELS,*,bit_budget=1000000):
 index=_index(profile);out=[]
 for X in scales:
  value,reason,row=_observed(program,index,X)
  for q in levels:
   if type(q) is not int or q<1:raise ValueError('positive integer q')
   root=rational_ceiling(X,F(1,q),bit_budget=bit_budget);C=program['constants'].get(str(q));missing=value is None or not root.available or C is None
   bound=None if missing else exact(C)*root.value
   if C is not None and exact(C)<0:raise ValueError('nonnegative constants required')
   state='missing' if missing else 'pass' if value[1]<=bound else 'fail' if value[0]>bound else 'unresolved_interval'
   cost=auxiliary_cost(program['target'],program['cutoff'],X)
   out.append(dict(X=X,level=q,uniform_normalized_abs_prefix_upper=None if cost is None else str(cost),normalized_upper_plus_auxiliary=None if value is None or cost is None else str(value[1]+cost),lower=None if value is None else str(value[0]),upper=None if value is None else str(value[1]),bound=None if bound is None else str(bound),upper_margin=None if bound is None else str(bound-value[1]),lower_margin=None if bound is None else str(bound-value[0]),status=state,missing=missing,reason=(reason or ('unknown_level_constant' if C is None else root.reason)) if missing else None,finite_pass=True if state=='pass' else False if state=='fail' else None,global_bound_proved=False))
 return dict(observations=out,finite_passes=sum(o['status']=='pass' for o in out),finite_failures=sum(o['status']=='fail' for o in out),unresolved_intervals=sum(o['status']=='unresolved_interval' for o in out),missing_cases=sum(o['missing'] for o in out),finite_cases=len(out),global_bound_proved=False)

def candidate_factory(profile,target,training_scales,levels=LEVELS,*,cutoffs=CUTOFFS,bit_budget=1000000):
 if target not in ('mu','c'):raise ValueError('actual target mu or c required')
 index=_index(profile);candidates=[];archive=[]
 for raw in cutoffs:
  cutoff=cutoff_spec(raw);program=dict(target=target,cutoff=cutoff,constants={});constants,evidence=fit_constants(program,profile,training_scales,levels,bit_budget=bit_budget);program['constants']=constants;pid=digest(program)
  coverage=[];diagnostics=[];costs=[];cert=auxiliary_certificate(target,cutoff)
  for X in training_scales:
   row=index.get((target,digest(cutoff),X));coverage.append(dict(X=X,coverage=None if row is None else row.get('coverage'),missing=row is None))
   if row is not None and row.get('component_certificate') is not None and row['component_certificate']!=cert:raise ValueError('component certificate mismatch')
   energy=None if row is None else row.get('original_energy')
   diagnostics.append(dict(X=X,original_energy=energy,normalized_original_energy=None if energy is None else str(F(energy['A_X'],X*X)),normalized_original_innovation=None if energy is None else str(F(energy['A_2X']-4*energy['A_X'],4*X*X)),diagnostic_only=True))
   charge=auxiliary_cost(target,cutoff,X)
   costs.append(dict(X=X,uniform_normalized_abs_prefix_upper=None if charge is None else str(charge),bound_semantics='supplied uniform auxiliary theorem; coarse log upper 1+log(4X)<=2+bit_length X',conditional_only=True))
  candidate=dict(program_id=pid,program=program,conditional_auxiliary=admission(cutoff),training_score=score(program,profile,training_scales,levels,bit_budget=bit_budget),coverage=coverage,component_certificate=cert,auxiliary_costs=costs,original_energy_diagnostics=diagnostics,global_bound_proved=False)
  candidates.append(candidate);archive.append(dict(program_id=pid,exact_program=program,fit_observations=evidence,conditional_auxiliary=admission(cutoff),discarded=False))
 return dict(schema=1,target=target,cutoffs=[cutoff_spec(c) for c in cutoffs],dictionary_sha256=digest([cutoff_spec(c) for c in cutoffs]),candidates=candidates,proposal_archive=archive,training_scales=list(training_scales),levels=list(levels),global_bound_proved=False)

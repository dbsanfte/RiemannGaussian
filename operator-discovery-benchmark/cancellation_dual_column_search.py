"""Generic outcome-conditioned exact dual square proposals, no arithmetic inputs."""
from fractions import Fraction as F
from math import isqrt
import hashlib,json
import arithmetic_cycle_language as L
ATOMS=('prefix','half','even','mod3one','prime')
COEFFICIENTS=('-3','-2','-1/2','1/2','2','3')

def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def enumerate_descriptors():
 out=[]
 for region in ('parent','child'):
  for i,left in enumerate(ATOMS):
   for right in ATOMS[i+1:]:
    for c in COEFFICIENTS:
     d=dict(family='rational_atom_mix',region=region,left=left,right=right,coefficient=c);out.append(dict(d,id=digest(d)))
 return out

def _descriptor(d):
 if type(d)is not dict or d not in enumerate_descriptors():raise ValueError('declared canonical descriptor required')
 return d

def _indices(atom,t):
 out=[]
 for n in range(1,t+1):
  ok=atom=='prefix' or atom=='half' and n<=t//2 or atom=='even' and n%2==0 or atom=='mod3one' and n%3==1 or atom=='prime' and n>=2 and all(n%q for q in range(2,isqrt(n)+1))
  if ok:out.append(n)
 return out

def build_group(desc,X,H,*,max_operations=1000000,max_horizon=127):
 desc=_descriptor(desc)
 if any(type(n)is not int or n<1 for n in (X,H,max_operations,max_horizon)):raise ValueError('strict positive integer domain')
 if H<4*X-1:raise ValueError('complete block horizon required')
 if H>max_horizon:raise OverflowError('proposal horizon cap')
 if 16*X*H*H>max_operations:raise OverflowError('proposal polynomial work preflight')
 start,end=(X,2*X) if desc['region']=='parent' else (2*X,4*X);out=[]
 for t in range(start,end):
  a={(n,):F(1) for n in _indices(desc['left'],t)};b={(n,):F(1) for n in _indices(desc['right'],t)};p=L.add(a,L.scale(b,F(desc['coefficient'])))
  out.append(dict(weight='1',poly=L.dump_poly(p)))
 return out

def propose(instances,dual,scales,max_new_groups=8,*,max_operations=20000000,max_horizon=127):
 if type(instances)is not list or type(scales)is not list or not instances or len(scales)>len(instances):raise ValueError('instance/scale coverage')
 if type(max_new_groups)is not int or not 0<=max_new_groups<=120:raise ValueError('selection cap')
 if type(dual)is not dict or dual.get('status')!='exact_separator' or dual.get('certified')is not True:raise ValueError('exact sealed separator required')
 if len(dual['monomials'])!=len(dual['weights']):raise ValueError('dual dimension')
 y={}
 for m,w in zip(dual['monomials'],dual['weights']):
  if type(m)is not dict or set(m)!={'instance','m'} or type(m['instance'])is not int or not 0<=m['instance']<len(instances) or type(m['m'])is not list:raise ValueError('dual coordinate')
  if any(type(n)is not int or n<1 or n>instances[m['instance']]['horizon'] for n in m['m']) or m['m']!=sorted(m['m']):raise ValueError('canonical horizon-bound dual monomial')
  key=(m['instance'],tuple(m['m']))
  if key in y:raise ValueError('duplicate dual coordinate')
  if type(w)is not str or str(F(w))!=w:raise ValueError('canonical exact dual weight')
  y[key]=F(w)
 # Ordinary instances are the declared scales in order; remaining rows must be
 # explicitly marked by their target/horizon/lhs as auxiliary encodings.
 for i,X in enumerate(scales):
  if type(X)is not int or X<1 or instances[i]['horizon']!=4*X-1:raise ValueError('ordinary scale horizon binding')
 for inst in instances[len(scales):]:
  if inst['target']!='mu' or inst['horizon']!=1 or inst['lhs']!=[] or any(inst['square_groups']):raise ValueError('explicit empty-square auxiliary row required')
 candidates=[];used=0
 for d in enumerate_descriptors():
  dot=F(0);expanded=[];groups=[]
  for i,inst in enumerate(instances):
   group=build_group(d,scales[i],inst['horizon'],max_operations=max_operations,max_horizon=max_horizon) if i<len(scales) else []
   groups.append(group);p={}
   for term in group:
    a=L.load_poly(term['poly']);used+=len(a)**2
    if used>max_operations:raise OverflowError('proposal total expansion budget')
    p=L.add(p,L.mul(a,a,max_operations=max_operations))
   missing=[m for m in p if (i,m) not in y]
   if missing:raise ValueError('unexpected monomial in complete proposed column')
   dot+=sum((q*y[i,m] for m,q in p.items()),F(0));expanded.append(L.dump_poly(p))
  norm=1+F(d['coefficient'])**2
  candidates.append(dict(descriptor=d,column_sha256=digest(expanded),groups_sha256=digest(groups),dot=str(dot),normalized_dot=str(dot/norm),negative=dot<0))
 ranked=sorted((c for c in candidates if c['negative']),key=lambda c:(F(c['normalized_dot']),c['descriptor']['id']));selected=ranked[:max_new_groups]
 return dict(candidates=candidates,selected=selected,candidate_archive_sha256=digest(candidates),selected_sha256=digest(selected),all_candidates_retained=True,enumerated=120,posthoc_outcome_conditioned=True,no_actual_signed_coefficient_input=True,auxiliary_groups_empty=True,operations=used,global_bound_proved=False,RH_proved=False,scope='exact witness-guided basis proposals only; invalidation is not feasibility')

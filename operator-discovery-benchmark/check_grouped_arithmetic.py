"""Independent grouped arithmetic relations and shared finite certificate audit."""
from fractions import Fraction as F
from math import gcd
import check_arithmetic_cycle_certificate as P

def require(x,msg):
 if not x:raise ValueError(msg)
def witness(n,factors,H):
 P.integer(n);require(n<=H,'factor index horizon');require(type(factors)is list,'factor witness list');out={};product=1;last=1
 for pair in factors:
  require(type(pair)is list and len(pair)==2,'factor pair schema');p,e=pair;P.integer(p);P.integer(e);require(p>last and p<=n and P.prime(p),'sorted actual prime witnesses');require(e<=n.bit_length(),'exponent preflight')
  for _ in range(e):
   product*=p;require(product<=n,'factor product exceeds index')
  out[p]=e;last=p
 require(product==n,'complete factor witness product');return out

def relation(spec,target,H):
 require(target in ('mu','c'),'actual target');P.integer(H);P.guard(H,'horizon')
 if type(spec)is not dict:raise ValueError('relation schema')
 if spec.get('kind')=='norm':
  require(set(spec)=={'kind','n','factors'},'norm exact fields');n=spec['n'];fac=witness(n,spec['factors'],H);value=int(all(e==1 for e in fac.values())) if target=='mu' else 4**len(fac)
  return P.add({(n,n):F(1)},{():F(-value)})
 if spec.get('kind')=='gcd_product':
  require(set(spec)=={'kind','a','b','factors_a','factors_b'},'gcd exact fields');a,b=spec['a'],spec['b'];fa=witness(a,spec['factors_a'],H);fb=witness(b,spec['factors_b'],H);g=gcd(a,b);u,v=a//g,b//g
  overlap=sum(1 for p in set(fa)&set(fb) if fa[p]!=fb[p])
  if target=='mu':
   indicator=int(overlap==0 and all(min(fa[p],fb[p])==1 for p in set(fa)&set(fb)));return P.add({tuple(sorted((a,b))):F(1)},{tuple(sorted((u,v))):F(-indicator)})
  den=2**overlap
  return P.add({tuple(sorted((a,b))):F(den)},{tuple(sorted((g,g,u,v))):F(-1)})
 return P.relation(spec,target,H)

def verify_certificate(cert):
 require(type(cert)is dict and set(cert)=={'target','horizon','lhs','squares','relations'},'certificate schema');t=cert['target'];H=cert['horizon'];P.integer(H);P.guard(H,'horizon');require(t in ('mu','c'),'target');lhs=P.parse(cert['lhs'],H);rhs={}
 for s in cert['squares']:
  require(set(s)=={'weight','poly'},'square schema');w=P.rational(s['weight']);require(w>=0,'nonnegative square');p=P.parse(s['poly'],H);rhs=P.add(rhs,P.multiply(p,p),w)
 for r in cert['relations']:
  require(set(r)=={'spec','multiplier'},'relation schema');q=relation(r['spec'],t,H);rhs=P.add(rhs,P.multiply(P.parse(r['multiplier'],H),q))
 require(lhs==rhs,'exact grouped certificate mismatch');return dict(verified=True,finite_identity_verified=True,actual_finite_nonnegative_evaluation=True,global_bound_proved=False,RH_proved=False)

def columns(instance):
 require(set(instance)=={'target','horizon','lhs','square_groups','relation_groups'},'instance schema');t,H=instance['target'],instance['horizon'];P.integer(H);P.guard(H,'horizon');lhs=P.parse(instance['lhs'],H);sq=[];rel=[]
 for group in instance['square_groups']:
  require(type(group)is list,'square group list');column={}
  for s in group:
   require(set(s)=={'weight','poly'},'square atom schema');w=P.rational(s['weight']);require(w>=0,'nonnegative within group');p=P.parse(s['poly'],H);column=P.add(column,P.multiply(p,p),w)
  sq.append(column)
 for group in instance['relation_groups']:
  require(type(group)is list,'relation group list');column={}
  for r in group:
   require(set(r)=={'spec','multiplier'},'relation atom schema');q=relation(r['spec'],t,H);column=P.add(column,P.multiply(P.parse(r['multiplier'],H),q))
  rel.append(column)
 return lhs,sq,rel

def verify_joint(instances,square_weights,relation_weights,*,allow_constant_slack=False):
 require(type(instances)is list and instances,'nonempty instances');sw=list(map(P.rational,square_weights));rw=list(map(P.rational,relation_weights));require(all(w>=0 for w in sw),'shared nonnegative square weights');out=[]
 for instance in instances:
  lhs,sq,rel=columns(instance);require(len(sq)==len(sw) and len(rel)==len(rw),'same shared group dimensions');rhs={}
  for w,c in zip(sw,sq):rhs=P.add(rhs,c,w)
  for w,c in zip(rw,rel):rhs=P.add(rhs,c,w)
  residue=P.add(lhs,rhs,F(-1));require(not any(m for m in residue),'nonconstant shared template mismatch');slack=residue.get((),F(0));require(slack>=0 if allow_constant_slack else slack==0,'constant shared template mismatch');out.append(dict(target=instance['target'],horizon=instance['horizon'],finite_identity_verified=True,constant_slack=str(slack)))
 return dict(verified=True,instances=out,shared_weights_verified=True,finite_only=True,global_bound_proved=False,RH_proved=False)

def verify_joint_result(instances,result,*,allow_constant_slack=False):
 status=result.get('status')
 if status!='finite_certificate':
  require(status in ('no_certificate_found','missing_resource'),'explicit joint missing/failure status');require('certificates' not in result,'failed result certificate');return dict(verified=True,status=status,finite_verified=False,global_bound_proved=False)
 weights=result['weights'];checked=verify_joint(instances,weights['square_weights'],weights['relation_weights'],allow_constant_slack=allow_constant_slack);sw=list(map(P.rational,weights['square_weights']));rw=list(map(P.rational,weights['relation_weights']));require(len(result['certificates'])==len(instances),'certificate count')
 for instance,cert in zip(instances,result['certificates']):
  expected=dict(target=instance['target'],horizon=instance['horizon'],lhs=instance['lhs'],squares=[],relations=[])
  for w,g in zip(sw,instance['square_groups']):
   if w:
    for s in g:
     value=w*P.rational(s['weight'])
     if value:expected['squares'].append(dict(weight=str(value),poly=s['poly']))
  for w,g in zip(rw,instance['relation_groups']):
   if w:
    for r in g:expected['relations'].append(dict(spec=r['spec'],multiplier=P.canonical({m:w*v for m,v in P.parse(r['multiplier'],instance['horizon']).items()})))
  lhs,sq,rel=columns(instance);rhs={}
  for w,p in zip(sw,sq):rhs=P.add(rhs,p,w)
  for w,p in zip(rw,rel):rhs=P.add(rhs,p,w)
  slack=P.add(lhs,rhs,F(-1)).get((),F(0))
  if allow_constant_slack and slack:expected['squares'].append(dict(weight=str(slack),poly=[dict(m=[],c='1')]))
  require(cert==expected,'exact shared certificate expansion');verify_certificate(cert)
 if allow_constant_slack:require(result['constant_slacks']==[i['constant_slack'] for i in checked['instances']],'computed constant slacks')
 return checked

def verify_joint_dual(instances,dual,*,allow_constant_slack=False):
 require(dual.get('status')=='exact_separator' and dual.get('certified') is True,'exact separator status');allcols=[columns(i) for i in instances];ns=len(allcols[0][1]);nr=len(allcols[0][2]);require(all(len(s)==ns and len(r)==nr for l,s,r in allcols),'common dual group counts')
 domain=sorted((j,m) for j,(lhs,sq,rel) in enumerate(allcols) for m in set(lhs)|{m for p in sq+rel for m in p}|({()} if allow_constant_slack else set()));given=[(r['instance'],tuple(r['m'])) for r in dual['monomials']];require(given==domain and len(given)==len(dual['weights']),'full stacked dual domain');y=dict(zip(domain,map(P.rational,dual['weights'])))
 def dot(j,p):return sum((v*y[j,m] for m,v in p.items()),F(0))
 lhs=sum((dot(j,l) for j,(l,s,r) in enumerate(allcols)),F(0));sd=[sum((dot(j,s[k]) for j,(l,s,r) in enumerate(allcols)),F(0)) for k in range(ns)];rd=[sum((dot(j,r[k]) for j,(l,s,r) in enumerate(allcols)),F(0)) for k in range(nr)]
 require(lhs<0 and all(v>=0 for v in sd) and all(v==0 for v in rd),'stacked exact cone separation');cd=[y[j,()] for j in range(len(instances))] if allow_constant_slack else [];require(all(v>=0 for v in cd),'nonnegative constant dual columns');require(list(map(F,dual['columns_dot_y']))==sd+[v for r in rd for v in (r,-r)]+cd and F(dual['lhs_dot_y'])==lhs,'recorded dual dots')
 return dict(verified=True,declared_shared_cone_only=True,global_bound_proved=False,RH_proved=False)

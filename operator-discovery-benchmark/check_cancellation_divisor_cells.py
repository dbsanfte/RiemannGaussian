"""Independent complete divisor-cell reconstruction; no producer imports."""
from fractions import Fraction as F
import re
import check_cancellation_divisor_localizer as BASE
import check_grouped_arithmetic as G
P=G.P
def scale(p,q):return {m:v*q for m,v in p.items() if v*q}
digest=BASE.digest
SPEC=dict(version='divisor-cells-v1',regions=['parent','child'],thetas=['1/3','1/2','2/3'],powers=[-1,0,1],square_forms=['contrast','prefix_plus','prefix_minus'],relation_forms=['one','prefix','contrast','normalization'],source_domain='all 1<=a<=t, d|a; inside and complete complement',partition='d<=floor(t^theta)',normalizer='unit_constant',weights='a^power',source_scale='N=4X-1')
def rat(s,bits=4096):
 if type(s)is not str or len(s)>2*bits+3 or not re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?',s):raise ValueError('canonical rational literal')
 q=F(s)
 if str(q)!=s:raise ValueError('canonical rational')
 if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>bits:raise OverflowError('rational bits')
 return q
def floor_cut(t,partition,bits=4096,max_exponent=64):
 if type(partition)is not dict or set(partition)!={'kind','coefficient','power'}or partition['kind']!='divisor_le':raise ValueError('partition')
 c=rat(partition['coefficient'],bits);p=rat(partition['power'],bits)
 if c<0 or p<0:raise ValueError('nonnegative cut')
 if type(max_exponent)is not int or max_exponent<1:raise ValueError('exponent limit')
 if max(p.numerator,p.denominator)>max_exponent or p.denominator*(c.numerator.bit_length()+c.denominator.bit_length())+p.numerator*t.bit_length()>bits:raise OverflowError('cut powers')
 rhs=c.numerator**p.denominator*t**p.numerator;den=c.denominator**p.denominator
 lo=0;hi=1
 while hi**p.denominator*den<=rhs:hi*=2
 while hi-lo>1:
  mid=(lo+hi)//2
  if mid**p.denominator*den<=rhs:lo=mid
  else:hi=mid
 return lo
def core(t,weights,partition,bits=4096,max_exponent=64):
 if type(t)is not int or t<1 or type(weights)is not list or len(weights)!=t:raise ValueError('complete horizon/weights')
 qs=[rat(w,bits)for w in weights];cut=floor_cut(t,partition,bits,max_exponent);I={};O={};full=[];ip=[];op=[];blocks=[]
 for a in range(1,t+1):
  ds=[]
  for d in range(1,t+1):
   if a%d:continue
   ds.append(d);full.append([a,d]);inside=d<=cut;(ip if inside else op).append([a,d]);dest=I if inside else O;m=tuple(sorted((a,d)))
   if qs[a-1]:dest[m]=dest.get(m,F(0))+qs[a-1]
  blocks.append(dict(a=a,weight=weights[a-1],divisors=ds))
 B=P.add(I,O);c=qs[0];Z=P.add(B,{():-c}if c else{});D=scale(P.add(P.add(I,O,F(-1)),{():-c}if c else{}),F(1,2));Dp=P.add(I,{():-c}if c else{});prefix={(a,):F(1)for a in range(1,t+1)}
 prim=[dict(spec=dict(kind='unit')if a==1 else dict(kind='inverse_row',n=a),multiplier=P.canonical({():c,(1,):c}if a==1 and c else{}if a==1 else{(a,):qs[a-1]}if qs[a-1]else{}))for a in range(1,t+1)]
 source=dict(pairs=full,pairs_sha256=digest(full),pair_count=len(full),blocks=blocks,source_domain='all 1<=a<=H and d|a; zero weights retained',complete=True)
 return dict(P=prefix,I=I,O=O,B=B,Z=Z,D=D,Dprime=Dp,c=c,cut=cut,prim=prim,source=source,ip=ip,op=op)
def certificate(t,lhs,U,prim):return dict(target='mu',horizon=t,lhs=P.canonical(lhs),squares=[],relations=[dict(spec=r['spec'],multiplier=P.canonical(P.multiply(P.parse(r['multiplier'],t),U)))for r in prim])
def check_cells(horizon,weights,partition,output,*,target='mu',max_horizon=128,max_operations=20000000,max_terms=10000,max_coefficient_bits=4096,max_exponent=64):
 for v in [horizon,max_horizon,max_operations,max_terms,max_coefficient_bits]:
  if type(v)is not int or v<1:raise ValueError('strict bounds')
 if target!='mu':raise ValueError('mu only')
 if horizon>max_horizon or 16*(horizon+1)**4>max_operations:raise OverflowError('complete source preflight')
 if (horizon*horizon+horizon+1)**2>max_terms or 8*max((abs(rat(w,max_coefficient_bits).numerator).bit_length()+rat(w,max_coefficient_bits).denominator.bit_length() for w in weights),default=1)+8*horizon.bit_length()>max_coefficient_bits:raise OverflowError('conservative polynomial allocation preflight')
 floor_cut(horizon,partition,max_coefficient_bits,max_exponent);r=core(horizon,weights,partition,max_coefficient_bits,max_exponent);t=horizon
 closures=[dict(multiplier=name,certificate=certificate(t,P.multiply(r['Z'],U),U,r['prim']))for name,U in [('one',{():F(1)}),('prefix',r['P']),('contrast',r['D']),('normalization',r['Z'])]]
 transports=[];squares=[]
 for s in [-1,0,1]:
  A=r['D']if s==0 else P.add(r['P'],r['D'],F(s));Ap=r['Dprime']if s==0 else P.add(r['P'],r['Dprime'],F(s));U=scale(P.add(r['D'],r['Dprime']),F(-1,2))if s==0 else scale(P.add(scale(r['P'],2*s),P.add(r['D'],r['Dprime'])),F(-1,2));square=P.multiply(A,A)
  transports.append(dict(sign=s,certificate=certificate(t,P.add(square,P.multiply(Ap,Ap),F(-1)),U,r['prim'])));squares.append(dict(sign=s,poly=P.canonical(A),square_poly=P.canonical(square),formal_scalar=str(square.get((),F(0)))))
 expected=dict(target='mu',horizon=t,weights=weights,partition=partition,cutoff=r['cut'],c=str(r['c']),B=P.canonical(r['B']),inside=P.canonical(r['I']),complement=P.canonical(r['O']),Z=P.canonical(r['Z']),D=P.canonical(r['D']),Dprime=P.canonical(r['Dprime']),prefix=P.canonical(r['P']),source=dict(full=r['source'],inside_pairs=r['ip'],complement_pairs=r['op'],inside_pairs_sha256=digest(r['ip']),complement_pairs_sha256=digest(r['op']),complete=True),normalization_certificate=certificate(t,r['Z'],{():F(1)},r['prim']),closures=closures,square_transports=transports,coupled_squares=squares,formal_identities_verified=True,arithmetic_values_substituted=False,global_bound_proved=False,RH_proved=False,scope='supplied complete structural split; partial channels unknown; squares do not establish critical budget')
 if set(output)!=set(expected)|{'cost'}:raise ValueError('output fields')
 for k,v in expected.items():
  if digest(output[k])!=digest(v):raise ValueError('cell mismatch '+k)
 cost=output['cost']
 if set(cost)!={'operations','max_operations','max_terms','max_coefficient_bits'}or any(type(v)is not int for v in cost.values())or not 0<=cost['operations']<=max_operations or (cost['max_operations'],cost['max_terms'],cost['max_coefficient_bits'])!=(max_operations,max_terms,max_coefficient_bits):raise ValueError('cost receipt')
 for cert in [expected['normalization_certificate']]+[x['certificate']for x in closures+transports]:
  for poly in [cert['lhs']]+[v['multiplier']for v in cert['relations']]:
   parsed=P.parse(poly,t)
   if len(parsed)>max_terms or any(max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits for q in parsed.values()):raise OverflowError('independent polynomial bounds')
  G.verify_certificate(cert)
 return dict(verified=True,producer_operation_count_independently_verified=False,global_bound_proved=False)
def additions():
 out=dict(square=[],relation=[])
 for region in SPEC['regions']:
  for theta in SPEC['thetas']:
   for power in SPEC['powers']:
    c={k:SPEC[k]for k in ['version','source_domain','partition','normalizer','weights','source_scale']};c.update(region=region,theta=theta,power=power)
    for kind in out:
     for form in SPEC[kind+'_forms']:
      d=dict(c,family='divisor_cell_'+kind,form=form);out[kind].append(dict(d,id=digest(d)))
 return out
def descriptors():
 b=BASE.descriptors();a=additions();return {k:b[k]+a[k]for k in b}
def build_additions(X,*,max_horizon=80,max_operations=200000000,max_terms=100000,max_coefficient_bits=4096):
 for v in [X,max_horizon,max_operations,max_terms,max_coefficient_bits]:
  if type(v)is not int or v<1:raise ValueError('strict bounds')
 H=4*X-1
 if H>max_horizon or 18*H*H>max_operations:raise OverflowError('complete cells preflight')
 sqs=[];rels=[];archive=[];work=0
 for region in SPEC['regions']:
  ts=list(range(X,2*X)if region=='parent'else range(2*X,4*X))
  for theta in SPEC['thetas']:
   for j in SPEC['powers']:
    sg=[[],[],[]];agg=[{}for _ in range(4)];rows=[]
    for t in ts:
     r=core(t,[str(F(a)**j)for a in range(1,t+1)],dict(kind='divisor_le',coefficient='1',power=theta),max_coefficient_bits);work+=t*t
     for k,A in enumerate([r['D'],P.add(r['P'],r['D']),P.add(r['P'],r['D'],F(-1))]):sg[k].append(dict(weight='1',poly=P.canonical(A)))
     for k,U in enumerate([{():F(1)},r['P'],r['D'],r['Z']]):
      for a,term in enumerate(r['prim'],1):
       p=P.multiply(P.parse(term['multiplier'],t),U);work+=len(P.parse(term['multiplier'],t))*len(U);agg[k][a]=P.add(agg[k].get(a,{}),p)
       if len(agg[k][a])>max_terms or any(max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits for q in agg[k][a].values()):raise OverflowError('cell polynomial budget')
     if work>max_operations:raise OverflowError('independent construction proxy')
     rows.append(dict(t=t,cut=r['cut'],source_pairs_sha256=r['source']['pairs_sha256'],inside_pairs_sha256=digest(r['ip']),complement_pairs_sha256=digest(r['op']),source_count=len(r['source']['pairs']),inside_count=len(r['ip']),complement_count=len(r['op']),polynomials_sha256=digest({k:P.canonical(r[v])for k,v in [('P','P'),('I','I'),('O','O'),('D','D'),('Z','Z')]})))
    rg=[[dict(spec=dict(kind='unit')if a==1 else dict(kind='inverse_row',n=a),multiplier=P.canonical(p))for a,p in sorted(g.items())]for g in agg];sqs+=sg;rels+=rg
    archive.append(dict(region=region,theta=theta,power=j,scales=ts,rows=rows,square_groups_sha256=digest(sg),relation_groups_sha256=digest(rg),formal_square_scalars=[str(sum((P.parse(v['poly'],H).get((),F(0))**2 for v in g),F(0)))for g in sg],formal_relation_scalars=[str(-P.parse(g[0]['multiplier'],H).get((),F(0)))for g in rg]))
 return dict(square_groups=sqs,relation_groups=rels,archive=archive,spec=SPEC)
def build(program,X,**limits):
 if program.get('target')!='mu':raise ValueError('mu only')
 extra=build_additions(X,**limits);out=BASE.build(program,X);out['instance']['square_groups']+=extra['square_groups'];out['instance']['relation_groups']+=extra['relation_groups'];d=descriptors();out.update(square_ids=[v['id']for v in d['square']],relation_ids=[v['id']for v in d['relation']],dictionary_sha256=digest(d),cell_archive=extra['archive'],cell_spec=SPEC);return out
def auxiliary():return BASE.B.I.auxiliary_constraint(descriptors())
def check_builder(program,X,out,**limits):
 expected=build(program,X,**limits)
 for k in expected:
  if k.endswith('construction_operations'):continue
  if digest(out.get(k))!=digest(expected[k]):raise ValueError('builder mismatch '+k)
 return dict(verified=True,producer_operation_count_independently_verified=False,global_bound_proved=False)

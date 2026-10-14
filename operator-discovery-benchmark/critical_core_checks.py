"""Independent exact critical-core arithmetic/fit checker. No producer imports."""
from fractions import Fraction as F
import hashlib,json,math
FEATURES=[{'core_depth':h,'theta':theta} for h in (1,2,3,5) for theta in ('1/6','1/3','1/2')]
def require(ok,message):
 if not ok:raise ValueError(message)
def integer(x,minimum=0):
 require(type(x) is int and x>=minimum,'integer domain');return x
def rational(x):
 require(type(x) in (int,str) or isinstance(x,F),'exact rational');return F(x)
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def floor_root(n,k):
 integer(n);integer(k,1)
 if n<2:return n
 lo=0;hi=1<<((n.bit_length()+k-1)//k)
 while hi-lo>1:
  v=(lo+hi)//2
  if v**k<=n:lo=v
  else:hi=v
 return hi if hi**k<=n else lo
def ceil_root(n,k):
 a=floor_root(n,k);return a if a**k==n else a+1
def floor_power(n,p):
 p=rational(p);require(p>0,'positive power');return floor_root(n**p.numerator,p.denominator)
def canonical_target(t):
 require(isinstance(t,dict) and set(t)=={'r','l','filter'},'target schema');integer(t['r']);integer(t['l']);require(t['r']+t['l']>0,'positive arity')
 weights={}
 for term in t['filter']:
  require(set(term)=={'divisor','weight'},'filter schema');d=integer(term['divisor'],1);weights[d]=weights.get(d,F(0))+rational(term['weight'])
 terms=[dict(divisor=d,weight=str(w)) for d,w in sorted(weights.items()) if w]
 require(terms,'nonzero filter');return dict(r=t['r'],l=t['l'],filter=terms)
def local(r,l,j):
 return sum((-1)**i*math.comb(r,i)*((-1)**(j-i)*math.comb(l+j-i-1,j-i) if l else int(j==i)) for i in range(min(r,j)+1))
def factor_tables(N):
 least=list(range(N+1));e=[0]*(N+1);core=[0]*(N+1);omega=[0]*(N+1);core[1]=1
 for p in range(2,math.isqrt(N)+1):
  if least[p]==p:
   for n in range(p*p,N+1,p):
    if least[n]==n:least[n]=p
 for n in range(2,N+1):
  p=least[n];v=n//p;omega[n]=omega[v]+1
  if v%p==0:e[n]=e[v]+1;core[n]=core[v]
  else:e[n]=1;core[n]=v
 return least,e,core,omega
def coefficients(N,r,l,tables):
 _,e,core,_=tables;a=[0]*(N+1);a[1]=1
 for n in range(2,N+1):a[n]=a[core[n]]*local(r,l,e[n])
 return a
def feature_descriptor(spec):
 require(isinstance(spec,dict) and set(spec) in ({'theta','core_depth'},{'theta','core_depth','feature_id'}),'feature schema')
 h=integer(spec['core_depth'],1);theta=rational(spec['theta']);require(theta>0,'positive theta')
 payload={'theta':str(theta),'core_depth':h};fid=digest(payload)
 if 'feature_id' in spec:require(spec['feature_id']==fid,'feature digest mismatch')
 return dict(payload,feature_id=fid)
def reconstruct_row(X,target,features=FEATURES):
 integer(X,1);target=canonical_target(target);N=2*X-1;tab=factor_tables(N);least,e,core,omega=tab
 a=coefficients(N,target['r'],target['l'],tab);c=coefficients(N,1,1,tab);arrays=[a];coverage=[];cutoffs=[]
 for spec in features:
  spec=feature_descriptor(spec);h=spec['core_depth'];z=floor_power(X,spec['theta']);u=math.isqrt(X);R=[0]*(N+1);eligible=[];retained=[];removed=[]
  for n in range(2,N+1):
   if least[n]<=z and core[n]<=u and e[n]%2==0:
    eligible.append(n)
    if core[n]==1 or omega[core[n]]>h:R[n]=c[n];retained.append(n)
    else:removed.append(n)
  arrays.append(R);coverage.append(dict(eligible=eligible,retained=retained,removed=removed));cutoffs.append(dict(z=z,u=u))
 Q=math.lcm(*(F(t['weight']).denominator for t in target['filter']));w=[(t['divisor'],int(F(t['weight'])*Q)) for t in target['filter']]
 prefix=[]
 for arr in arrays:
  P=[0]*(N+1)
  for n in range(1,N+1):P[n]=P[n-1]+arr[n]
  prefix.append([sum(b*P[n//d] for d,b in w) for n in range(X,2*X)])
 gram=[[sum(x*y for x,y in zip(v,u)) for u in prefix] for v in prefix]
 return dict(X=X,target_id=digest(target),feature_ids=['base_G']+[feature_descriptor(f)['feature_id'] for f in features],gram_numerators=gram,gram_base_denominator=X*X*Q*Q,correction_denominators=[1]+[ceil_root(X,2*(s['core_depth']+1)) for s in features],cutoffs=cutoffs,coverage=coverage,source_arrays=arrays,weight_common_denominator=Q)
def normalized_matrix(row):
 G=row['gram_numerators'];D=integer(row['gram_base_denominator'],1);roots=row['correction_denominators'];require(len(G)==len(roots) and all(len(a)==len(roots) for a in G),'complete Gram shape')
 for r in roots:integer(r,1)
 return [[F(v,D*roots[i]*roots[j]) for j,v in enumerate(a)] for i,a in enumerate(G)]
def corrected_energy(row,weights):
 M=normalized_matrix(row);require(len(weights)==len(M)-1,'all correction weights required');w=[F(1)]+[rational(x) for x in weights]
 return sum(w[i]*w[j]*M[i][j] for i in range(len(w)) for j in range(len(w)))
def verify_profile(profile,scales,targets,features=FEATURES):
 if 'status' in profile:
  require(profile['status']=='available','profile unavailable');profile=profile['value']
 rows=profile['rows'];expected={(digest(canonical_target(t)),X) for t in targets for X in scales};seen=set()
 for row in rows:
  key=(row['target_id'],row['X']);require(key in expected and key not in seen,'unexpected/duplicate row');seen.add(key)
  t=next(t for t in targets if digest(canonical_target(t))==key[0]);truth=reconstruct_row(key[1],t,features)
  for field in ('feature_ids','gram_numerators','gram_base_denominator','correction_denominators'):require(row[field]==truth[field],f'exact {field} mismatch')
 require(seen==expected,'missing complete row');return dict(verified=True,rows=len(rows),global_bound_proved=False)
def refit(rows,weights,scales,levels,mode='direct'):
 require(mode in ('direct','innovation'),'mode');table={r['X']:r for r in rows};constants={};observations=[]
 for q in levels:
  integer(q,1);largest=F(0);complete=True
  for X in scales:
   if X not in table or (mode=='innovation' and 2*X not in table):complete=False;observations.append(dict(X=X,level=q,missing=True,reason='complete_target_scale_missing' if mode=='direct' else 'complete_child_scale_missing'));continue
   v=corrected_energy(table[X],weights)
   if mode=='innovation':v=corrected_energy(table[2*X],weights)-v
   root=ceil_root(X,q);largest=max(largest,v/root);observations.append(dict(X=X,level=q,observed=str(v),root=root,missing=False))
  constants[str(q)]=str(largest) if complete else None
 return constants,observations
def score(rows,weights,scales,levels,constants,mode='direct'):
 _,observations=refit(rows,weights,scales,levels,mode);out=[]
 for o in observations:
  c=constants.get(str(o['level']));missing=o['missing'] or c is None
  if missing:out.append(dict(o,missing=True,finite_pass=None));continue
  bound=rational(c)*o['root'];v=rational(o['observed']);out.append(dict(o,bound=str(bound),margin=str(bound-v),finite_pass=v<=bound))
 return out
def verify_quantization(float_weights,rational_weights,denominator=64):
 integer(denominator,1);require(len(float_weights)==len(rational_weights),'quantization length')
 for a,b in zip(float_weights,rational_weights):require(F(float(a)).limit_denominator(denominator)==rational(b),'quantization mismatch')
 return True
def verify_ridge_kkt(matrix,linear,weights,ridge,box=8):
 """Objective a+2g.w+w^T M w+ridge*||w||², symmetric PSD M.
 Exact box KKT is sufficient for convex minimum; checks M PSD separately.
 """
 M=[[rational(v) for v in row] for row in matrix];g=list(map(rational,linear));w=list(map(rational,weights));lam=rational(ridge);B=rational(box);n=len(w)
 require(lam>=0 and B>0 and len(g)==n and len(M)==n and all(len(row)==n for row in M),'ridge domains')
 require(all(M[i][j]==M[j][i] for i in range(n) for j in range(n)),'symmetry')
 # Exact PSD Schur elimination. A zero pivot requires its entire remaining row zero.
 A=[row[:] for row in M]
 for i in range(n):
  require(A[i][i]>=0,'nonPSD matrix')
  if not A[i][i]:require(all(A[i][j]==0 for j in range(i+1,n)),'nonPSD zero pivot');continue
  pivot=A[i][i]
  for j in range(i+1,n):
   for k in range(j,n):A[j][k]-=A[i][j]*A[i][k]/pivot;A[k][j]=A[j][k]
 for i,x in enumerate(w):
  require(-B<=x<=B,'box violation');grad=g[i]+sum(M[i][j]*w[j] for j in range(n))+lam*x
  require(grad==0 if -B<x<B else grad>=0 if x==-B else grad<=0,'KKT sign failure')
 return True

def source_profile(X,feature):
 feature=feature_descriptor(feature);N=2*X-1;tab=factor_tables(N);least,e,core,omega=tab;c=coefficients(N,1,1,tab);z=floor_power(X,feature['theta']);u=math.isqrt(X);classes=[0]*(N+1);full=[0]*(N+1);retained=[0]*(N+1);removed=[0]*(N+1)
 for n in range(2,N+1):
  if least[n]<=z and core[n]<=u and e[n]%2==0:
   classes[n]=1 if core[n]==1 else 2 if omega[core[n]]>feature['core_depth'] else 3
   full[n]=c[n]
   if classes[n]==3:removed[n]=c[n]
   else:retained[n]=c[n]
 def prefix(a):
  out=[0]*len(a)
  for n in range(1,len(a)):out[n]=out[n-1]+a[n]
  return out
 return dict(X=X,feature_id=feature['feature_id'],cutoffs=dict(z=z,u=u),source_horizon=N,full_prefix_sha256=digest(prefix(full)),retained_prefix_sha256=digest(prefix(retained)),removed_prefix_sha256=digest(prefix(removed)),coverage_sha256=digest(classes[1:]),class_counts=[classes[1:].count(i) for i in range(4)],coefficient_reconstruction_verified=True,prefix_reconstruction_verified=True)

def verify_source_profiles(value,scales,features=FEATURES):
 expected={(X,feature_descriptor(f)['feature_id']) for X in scales for f in features};seen=set();lookup={}
 for record in value['source_profiles']:
  key=(record['X'],record['feature_id']);require(key in expected and key not in seen,'source profile key');seen.add(key)
  feature=next(f for f in features if feature_descriptor(f)['feature_id']==key[1]);truth=source_profile(key[0],feature)
  require(record==truth,'complete source profile mismatch');lookup[key]=digest(truth)
 require(seen==expected,'missing source profile')
 for row in value['rows']:require(row['source_profile_sha256']==[lookup[row['X'],feature_descriptor(f)['feature_id']] for f in features],'row source-profile links')
 return True

def verify_actual_provenance(value,targets):
 N=integer(value['complete_horizon'],1);tab=factor_tables(N);expected={(1,1)}|{(t['r'],t['l']) for t in targets};seen=set()
 for rec in value['source_provenance']:
  key=(rec['r'],rec['l']);require(key in expected and key not in seen,'source provenance domain');seen.add(key)
  require(rec['source_sha256']==digest(coefficients(N,*key,tab)),'actual coefficient source hash');integer(rec['source_cost'])
 require(seen==expected,'missing actual source');require(value['global_bound_proved'] is False and value['RH_proved'] is False,'identity/finite evaluation cannot promote global estimate');return True

def program_weights(program,features=FEATURES):
 require(isinstance(program,dict) and set(program)=={'target','corrections','constants'},'program schema');canonical_target(program['target']);ids=[feature_descriptor(f)['feature_id'] for f in features];w=[F(0)]*len(ids);seen=set()
 for term in program['corrections']:
  require(set(term)=={'feature','weight'},'correction schema');f=feature_descriptor(term['feature']);fid=f['feature_id'];require(fid in ids and fid not in seen,'unknown/duplicate correction');seen.add(fid);w[ids.index(fid)]=rational(term['weight'])
 return w

def verify_program_fit(program,rows,scales,levels,features=FEATURES):
 weights=program_weights(program,features)
 for mode in ('direct','innovation'):
  constants,_=refit(rows,weights,scales,levels,mode);require(program['constants'][mode]==constants,'exact fitted constants mismatch')
 return True

def verify_ridge_record(record,pooled):
 require(record['status']=='available','no optimum in failed record');support=record['support_indices'];require(support and len(set(support))==len(support),'support uniqueness')
 for i in support:integer(i,1);require(i<len(pooled),'support domain')
 ridge=rational(record['ridge']);require(ridge>0,'positive ridge');box=rational(record['box']);require(box==8,'declared box')
 M=[[pooled[i][j] for j in support] for i in support];g=[pooled[0][i] for i in support];Q=[[M[i][j]+(ridge if i==j else 0) for j in range(len(support))] for i in range(len(support))]
 require(record['normal_matrix']==[[str(x) for x in row] for row in Q],'ridge matrix origin');require(record['linear']==list(map(str,g)) and rational(record['constant'])==pooled[0][0],'ridge response origin')
 if 'quadratic_matrix' in record:require(record['quadratic_matrix']==[[str(x) for x in row] for row in M],'quadratic response origin')
 w=list(map(rational,record['exact_weights']));verify_ridge_kkt(M,g,w,ridge,box)
 require(record['positive_definite_verified'] is True,'positive ridge matrix flag');require(record['quantized_weights']==[str(x.limit_denominator(64)) for x in w],'exact rational quantization')
 objective=pooled[0][0]+2*sum(x*y for x,y in zip(g,w))+sum(w[i]*Q[i][j]*w[j] for i in range(len(w)) for j in range(len(w)))
 require(rational(record['objective'])==objective,'ridge objective mismatch')
 gradients=[g[i]+sum(Q[i][j]*w[j] for j in range(len(w))) for i in range(len(w))]
 cert=record['KKT_certificate'];require(cert['all_KKT_verified'] is True and cert['feasible'] is True,'KKT flags');require(list(map(rational,cert['half_gradients']))==gradients,'KKT gradients');require(cert['coordinate_conditions']==[v>=0 if x==-box else v<=0 if x==box else v==0 for x,v in zip(w,gradients)],'KKT coordinate conditions')
 return True

def verify_search_archive(archive,profile,features=None):
 if 'status' in profile:require(profile['status']=='available','profile unavailable');profile=profile['value']
 features=[feature_descriptor(f) for f in (features or profile['features'])];target=canonical_target(archive['target']);require(len(target['filter'])<=target['r']+target['l'],'fixed-filter conditional pole gate');tid=digest(target);require(archive['target_id']==tid,'archive target hash');require(archive['features']==features and archive['dictionary_sha256']==digest(features),'archive feature dictionary')
 rows=[r for r in profile['rows'] if r['target_id']==tid];scales=archive['training_scales'];levels=archive['levels'];byX={r['X']:r for r in rows};require(all(X in byX for X in scales),'complete training rows');size=len(features)+1
 pooled=[[sum(normalized_matrix(byX[X])[i][j] for X in scales) for j in range(size)] for i in range(size)]
 candidate_map={c['program_id']:c for c in archive['candidates']};require(len(candidate_map)==len(archive['candidates']),'candidate duplicate');seen=set()
 for entry in archive['proposal_archive']:
  if 'exact_program' not in entry:
   require(entry.get('status') in ('missing','failed','invalid') and entry.get('discarded') is True,'missing attempt retained');continue
  program=entry['exact_program'];pid=digest(program);require(entry['program_id']==pid and pid in candidate_map,'exact candidate hash');weights=program_weights(program,features);verify_program_fit(program,rows,scales,levels,features)
  require(canonical_target(program['target'])==target,'program target unchanged')
  expected_obs=[]
  for mode in ('direct','innovation'):
   _,obs=refit(rows,weights,scales,levels,mode);expected_obs.extend(dict(o,mode=mode) for o in obs)
  require(entry['fit_observations']==expected_obs,'fit observations exact')
  origin=entry['origin'];kind=origin['kind']
  if kind=='baseline':require(not program['corrections'],'baseline zero corrections')
  elif kind=='singleton':
   require(len(program['corrections'])==1 and program['corrections'][0]['feature']['feature_id']==origin['feature_id'] and rational(program['corrections'][0]['weight'])==rational(origin['weight']),'singleton production')
  elif kind=='ridge_fit':
   solver=origin['solver'];verify_ridge_record(solver,pooled);key='exact_weights' if origin['variant']=='exact' else 'quantized_weights';require(origin['variant'] in ('exact','quantized'),'ridge variant');expected=[F(0)]*len(features)
   for i,w in zip(solver['support_indices'],solver[key]):expected[i-1]=rational(w)
   require(weights==expected,'ridge program coefficients')
  else:raise ValueError('unknown production origin')
  alias=pid in seen;require(entry['alias_of']==(pid if alias else None) and entry['discarded']==alias,'alias retention');seen.add(pid)
 for pid,candidate in candidate_map.items():
  require(pid in seen and digest(candidate['program'])==pid,'candidate archive coverage');require(candidate['global_bound_proved'] is False,'finite candidate cannot prove bound')
  require(candidate['conditional_correction_bridge'] is True,'conditional correction bridge flag')
  program=candidate['program'];weights=program_weights(program,features)
  for mode in ('direct','innovation'):
   truth=score(rows,weights,scales,levels,program['constants'][mode],mode);recorded=candidate['training_score']['modes'][mode]['observations']
   require(len(truth)==len(recorded),'score count')
   truthmap={(o['X'],o['level']):o for o in truth}
   for o in recorded:
    t=truthmap[o['X'],o['level']]
    for field in ('missing','finite_pass'):require(o[field]==t[field],'score status')
    if not t['missing']:
     for field in ('observed','bound','margin'):require(rational(o[field])==rational(t[field]),'score arithmetic')
 return dict(verified=True,candidates=len(candidate_map),attempts=len(archive['proposal_archive']),global_bound_proved=False)

def verify_profile_bundle(profile,scales,targets,features=FEATURES):
 require(isinstance(profile,dict) and profile.get('status')=='available','complete available profile required');value=profile['value'];declared=[feature_descriptor(f) for f in features]
 require(value['features']==declared,'ordered features mismatch');require(value['complete_horizon']==2*max(scales)-1,'complete horizon mismatch')
 result=verify_profile(value,scales,targets,declared);verify_source_profiles(value,scales,declared);verify_actual_provenance(value,targets)
 return dict(result,source_profiles_verified=True,actual_provenance_verified=True)

class _IndependentCache:
 """Factor once at the complete horizon; share actual c/core sources per X."""
 def __init__(self,N,targets,use_numpy=True):
  self.N=N;self.tables=factor_tables(N);self.coeff={};self.prefix={};self.absolute={};self.np=None
  if use_numpy:
   try:import numpy as np;self.np=np
   except ImportError:pass
  for r,l in {(1,1)}|{(t['r'],t['l']) for t in targets}:
   a=coefficients(N,r,l,self.tables);absolute=sum(map(abs,a));self.absolute[r,l]=absolute
   if self.np is not None and absolute<=2**63-1:
    a=self.np.asarray(a,dtype=self.np.int64);P=self.np.cumsum(a,dtype=self.np.int64)
   else:
    P=[0]*len(a)
    for n in range(1,len(a)):P[n]=P[n-1]+a[n]
   self.coeff[r,l]=a;self.prefix[r,l]=P
  if self.np is not None:self.tables=tuple(self.np.asarray(t,dtype=self.np.int64) for t in self.tables)
 def py(self,a):return a.tolist() if hasattr(a,'tolist') else a
 def regions(self,X,features):
  T=2*X-1;least,e,core,omega=self.tables;c=self.coeff[1,1];safe=self.np is not None and self.absolute[1,1]<=2**63-1;prefixes=[];records=[]
  for feature in features:
   z=floor_power(X,feature['theta']);u=math.isqrt(X);h=feature['core_depth']
   if safe:
    np=self.np;cores=core[:T+1];active=(least[:T+1]<=z)&(e[:T+1]%2==0)&(cores<=u);active[:2]=False
    classes=np.zeros(T+1,dtype=np.int64);classes[active]=3;classes[active&(cores==1)]=1;classes[active&(omega[cores]>h)]=2
    full=np.cumsum(np.where(active,c[:T+1],0),dtype=np.int64);retained=np.cumsum(np.where((classes==1)|(classes==2),c[:T+1],0),dtype=np.int64);removed=full-retained
    counts=np.bincount(classes[1:],minlength=4).tolist()
   else:
    classes=[0]*(T+1);full=[0]*(T+1);retained=[0]*(T+1);removed=[0]*(T+1)
    for n in range(1,T+1):
     if n>=2 and least[n]<=z and e[n]%2==0 and core[n]<=u:classes[n]=1 if core[n]==1 else 2 if omega[core[n]]>h else 3
     a=int(c[n]) if classes[n] else 0;r=a if classes[n] in (1,2) else 0;full[n]=full[n-1]+a;retained[n]=retained[n-1]+r;removed[n]=removed[n-1]+a-r
    counts=[classes[1:].count(i) for i in range(4)]
   records.append(dict(X=X,feature_id=feature['feature_id'],cutoffs=dict(z=z,u=u),source_horizon=T,full_prefix_sha256=digest(self.py(full)),retained_prefix_sha256=digest(self.py(retained)),removed_prefix_sha256=digest(self.py(removed)),coverage_sha256=digest(self.py(classes[1:])),class_counts=counts,coefficient_reconstruction_verified=True,prefix_reconstruction_verified=True));prefixes.append(retained)
  return prefixes,records
 def gram(self,X,target,features,residuals):
  target=canonical_target(target);Q=math.lcm(*(F(t['weight']).denominator for t in target['filter']));weights=[(t['divisor'],int(F(t['weight'])*Q)) for t in target['filter']];inputs=[self.prefix[target['r'],target['l']]]+residuals;cols=[]
  for P in inputs:
   maximum_prefix=int(self.np.max(self.np.abs(P))) if self.np is not None and hasattr(P,'dtype') else max(abs(int(v)) for v in P)
   bound=sum(abs(w) for d,w in weights)*maximum_prefix
   if self.np is not None and hasattr(P,'dtype') and bound<=2**63-1:
    np=self.np;n=np.arange(X,2*X,dtype=np.int64);col=np.zeros(X,dtype=np.int64)
    for d,w in weights:col+=w*P[n//d]
   else:col=[sum(w*int(P[n//d]) for d,w in weights) for n in range(X,2*X)]
   cols.append(col)
  maximum=max(int(self.np.max(self.np.abs(col))) if self.np is not None and hasattr(col,'dtype') else max(abs(int(v)) for v in col) for col in cols);size=len(cols);bound=X*maximum**2
  if self.np is not None and bound<=2**63-1:
   mat=self.np.array(cols,dtype=self.np.int64);G=(mat@mat.T).tolist()
  else:
   G=[[0]*size for _ in range(size)]
   for i in range(size):
    for j in range(i,size):G[i][j]=G[j][i]=sum(int(a)*int(b) for a,b in zip(cols[i],cols[j]))
  return dict(X=X,target_id=digest(target),feature_ids=['base_G']+[f['feature_id'] for f in features],gram_numerators=G,gram_base_denominator=X*X*Q*Q,correction_denominators=[1]+[ceil_root(X,2*(f['core_depth']+1)) for f in features],weight_common_denominator=Q,prefix_abs_bound=maximum,int64_gram_abs_bound=bound,base_energy=str(F(G[0][0],X*X*Q*Q)))

def verify_profile_bundle(profile,scales,targets,features=FEATURES,*,use_numpy=True):
 require(isinstance(profile,dict) and profile.get('status')=='available','complete available profile required');value=profile['value'];features=[feature_descriptor(f) for f in features];targets=[canonical_target(t) for t in targets];scales=list(scales)
 require(scales and len(set(scales))==len(scales),'nonempty distinct scales');require(value['features']==features and value['targets']==targets,'ordered dimensions');N=2*max(scales)-1;require(value['complete_horizon']==N,'horizon');cache=_IndependentCache(N,targets,use_numpy)
 source_records={(r['X'],r['feature_id']):r for r in value['source_profiles']};require(len(source_records)==len(value['source_profiles'])==len(scales)*len(features),'source profile completeness');rows={(r['X'],r['target_id']):r for r in value['rows']};require(len(rows)==len(value['rows'])==len(scales)*len(targets),'row completeness')
 for X in scales:
  residuals,records=cache.regions(X,features)
  for record in records:require(source_records.get((X,record['feature_id']))==record,'actual source profile mismatch')
  for target in targets:
   truth=cache.gram(X,target,features,residuals);row=rows.get((X,digest(target)));require(row is not None,'actual row missing')
   for field,val in truth.items():require(row.get(field)==val,'actual '+field+' mismatch')
   require(row['source_profile_sha256']==list(map(digest,records)),'source links');require(row['complete_block'] is True and row['all_base_corrector_cross_terms_retained'] is True and row['global_bound_proved'] is False,'row flags')
 provenance=value['source_provenance'];seen=set()
 for rec in provenance:
  key=(rec['r'],rec['l']);require(key in cache.coeff and key not in seen,'source provenance');seen.add(key)
  require(rec['source_sha256']==digest(cache.py(cache.coeff[key])) and rec['prefix_sha256']==digest(cache.py(cache.prefix[key])),'actual coefficient/prefix provenance');require(rec['absolute_coefficient_sum']==cache.absolute[key] and rec['compact_prefix_int64_proved_safe']==(cache.absolute[key]<=2**63-1),'source compact safety');integer(rec['source_cost'])
 require(seen==set(cache.coeff),'missing provenance');require(value['global_bound_proved'] is False and value['RH_proved'] is False and value['actual_all_scale_signed_bound_proved'] is False,'no global promotion')
 return dict(verified=True,rows=len(rows),source_profiles_verified=True,actual_provenance_verified=True,global_bound_proved=False)

def _expected_productions(features):
 ids=[f['feature_id'] for f in features];expected={('baseline',)};groups={}
 for fid in ids:
  for weight in ('-4','-1','-1/4','1/4','1','4'):expected.add(('singleton',fid,weight))
 for h in (1,2,3,5):
  indices=[i+1 for i,f in enumerate(features) if f['core_depth']==h]
  if indices:groups['depth_'+str(h)]=indices
 for theta in ('1/6','1/3','1/2'):
  indices=[i+1 for i,f in enumerate(features) if f['theta']==theta]
  if indices:groups['theta_'+theta]=indices
 groups['all']=list(range(1,len(features)+1))
 for group in groups:
  for ridge in ('1/1024','1/64','1'):
   for variant in ('exact','quantized'):expected.add(('ridge_fit',group,ridge,variant))
 return expected,groups

# Preserve the arithmetic/optimizer audit, then strengthen complete production coverage.
_verify_search_archive_arithmetic=verify_search_archive
def verify_search_archive(archive,profile,features=None):
 value=profile['value'] if 'status' in profile else profile;features=[feature_descriptor(f) for f in (features or value['features'])];declared={digest({'theta':theta,'core_depth':h}) for h in (1,2,3,5) for theta in ('1/6','1/3','1/2')}
 require(all(f['feature_id'] in declared for f in features),'declared grammar features');expected,groups=_expected_productions(features);seen=set();origins={}
 for entry in archive['proposal_archive']:
  origin=entry['origin'];kind=origin['kind']
  if kind=='baseline':key=('baseline',);require(set(origin)=={'kind'},'baseline origin')
  elif kind=='singleton':
   require(set(origin)=={'kind','feature_id','weight'},'singleton origin');key=(kind,origin['feature_id'],origin['weight'])
  elif kind=='ridge_fit':
   require(set(origin)<= {'kind','group','ridge','variant','solver'} and {'kind','group','ridge','variant'}<=set(origin),'ridge origin');key=(kind,origin['group'],origin['ridge'],origin['variant'])
   if 'solver' in origin and origin['solver'].get('status')=='available':
    solver=origin['solver'];require(solver['support_indices']==groups.get(origin['group']) and rational(solver['ridge'])==rational(origin['ridge']),'ridge group support/origin')
  else:raise ValueError('unknown proposal origin')
  require(key in expected and key not in seen,'omitted/duplicate/undeclared production');seen.add(key)
  if 'program_id' in entry:origins.setdefault(entry['program_id'],[]).append(origin)
 require(seen==expected,'missing required proposal attempts')
 for candidate in archive['candidates']:require(candidate['origins']==origins.get(candidate['program_id']),'candidate origin metadata')
 return _verify_search_archive_arithmetic(archive,profile,features)

def score_schema(program,profile,features,scales,levels):
 if 'status' in profile:
  require(profile['status']=='available','profile unavailable');profile=profile['value']
 features=[feature_descriptor(f) for f in features];tid=digest(canonical_target(program['target']));rows=[r for r in profile['rows'] if r['target_id']==tid];weights=program_weights(program,features);modes={}
 for mode in ('direct','innovation'):
  observations=score(rows,weights,scales,levels,program['constants'][mode],mode);lookup={(o['X'],o['level']):o for o in observations};out=[]
  for X in scales:
   for q in levels:
    o=lookup[X,q];value=o.get('observed');constant=program['constants'][mode].get(str(q));missing=o['missing']
    reason=None if not missing else ('complete_target_scale_missing' if mode=='direct' else 'complete_child_scale_missing') if value is None else 'unknown_level_constant'
    out.append(dict(X=X,level=q,observed=value,bound=o.get('bound'),margin=o.get('margin'),missing=missing,reason=reason,finite_pass=o['finite_pass'] if 'finite_pass' in o else None,global_bound_proved=False))
  modes[mode]=dict(observations=out,finite_passes=sum(o['finite_pass'] is True for o in out),finite_failures=sum(o['finite_pass'] is False for o in out),missing_cases=sum(o['missing'] for o in out),finite_cases=len(out))
 return dict(modes=modes,global_bound_proved=False)

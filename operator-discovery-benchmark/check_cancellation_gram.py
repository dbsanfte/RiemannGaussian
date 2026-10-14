"""Independent rational PSD check via ALL principal minors (not producer LDL)."""
from fractions import Fraction as F
from itertools import combinations

def rational(x,max_bits=4096):
 if type(x) not in (int,str,F):raise ValueError('exact rational only')
 if type(x)is str:
  if len(x)>4*max_bits+4 or any(c not in '0123456789+-/' for c in x):raise ValueError('bounded rational text')
 q=F(x)
 if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_bits:raise OverflowError('coefficient bits')
 return q

def verify_psd(matrix,*,max_dimension=12,max_operations=1000000,max_coefficient_bits=4096):
 if any(type(n)is not int or n<1 for n in (max_dimension,max_operations,max_coefficient_bits)):raise ValueError('strict positive limits')
 if type(matrix)is not list or not matrix or len(matrix)>max_dimension:raise ValueError('bounded matrix')
 n=len(matrix)
 if any(type(r)is not list or len(r)!=n for r in matrix):raise ValueError('square matrix')
 a=[[rational(x,max_coefficient_bits) for x in r] for r in matrix]
 if any(a[i][j]!=a[j][i] for i in range(n) for j in range(n)):raise ValueError('symmetric matrix')
 if (2**n)*n**3>max_operations:raise OverflowError('principal-minor work preflight')
 used=0;minors=[]
 def charged(q):
  nonlocal used
  used+=1
  if used>max_operations:raise OverflowError('minor work')
  return rational(q,max_coefficient_bits)
 for size in range(1,n+1):
  for ids in combinations(range(n),size):
   b=[[a[i][j] for j in ids] for i in ids];det=F(1)
   for k in range(size):
    pivot=next((i for i in range(k,size) if b[i][k]),None)
    if pivot is None:det=F(0);break
    if pivot!=k:b[k],b[pivot]=b[pivot],b[k];det=-det
    v=b[k][k];det=charged(det*v)
    for i in range(k+1,size):
     ratio=charged(b[i][k]/v)
     for j in range(k+1,size):b[i][j]=charged(b[i][j]-ratio*b[k][j])
   if det<0:raise ValueError('negative principal minor '+repr(ids))
   minors.append(dict(indices=list(ids),determinant=str(det)))
 return dict(PSD_verified=True,dimension=n,principal_minors=minors,operations=used,global_bound_proved=False,RH_proved=False)

def atom_blocks(X):
 import check_cancellation_arithmetic_run as I
 return {r:[[I.P.canonical(I.contrast(a,t)) for a in ['prefix','half','even','mod3one','prime']] for t in (range(X,2*X) if r=='parent' else range(2*X,4*X))] for r in ['parent','child']}

def gram_polynomial(matrix,blocks,H):
 import check_cancellation_arithmetic_run as I
 P=I.P;out={};A=[[rational(v) for v in row] for row in matrix]
 for atoms in blocks:
  ps=[P.parse(a,H) for a in atoms]
  if len(ps)!=5:raise ValueError('five atoms')
  for i in range(5):
   for j in range(5):out=P.add(out,P.multiply(ps[i],ps[j]),A[i][j])
 return out

def verify_primal(instances,scales,result):
 import check_cancellation_arithmetic_run as I
 import check_grouped_arithmetic as G
 P=I.P
 if result.get('status')!='finite_PSD_certificate':raise ValueError('finite PSD result required')
 weights=result['weights'];grams=result['grams'];proofs={r:verify_psd(grams[r]) for r in ['parent','child']};slacks=[]
 if len(result['certificates'])!=len(instances):raise ValueError('certificate coverage')
 for k,inst in enumerate(instances):
  lhs,sq,rel=G.columns(inst);rhs={}
  if len(weights['square_weights'])!=len(sq) or len(weights['relation_weights'])!=len(rel):raise ValueError('shared groups')
  for c,p in zip(weights['square_weights'],sq):
   c=rational(c)
   if c<0:raise ValueError('negative square coefficient')
   rhs=P.add(rhs,p,c)
  for c,p in zip(weights['relation_weights'],rel):rhs=P.add(rhs,p,rational(c))
  blocks=atom_blocks(scales[k]) if k<len(scales) else {'parent':[],'child':[]}
  for r in ['parent','child']:rhs=P.add(rhs,gram_polynomial(grams[r],blocks[r],inst['horizon']))
  residue=P.add(lhs,rhs,F(-1))
  if any(m for m in residue) or residue.get((),F(0))<0:raise ValueError('full original polynomial residual')
  slacks.append(str(residue.get((),F(0))))
  record=result['certificates'][k]
  if 'Gram_proofs' in record:
   for region in ['parent','child']:
    gp=record['Gram_proofs'][region];expected=gram_polynomial(grams[region],blocks[region],inst['horizon'])
    if P.parse(gp['polynomial'],inst['horizon'])!=expected:raise ValueError('archived Gram polynomial')
    expanded={}
    for term in gp['squares']:
     w=rational(term['weight'])
     if w<0:raise ValueError('negative archived Gram square')
     a=P.parse(term['poly'],inst['horizon']);expanded=P.add(expanded,P.multiply(a,a),w)
    if expanded!=expected:raise ValueError('archived Gram SOS crosses')
    if gp['decomposition']['matrix']!=grams[region]:raise ValueError('archived Gram matrix')
  cert=record['certificate'];G.verify_certificate(cert)
  if cert['target']!=inst['target'] or cert['horizon']!=inst['horizon'] or cert['lhs']!=inst['lhs']:raise ValueError('original target certificate binding')
 if result['constant_slacks']!=slacks:raise ValueError('exact scalar slacks')
 return dict(verified=True,PSD_proofs=proofs,constant_slacks=slacks,global_bound_proved=False,RH_proved=False)

def verify_dual(instances,scales,dual):
 import check_cancellation_arithmetic_run as I
 import check_grouped_arithmetic as G
 P=I.P;G.verify_joint_dual(instances,dual,allow_constant_slack=True)
 y={(r['instance'],tuple(r['m'])):rational(w) for r,w in zip(dual['monomials'],dual['weights'])};Hs={};cross=[]
 for region in ['parent','child']:
  H=[[F(0)]*5 for _ in range(5)]
  for k,X in enumerate(scales):
   for atoms in atom_blocks(X)[region]:
    ps=[P.parse(a,instances[k]['horizon']) for a in atoms]
    for i in range(5):
     for j in range(i,5):
      p=P.multiply(ps[i],ps[j])
      if any((k,m) not in y for m in p):raise ValueError('complete Gram dual domain')
      H[i][j]+=sum((c*y[k,m] for m,c in p.items()),F(0));H[j][i]=H[i][j]
  verify_psd(H)
  if dual['gram_duals'][region]['matrix']!=[[str(v) for v in row] for row in H]:raise ValueError('full Gram dual entries')
  cross.extend(str(H[i][j]) for i in range(5) for j in range(i+1,5));Hs[region]=[[str(v) for v in row] for row in H]
 if dual['extra_cross_dots']!=cross:raise ValueError('extra cross dots')
 return dict(verified=True,full_Gram_dual_matrices=Hs,declared_finite_cone_only=True,global_bound_proved=False,RH_proved=False)

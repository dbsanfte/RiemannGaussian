"""Exact rational PSD Grams and complete shared-block SOS conversion.
No numerical PSD proposal, coefficient response or global bound is admitted.
"""
from fractions import Fraction as F
import re
import arithmetic_cycle_language as L

def rational(x,*,max_bits=4096):
 if type(max_bits)is not int or max_bits<1:raise ValueError('positive bit limit')
 if type(x)not in (str,int,F):raise ValueError('exact rational matrix entry')
 if type(x)is str:
  if len(x)>2*max_bits+4:raise OverflowError('raw rational string size')
  if re.fullmatch(r'-?[0-9]+(?:/[0-9]+)?',x) is None:raise ValueError('integer/rational literal only')
  nums=x.split('/')
  for q in nums:
   if len(q.lstrip('-0'))>max_bits:raise OverflowError('raw rational integer size')
 elif type(x)is int:
  if abs(x).bit_length()>max_bits:raise OverflowError('raw integer bits')
 else:
  if max(abs(x.numerator).bit_length(),x.denominator.bit_length())>max_bits:raise OverflowError('raw Fraction bits')
 q=F(x)
 if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_bits:raise OverflowError('rational coefficient bits')
 return q

def ldlt_psd(matrix,*,max_dimension=64,max_operations=1000000,max_coefficient_bits=4096):
 if any(type(n)is not int or n<1 for n in (max_dimension,max_operations,max_coefficient_bits)):raise ValueError('positive strict limits')
 if type(matrix)is not list or not matrix or len(matrix)>max_dimension:raise ValueError('nonempty bounded square matrix')
 n=len(matrix)
 if any(type(row)is not list or len(row)!=n for row in matrix):raise ValueError('square matrix')
 A=[[rational(v,max_bits=max_coefficient_bits) for v in row] for row in matrix]
 if any(A[i][j]!=A[j][i] for i in range(n) for j in range(n)):raise ValueError('exact symmetry required')
 used=0
 def check(q):
  nonlocal used
  used+=1
  if used>max_operations:raise OverflowError('LDL operations')
  if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits:raise OverflowError('LDL coefficient bits')
 for row in A:
  for q in row:check(q)
 R=[row[:] for row in A];columns=[];weights=[]
 for k in range(n):
  pivot=R[k][k]
  if pivot<0:raise ValueError('negative PSD pivot')
  if pivot==0:
   if any(R[i][k] for i in range(k+1,n)):raise ValueError('zero PSD pivot with nonzero remainder row')
   continue
  v=[F(0)]*n;v[k]=F(1)
  for i in range(k+1,n):v[i]=R[i][k]/pivot;check(v[i])
  columns.append(v);weights.append(pivot)
  for i in range(k+1,n):
   for j in range(i,n):
    R[i][j]-=pivot*v[i]*v[j];check(R[i][j]);R[j][i]=R[i][j]
  for i in range(k,n):R[k][i]=R[i][k]=F(0)
 # Explicit reconstruction catches dropped crosses or decomposition mistakes.
 rebuilt=[[F(0) for j in range(n)] for i in range(n)]
 for i in range(n):
  for j in range(n):
   for d,v in zip(weights,columns):
    term=d*v[i]*v[j];check(term);rebuilt[i][j]+=term;check(rebuilt[i][j])
 if rebuilt!=A:raise ValueError('exact LDL reconstruction mismatch')
 return dict(matrix=[[str(q) for q in row] for row in A],positive_pivots=list(map(str,weights)),covectors=[[str(q) for q in v] for v in columns],rank=len(weights),dimension=n,PSD_verified=True,operations=used,global_bound_proved=False,RH_proved=False)

def pair_square_coordinates(matrix):
 """Any symmetric G: quadratic form uses diagonal squares and +pair squares.
 Cross coefficient2Gij is retained. Diagonal coefficients may be NEGATIVE;
 this is a signed identity map, not a nonnegative basis certificate.
 """
 n=len(matrix);G=[[rational(q) for q in row] for row in matrix]
 if not n or any(len(row)!=n for row in G) or any(G[i][j]!=G[j][i] for i in range(n) for j in range(n)):raise ValueError('symmetric matrix')
 return dict(diagonal=[str(G[i][i]-sum((G[i][j] for j in range(n) if j!=i),F(0))) for i in range(n)],plus_pairs=[dict(i=i,j=j,coefficient=str(G[i][j])) for i in range(n) for j in range(i+1,n)],scope='signed exact expansion; PSD is checked separately')

def gram_polynomial(matrix,atoms,*,max_terms=100000,max_operations=1000000):
 n=len(atoms)
 if len(matrix)!=n or any(len(row)!=n for row in matrix):raise ValueError('Gram atom dimensions')
 p=[L.load_poly(a) for a in atoms];out={};used=0
 for i in range(n):
  for j in range(n):
   used+=len(p[i])*len(p[j])
   if used>max_operations:raise OverflowError('complete Gram expansion work')
   out=L.add(out,L.scale(L.mul(p[i],p[j],max_terms=max_terms,max_operations=max_operations),rational(matrix[i][j])))
   if len(out)>max_terms:raise OverflowError('Gram terms')
 return out

def instantiate_sos(matrix,blocks,*,max_terms=100000,max_operations=1000000,**ldl_limits):
 """blocks[t] is a list of canonical atom polynomials, same G at EVERY t.
 Atoms must have zero formalconstant; actual block cutoffs belong to caller.
 """
 dec=ldlt_psd(matrix,max_operations=max_operations,**ldl_limits);n=dec['dimension'];squares=[];total={}
 if type(blocks)is not list:raise ValueError('complete blocks list')
 used=dec['operations']
 if len(blocks)*n*n>max_operations:raise OverflowError('shared blocks work preflight')
 for atoms in blocks:
  if type(atoms)is not list or len(atoms)!=n:raise ValueError('same shared Gram dimensions')
  ps=[L.load_poly(a) for a in atoms]
  used+=sum(len(a)*len(b) for a in ps for b in ps)
  if used>max_operations:raise OverflowError('shared Gram cumulative work')
  if any(() in p for p in ps):raise ValueError('primitive atoms must have zero formalconstant')
  for d,v in zip(dec['positive_pivots'],dec['covectors']):
   p=L.add(*(L.scale(a,rational(c)) for a,c in zip(ps,v)))
   if p:squares.append(dict(weight=d,poly=L.dump_poly(p)))
  total=L.add(total,gram_polynomial(matrix,atoms,max_terms=max_terms,max_operations=max_operations))
  if len(total)>max_terms:raise OverflowError('shared Gram total terms')
 rhs={}
 for s in squares:
  p=L.load_poly(s['poly']);used+=len(p)**2
  if used>max_operations:raise OverflowError('shared SOS cumulative work')
  rhs=L.add(rhs,L.scale(L.mul(p,p,max_terms=max_terms,max_operations=max_operations),rational(s['weight'])))
 if rhs!=total:raise ValueError('full shared Gram/SOS mismatch')
 return dict(squares=squares,polynomial=L.dump_poly(total),decomposition=dec,shared_Gram_verified=True,all_cross_terms_retained=True,global_bound_proved=False,RH_proved=False)

def diagonal_congruence(matrix,scales):
 """P'_i=s_i P_i, G'ij=Gij/(s_i*s_j), nonzero exact s_i.
 Preserves quadratic polynomial and PSD; no fitted scale-dependent G allowed.
 """
 s=list(map(rational,scales));n=len(s)
 if any(not q for q in s) or len(matrix)!=n or any(len(row)!=n for row in matrix):raise ValueError('invertible atom normalization')
 return [[str(rational(matrix[i][j])/(s[i]*s[j])) for j in range(n)] for i in range(n)]

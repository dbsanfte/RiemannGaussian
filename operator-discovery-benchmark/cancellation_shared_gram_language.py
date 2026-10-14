"""Exact shared Gram SOS retaining constants and skipping zero products.
All atom syntax is validated even when its Gram coefficient vanishes.
"""
from fractions import Fraction as F
import time
import arithmetic_cycle_language as L
from cancellation_gram_language import ldlt_psd, rational

def instantiate_sos(matrix,blocks,*,max_terms=100000,max_operations=1000000,deadline=None,**ldl_limits):
 bits=ldl_limits.get('max_coefficient_bits',4096)
 dec=ldlt_psd(matrix,max_operations=max_operations,**ldl_limits)
 n=dec['dimension'];used=dec['operations'];squares=[];total={};rhs={}
 def charge(work=1):
  nonlocal used
  used+=work
  if used>max_operations:raise OverflowError('shared Gram cumulative actual work')
  if deadline is not None and time.monotonic()>deadline:raise TimeoutError('shared Gram deadline')
 def check(poly):
  if len(poly)>max_terms:raise OverflowError('shared Gram term cap')
  for q in poly.values():rational(q,max_bits=bits)
  return poly
 def product(a,b):
  charge(len(a)*len(b))
  return check(L.mul(a,b,max_terms=max_terms,max_operations=max_operations))
 def merge(dest,p,w):
  charge(len(p))
  for m,q in p.items():
   value=rational(dest.get(m,F(0))+w*q,max_bits=bits)
   if value:dest[m]=value
   else:dest.pop(m,None)
  check(dest)
 G=[[rational(q,max_bits=bits)for q in row]for row in dec['matrix']]
 active=[(a,b,G[a][b]*(1 if a==b else 2))for a in range(n)for b in range(a,n)if G[a][b]]
 if type(blocks)is not list:raise ValueError('complete blocks list')
 for atoms in blocks:
  charge(n)
  if type(atoms)is not list or len(atoms)!=n:raise ValueError('same shared Gram dimensions')
  ps=[]
  for atom in atoms:
   if type(atom)is not list or len(atom)>max_terms:raise OverflowError('atom terms')
   charge(len(atom))
   for term in atom:
    if type(term)is not dict or set(term)!={'m','c'}:raise ValueError('atom term schema')
    rational(term['c'],max_bits=bits)
   ps.append(check(L.load_poly(atom)))
  for a,b,w in active:merge(total,product(ps[a],ps[b]),w)
  for d,v in zip(dec['positive_pivots'],dec['covectors']):
   p={}
   for atom,c in zip(ps,v):
    c=rational(c,max_bits=bits)
    if c:merge(p,atom,c)
   if p:
    squares.append(dict(weight=d,poly=L.dump_poly(p)))
    merge(rhs,product(p,p),rational(d,max_bits=bits))
 charge()
 if rhs!=total:raise ValueError('full shared Gram/SOS mismatch')
 return dict(squares=squares,polynomial=L.dump_poly(total),decomposition=dec,shared_Gram_verified=True,all_cross_terms_retained=True,operations=used,global_bound_proved=False,RH_proved=False)

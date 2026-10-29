#!/usr/bin/env python3
"""Tiny symbolic polynomial identity check, not native-bank factor testing."""
import json

def add(*polys):
 out={}
 for p in polys:
  for e,c in p.items():out[e]=out.get(e,0)+c
 return {e:c for e,c in out.items() if c}
def neg(p):return {e:-c for e,c in p.items()}
def mul(p,q):
 out={}
 for (i,j),a in p.items():
  for (k,l),b in q.items():out[i+k,j+l]=out.get((i+k,j+l),0)+a*b
 return {e:c for e,c in out.items() if c}
one={(0,0):1};r={(1,0):1};s={(0,1):1};r2=mul(r,r)
u=add(one,s);v=s;e1=add(one,r,r2);e2=add(r,r2,mul(r,r2));e3=mul(r,r2)
A=add(mul(u,u),neg(v),neg(mul(e1,u)),e2)
B=add(neg(mul(u,v)),mul(e1,v),neg(e3))
expected=mul(add(s,neg(r)),add(s,neg(r2)))
assert A==expected and add(A,B)=={}
# Exact integer empty-block example demonstrates why A alone is not a gate.
u0=13;v0=42;A0=u0*u0-v0-7*u0+14;B0=-u0*v0+7*v0-8
resultant=B0*B0+u0*A0*B0+v0*A0*A0
assert (A0,B0,resultant)==(50,-260,3600)
print(json.dumps({'symbolic_hit_remainder':'(s-r)(s-r^2)*(X-1)',
 'symbolic_checks':2,'empty_block_integer_example':{'clock':[1,2,4],
 'rows':[6,7],'A':A0,'B':B0,'resultant':resultant},
 'scope':'formal identity and empty-gating diagnostic only; no native counterexample'}))

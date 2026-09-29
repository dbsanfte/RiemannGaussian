#!/usr/bin/env python3
"""Optional actual-prime central cancellation diagnostic; never a certificate.

Keep the original allocation polynomial, signed product phase, distinct
squarefree prime factors, nondominant owner and central radial mask.
Earlier nested core deletions are omitted: this is a test population.
Costs omit an UNEVALUATED sqrt(E). No eventual bound is inferred.
Compare the raw hinge, the previous cubic projection (with signed center),
and the exact small-prime difference on identical labels, using the
corresponding population endpoint for each mean bound. A comparison before
sqrt(E) does not certify a shared numerical arithmetic constant.
Keep every common-coordinate direction. Never run this in ordinary CI.
"""
import argparse
import math
import json
import numpy as np
from probe_riesz_retained_discrepancy import coefficients
from probe_riesz_sieve_mean import arithmetic

def balanced(A,D,X):
 G=A.T@A; B=D@D.T
 if np.trace(G)==0 or np.trace(B)==0: return 0.
 vals,V=np.linalg.eigh(G/np.trace(G)); vals=np.maximum(vals,1e-10)
 H=(V*np.sqrt(vals))@V.T; Hinv=(V/np.sqrt(vals))@V.T
 M=H@(B/np.trace(B))@H
 es,U=np.linalg.eigh((M+M.T)/2)
 Q=np.linalg.eigh(Hinv@((U*np.sqrt(np.maximum(es,0)))@U.T)@Hinv)[1]
 assert np.max(abs(Q@Q.T-np.eye(len(Q))))<1e-9
 return math.sqrt(X)*float(np.sqrt(np.sum((A@Q)**2,axis=0)*np.sum((Q.T@D)**2,axis=1)).sum())

def probe(N,r):
 u=10001/20000; y=54.; upper=(math.floor(u**(-N)/(N+1))+2)**2; L=math.log(upper)
 pop=math.floor(math.exp(2.029*N)/(N*N+1)); cap=pop//r
 mu,phi=arithmetic(max(pop,upper)); ints=np.arange(len(phi)); primes=np.flatnonzero((phi==ints-1)&(ints>=2))
 ps=primes[(primes>N*N)&(primes<upper)]
 fs=[[] for _ in range(cap+1)]
 for p in primes[primes<=cap]:
  for n in range(int(p),cap+1,int(p)): fs[n].append(int(p))
 costs=[]; labels=0; maxreg=0.
 for b in range(cap.bit_length()):
  low=2**b; end=min(2*low,cap)
  if end<=low:continue
  P=ps[(np.log(ps)+math.log(r*end)>1.971*N)&(np.log(ps)+math.log(r*low)<=2.029*N)]
  if not len(P):continue
  lp=np.log(P); rows=[]; moments=[]
  for n in range(max(2,low+1),end+1):
   if mu[n]==0 or n%r==0 or not fs[n] or min(fs[n])<r: continue
   original=r*n; factors=[r,*fs[n]]; logs=np.log(factors); T=lp+math.log(original)
   mask=(T>1.971*N)&(T<=2.029*N)&(lp<.65*T)&(P>max(factors))
   if not mask.any():continue
   elig=[math.log(p) for p in factors if N*N<p<upper]
   poly=coefficients(N,logs,elig)@(lp[None,:]**np.arange(N+2)[:,None])
   W=-poly*np.exp(-T/2)/(original*P)*np.cos(y*T)*u**(N+1)/(L*math.factorial(N))
   rows.append(W*mask); labels+=int(mask.sum())
   if len(logs)==2:
    moments.append([0.,2*logs[0]*logs[1],3*logs[0]*logs[1]*sum(logs)])
   elif len(logs)==3:
    moments.append([0.,0.,-6*float(np.prod(logs))])
   else: moments.append([0.,0.,0.])
   if len(rows)<=10:
    d=[1]
    for p in fs[n]: d += [p*j for j in d]
    d=np.array(d); ld=np.log(d)
    pulse=np.minimum(lp[:,None],np.maximum(L-ld,0)[None,:])-np.minimum(lp[:,None],np.maximum(L-math.log(r)-ld,0)[None,:])
    direct=np.minimum(lp[:,None],np.maximum(L-np.log(np.concatenate([d,r*d])),0)[None,:])@mu[np.concatenate([d,r*d])]
    val=pulse@mu[d]; maxreg=max(maxreg,float(np.max(abs(val-direct))))
  if not rows:continue
  A=np.array(rows); k=np.arange(1,end+1,dtype=float)
  F=np.minimum(lp[:,None],np.maximum(L-np.log(k),0)[None,:])-np.minimum(lp[:,None],np.maximum(L-math.log(r)-np.log(k),0)[None,:])
  D=(F[:,:-1]-F[:,1:])*np.sqrt(k[:-1])
  assert float(np.max(np.sum(D*D,axis=1)))<=2*math.log(r)+1e-8
  cost=balanced(A,D,end)
  # Baseline raw cost on the identical labels, before extracting r.
  kk=np.arange(1,r*end+1,dtype=float)
  F0=np.minimum(lp[:,None],np.maximum(L-np.log(kk),0)[None,:])
  D0=(F0[:,:-1]-F0[:,1:])*np.sqrt(kk[:-1])
  old=balanced(A,D0,r*end)
  moment=np.asarray(moments)/(math.log(r*end)**np.arange(1,4))
  dirs=[]; md=[]; residual=D0.copy(); center=0.
  for deg in range(1,4):
   d=np.sqrt(kk[:-1])*((np.log(kk[:-1])/math.log(r*end))**deg-(np.log(kk[1:])/math.log(r*end))**deg)
   m=moment[:,deg-1].copy()
   for olddir,oldm in zip(dirs,md):
    c=float(d@olddir); d-=c*olddir; m-=c*oldm
   norm=np.linalg.norm(d); d/=norm;m/=norm;dirs.append(d);md.append(m)
   a=D0@d; residual-=a[:,None]*d[None,:]; center+=float((m@A)@a)
  cubic=balanced(A,residual,r*end)
  costs.append([end,old,cost,cubic,center])
 out=dict(N=N,leastPrime=r,labels=labels,rawCost=sum(v[1]for v in costs),differenceCost=sum(v[2]for v in costs),cubicCost=sum(v[3]for v in costs),cubicCenter=sum(v[4]for v in costs),maxIdentityError=maxreg,blocks=costs)
 return out


def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--max-order',type=int,choices=[6,8,10],default=10)
 parser.add_argument('--primes',type=int,nargs='+',choices=[2,3,5],default=[2,3,5])
 args=parser.parse_args()
 for n in [6,8,10]:
  if n>args.max_order: continue
  for r in args.primes:
   print(json.dumps(probe(n,r)),flush=True)


if __name__=='__main__':
 main()

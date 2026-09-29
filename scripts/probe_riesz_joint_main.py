#!/usr/bin/env python3
"""Optional joint signed-main probe; never run by ordinary CI.

All marked primes are summed before the final real part. The finite radial
window, physical annulus, largest-prime/cofactor ordering and exact owner
factorial allocation are retained. Actual integers, primes and squarefree
counts are enumerated. Nonowner allocation and earlier nested masks are
not all included. The physical short cutoffs at orders 14/16/18 are only
1/2/3, respectively; these tests do not establish a large-order rate for
exponentially growing cutoffs. Floating outputs are not certificates or
bounds on the whole core. Default runs omit the larger order-18 job.
"""
import sys,math,json,time
import numpy as np
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from probe_riesz_cofactor_main import arithmetic,density
from probe_riesz_retained_factorial import unpaid_orders

def run(N,y):
 start=time.monotonic();u=10001/20000
 X=(math.floor(u**(-N)/(N+1))+2)**2;L=math.log(X)
 physical_lower=max(X,math.floor(math.exp(1.971*N)))
 physical_upper=min(X*X-1,math.floor(math.exp(2.029*N)))
 lo_p=math.isqrt(physical_lower)+1
 prime,mu=arithmetic(X)
 ps=np.flatnonzero(prime[lo_p:X])+lo_p
 low=np.maximum(physical_lower//ps,1)
 high=np.minimum(physical_upper//ps,ps-1)
 valid=low<high;ps=ps[valid];low=low[valid];high=high[valid]
 first=int(low.min());last=int(high.max()); ns=np.arange(first+1,last+1)
 assert np.all(ps<X)
 t=np.log(ps);v=np.log(ns);B=L-t
 cutoff=int(math.exp(float(B.max())))
 dens=np.zeros(len(ps))
 for d in range(1,cutoff+1):
  dens+=int(mu[d])*density(d)*np.maximum(0.,B-math.log(d))
 pref=np.exp((-1.5-1j*y)*v)
 row=np.zeros(len(ps),dtype=complex);p_row=np.zeros(len(ps),dtype=complex)
 all_rows=np.zeros((cutoff,len(ps)),dtype=complex)
 vpower=np.ones(len(v))
 allowed=set(range(N+2))-set(unpaid_orders(N))
 for k in range(N+2):
  if k in allowed:
   z=pref*vpower
   zsum=np.concatenate(([0j],np.cumsum(z)))
   pzsum=np.concatenate(([0j],np.cumsum(z*prime[ns])))
   b=math.comb(N+1,k)*t**(N+1-k)
   row+=b*(zsum[high-first]-zsum[low-first])
   p_row+=b*(pzsum[high-first]-pzsum[low-first])
   for d in range(1,cutoff+1):
    exact=np.concatenate(([0j],np.cumsum(z*((mu[ns]!=0)&(ns%d==0)))))
    all_rows[d-1]+=b*(exact[high-first]-exact[low-first])
  vpower*=v
 outer=u**(N+1)/(L*math.factorial(N))*np.exp((-1.5-1j*y)*t)
 density_terms=outer*dens*row
 prime_terms=-outer*B*p_row
 actual=np.zeros(len(ps),dtype=complex)
 for d in range(1,cutoff+1):
  actual+=int(mu[d])*np.maximum(0.,B-math.log(d))*all_rows[d-1]
 actual=outer*(actual-B*p_row)
 model=density_terms+prime_terms
 return dict(N=N,y=y,physicalUpper=X,L=L,nonemptyPhysicalAnnulus=True,
  markedPrimes=len(ps),cofactorRange=[first,last],shortCutoff=cutoff,
  sourceNormalizedSignedMain=float(model.sum().real),
  sourceNormalizedDensityPart=float(density_terms.sum().real),
  sourceNormalizedPrimePart=float(prime_terms.sum().real),
  sourceNormalizedActualOwnerSum=float(actual.sum().real),
  actualMinusModel=float((actual-model).sum().real),
  separateColumnsAbs=float(abs(model.real).sum()),
  separateDensityAndPrimeColumnsAbs=float((abs(density_terms.real)+abs(prime_terms.real)).sum()),
  nonownerAllocationIncluded=False,allOriginalMasksVerified=False,certified=False,
  seconds=time.monotonic()-start)
if __name__ == "__main__":
 import argparse
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--max-order',type=int,choices=[14,16,18],default=16)
 parser.add_argument('--height',type=float,default=54.)
 args=parser.parse_args()
 for N in [14,16,18]:
  if N<=args.max_order:
   print(json.dumps(run(N,args.height)),flush=True)

#!/usr/bin/env python3
"""Optional floating smooth-model probe of the literal cutoff-crossing geometry.

This is not a certificate or a discrete prime sum. It keeps the moving length,
original unpaid factorial orders, allocation and phase in a three-prime density
integral. Lean separately proves a lower bound using actual prime counts.
For N>8192 the floor correction is bounded below floating precision; its
logarithmic upper bound is recorded. No exhaustive verification runs in CI.
"""
import json
import math
import numpy as np
from scipy.special import logsumexp
from scipy.stats import binom
from probe_riesz_fixed_count_period import unpaid_orders
u=10001/20000
y=54.
w=math.pi/(64*y)
xs, ws=np.polynomial.legendre.leggauss(8)
z=(xs+1)*w/2
weights=np.multiply.outer(np.multiply.outer(ws,ws),ws)*(w/2)**3
rows=[]
for n in (256,640,1536,4096,8192,65536,262144,524288,1000000,2000000):
    logcut=-n*math.log(u)-math.log(n+1)
    if n<=8192:
        cut=pow(20000,n)//(pow(10001,n)*(n+1))
        L=2*math.log(cut+2)
        length_method='exact integer damped cutoff, floating log'
    else:
        L=2*logcut
        length_method='limiting log cutoff, floor error < 4*exp(-logcut)'
    v=(2*math.ceil((2*n*y-math.pi)/(2*math.pi))+1)*math.pi/y
    p=L/2+3*w+z[:,None,None]
    q=L/2-w+z[None,:,None]
    r=v-L+w+z[None,None,:]
    T=p+q+r
    # Same original unpaid-order set, without enumerating large arrays.
    # 4N>5(N+1-k) is the final literal guard.
    lo=max((n+1)//8+1,(n+5)//5+1)
    hi=min((7*(n+1)-1)//8,(15*n+64)//32,13*n//32)
    if n<=8192:
        orders=unpaid_orders(n)
        assert np.array_equal(orders,np.arange(lo,hi+1)),(n,lo,hi,orders[[0,-1]])
    allocated=sum(binom.cdf(hi,n+1,1-a/T)-binom.cdf(lo-1,n+1,1-a/T) for a in (p,q,r))
    phase=-np.cos(y*(T-v))
    crossing=L-p-q
    source_log=(n+1)*math.log(u)-T/2+(n+1)*np.log(T)-math.lgamma(n+1)
    logpositive=source_log-np.log(L)+np.log(-crossing)+np.log(-phase)+np.log1p(-allocated)-np.log(p)-np.log(q)-np.log(r)
    logmass=float(logsumexp(logpositive+np.log(weights)))
    rows.append(dict(N=n,moving_length=L,length_method=length_method,
       max_log_floor_error=math.log(4)-logcut,center_minus_2N=v-2*n,
       max_allocated=float(np.max(allocated)),min_unassigned=float(np.min(1-allocated)),
       min_cutoff_error=float(crossing.min()),max_cutoff_error=float(crossing.max()),
       min_phase=float(phase.min()),max_phase=float(phase.max()),
       log_source_normalized_crossing_mass=logmass,
       source_normalized_crossing_mass=math.exp(logmass) if abs(logmass)<700 else None,
       log_raw_crossing_mass=logmass-(n+1)*math.log(u),
       predicted_exponent=math.log(2*u),logmass_minus_growth=logmass-n*math.log(2*u)))
print(json.dumps({'scope':__doc__,'w':w,'rows':rows},indent=2))

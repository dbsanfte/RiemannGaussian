#!/usr/bin/env python3
"""Optional ordinary-prime-density diagnostic for the unsplit rough core.

This is NOT the literal prime sum, a full-core transport, a rigorous
quadrature enclosure or a bound on omitted prime counts. It evaluates the
original finite Riesz subset signs, moving length, exact binomial old
allocation and optional rectangle split in one shared continuum sample.
The ordinary density product dp/log(p) is an UNPROVED model replacement.
Only the explicit rough/physical/nondominant/window restrictions below are
modeled; no claim covers every inherited arithmetic support predicate.

Run outside CI using the existing numerical environment. The height-zero
column is a mass diagnostic, not a hypothetical off-critical zero height.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
from decimal import Decimal,localcontext
import numpy as np
from scipy.special import gammainc, gammaln
from scipy.stats import binom,qmc
U=10001/20000

def length(N):
    with localcontext() as c:
        c.prec=60
        return float(2*Decimal(20000**N//(10001**N*(N+1))+2).ln())

def moment(N,k,y,lo,hi):
    hi=np.maximum(lo,hi)
    if y==0:
        c=np.exp((N+1)*np.log(U)+(k+1)*np.log(2)+gammaln(k+1)-gammaln(N+1))
        return c*(gammainc(k+1,hi/2)-gammainc(k+1,lo/2))
    a=.5+1j*y
    def end(T):
        q=np.ones_like(T,dtype=complex);s=q.copy()
        for i in range(1,24):
            q*=(k-i+1)/(a*T);s+=q
        return -np.exp((N+1)*np.log(U)+k*np.log(T)-T/2-gammaln(N+1))*np.exp(-1j*y*T)*s/a
    return end(hi)-end(lo)

def row(N,k,power,seed,heights=(0,54)):
    v=qmc.Sobol(k-1,scramble=True,seed=seed).random_base2(power)
    cut=np.sort(v,axis=1)
    gap=np.diff(np.column_stack((np.zeros(len(v)),cut,np.ones(len(v)))),axis=1)
    r=2*np.log(N)/(2.03*N)
    free=1-k*r
    if free<=0:return {'N':N,'count':k,'seed':seed,'empty':True}
    xs=r+free*gap
    L=length(N)
    lo=np.maximum(1.95*N,2*np.log(N)/np.min(xs,axis=1))
    hi=np.minimum(2.03*N,L/np.max(xs,axis=1))
    valid=(hi>lo)&(np.max(xs,axis=1)<.65)
    hi=np.maximum(lo,hi)
    theta=np.sum(binom.cdf(13*N//32,N+1,1-xs)-binom.cdf((N+5)//5,N+1,1-xs),axis=1)
    assert np.min(theta)>=-1e-10 and np.max(theta)<=1+1e-10
    theta=np.clip(theta,0,1)
    j=np.arange((21*N+39)//40,23*N//40+1)
    owner=np.max(xs,axis=1)[:,None];least=np.min(xs,axis=1)[:,None]
    rect=np.sum(binom.pmf(j,N+1,owner)*(binom.cdf(N//25-1,N+1-j,least/(1-owner))-
          binom.cdf(max(0,(N+99)//100-1)-1,N+1-j,least/(1-owner))),axis=1)
    base=free**(k-1)/math.factorial(k-1)/math.factorial(k)/np.prod(xs,axis=1)*valid
    out={}
    for y in heights:
        obs=np.zeros(len(v),dtype=complex)
        for first in range(0,len(v),64):
            x=xs[first:first+64]
            sums=np.zeros((len(x),1));sign=np.ones(1)
            for col in x.T:
                sums=np.concatenate((sums,sums+col[:,None]),axis=1)
                sign=np.concatenate((sign,-sign))
            a=sums;sl=slice(first,first+len(x));ll=lo[sl,None];hh=hi[sl,None]
            end=np.minimum(hh,np.divide(L,a,out=np.full_like(a,np.inf),where=a>0))
            vals=-moment(N,N,y,ll,end)+(a/L)*moment(N,N+1,y,ll,end)
            obs[sl]=np.sum(vals*sign,axis=1)
        raw=base*obs
        vals=raw*(1-theta)
        enc=lambda z:[float(z.real),float(z.imag)]
        out[str(y)]={'raw':enc(np.mean(raw)),'assigned':enc(np.mean(raw*theta)),
         'joint':enc(np.mean(vals)),'packet':enc(np.mean(vals*rect)),
         'rest':enc(np.mean(vals*(1-rect))),'absolute_after_radial':float(np.mean(abs(vals))),
         'largest_share_bins':[enc(np.mean(vals*((np.max(xs,axis=1)>=a)&(np.max(xs,axis=1)<b))))
                for a,b in [(0,.5),(.5,.5625),(.5625,.65)]]}
    return dict(N=N,count=k,seed=seed,samples=len(v),valid=int(sum(valid)),heights=out)

def check_radial():
    """Floating regression against independent oscillatory quadrature."""
    from scipy.integrate import quad
    N=512
    for k in (N,N+1):
        lo,hi=1000.,1020.
        def f(T):
            return math.exp((N+1)*math.log(U)+k*math.log(T)-T/2-math.lgamma(N+1))
        for y in (0,54):
            if y:
                re=quad(f,lo,hi,weight='cos',wvar=y,epsabs=1e-11)[0]
                im=-quad(f,lo,hi,weight='sin',wvar=y,epsabs=1e-11)[0]
                expected=complex(re,im)
            else:
                expected=quad(f,lo,hi,epsabs=1e-11)[0]
            actual=moment(N,k,y,np.array([lo]),np.array([hi]))[0]
            assert abs(actual-expected)<1e-9*max(1,abs(expected)), (actual,expected)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--orders',type=int,nargs='+',default=[512,4096])
    ap.add_argument('--max-count',type=int,default=10)
    ap.add_argument('--power',type=int,default=13)
    ap.add_argument('--seeds',type=int,nargs='+',default=[117,241])
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    assert min(args.orders)>=320 and 3<=args.max_count<=16 and 1<=args.power<=20
    check_radial()
    rows=[]
    for N in args.orders:
        for k in range(3,args.max_count+1):
            for seed in args.seeds:
                result=row(N,k,args.power,seed)
                for h in result.get('heights',{}).values():
                    z=lambda name:complex(*h[name])
                    assert abs(z('raw')-z('assigned')-z('joint'))<1e-10
                    assert abs(z('packet')+z('rest')-z('joint'))<1e-10
                rows.append(result)
                print(f'N={N} count={k} seed={seed}',flush=True)
    payload=dict(scope='uncertified ordinary-prime-density rough-core model',
        orders=args.orders,max_count=args.max_count,sobol_power=args.power,seeds=args.seeds,
        radius=U,heights=[0,54],share_bins=[[0,.5],[.5,9/16],[9/16,13/20]],
        modeled_masks=['1.95N<T<=2.03N','all prime logs>2log(N)',
                      'all prime logs<L_N','largest log share<13/20'],
        limitations=['No discrete-prime transport','Higher counts unpaid',
            'No Sobol error enclosure','No roundoff enclosure',
            'No certification of every inherited arithmetic mask',
            '24 radial endpoint terms; no cofinal inference'],
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),rows=rows)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(payload,indent=2)+'\n')

if __name__=='__main__':
    main()

#!/usr/bin/env python3
"""Uncertified arithmetic test of adjoining p<=a<2p to the owner sector.

Squarefree composite a<2p has every prime factor <p, so p remains the
unique owner on both sides of the artificial a=p boundary. All integers
and marked primes are enumerated, the finite owner polynomial and product
phase are retained, and the possible unsaturated R_L(a) is kept exactly.
This is not the whole core: nonowner allocation, original count scheduling
and cofactor ratios >=2 are not certified or included. Never run in CI.
"""
import argparse,hashlib,math,json,time
from pathlib import Path
import numpy as np
from probe_riesz_cofactor_main import arithmetic,density
from probe_riesz_retained_factorial import unpaid_orders

def run(N,y):
    start=time.monotonic();u=10001/20000
    X=(20000**N//(10001**N*(N+1))+2)**2;L=math.log(X)
    nlo=max(X,math.floor(math.exp(1.95*N)))
    nhi=min(X*X-1,math.floor(math.exp(2.03*N)))
    pfirst=max(N*N+1,math.isqrt(nlo//2)+1)
    prime,mu=arithmetic(X)
    ps=np.flatnonzero(prime[pfirst:X])+pfirst
    low=np.maximum(nlo//ps,np.floor(ps.astype(float)**(7/13)).astype(np.int64))
    high=np.minimum(nhi//ps,2*ps-1)
    valid=low<high;ps=ps[valid];low=low[valid];high=high[valid]
    assert len(ps)
    t=np.log(ps);B=L-t
    first=int(low.min());last=int(high.max())
    if last>X:
        prime,mu=arithmetic(last)
    ns=np.arange(first+1,last+1);v=np.log(ns)
    cutoff=int(math.floor(math.exp(float(B.max()))))
    assert cutoff < first
    assert np.all(ps > N*N) and np.all(ps < X)
    assert np.all(high < 2*ps)
    ends=[(low,np.maximum(low,np.minimum(high,ps-1))),
          (np.minimum(high,np.maximum(low,ps-1)),high)]
    dens=np.zeros(len(ps))
    for d in range(1,cutoff+1):
        dens+=int(mu[d])*density(d)*np.maximum(0.,B-math.log(d))
    sf=(mu[ns]!=0);pr=prime[ns]
    # For a<2p<2X all proper divisors lie below X. Retain this exact
    # finite coefficient, including cases where the cofactor itself is >X.
    unsat=mu[ns].astype(float)*np.maximum(0.,v-L)*(~pr)
    pref=np.exp((-1.5-1j*y)*v)
    rows=np.zeros((2,len(ps)),complex);pr_rows=np.zeros_like(rows)
    unsat_rows=np.zeros_like(rows)
    exact_rows=np.zeros((2,cutoff,len(ps)),complex)
    vpower=np.ones(len(ns))
    def add_prefix(dest,z,b):
        zsum=np.concatenate(([0j],np.cumsum(z)))
        for i,(lo,hi) in enumerate(ends):
            dest[i]+=b*(zsum[hi-first]-zsum[lo-first])
    for k in range(N+2):
        if k not in unpaid_orders(N):
            z=pref*vpower
            b=math.comb(N+1,k)*t**(N+1-k)
            add_prefix(rows,z,b)
            add_prefix(pr_rows,z*pr,b)
            add_prefix(unsat_rows,z*unsat,b)
            for d in range(1,cutoff+1):
                add_prefix(exact_rows[:,d-1],z*(sf&(ns%d==0)),b)
        vpower*=v
    outer=u**(N+1)/(L*math.factorial(N))*np.exp((-1.5-1j*y)*t)
    actual=-B*pr_rows-unsat_rows
    for d in range(1,cutoff+1):
        actual+=int(mu[d])*np.maximum(0.,B-math.log(d))*exact_rows[:,d-1]
    actual*=outer
    den=outer*dens*rows;prpart=-outer*B*pr_rows
    upper=-outer*unsat_rows
    model=den+prpart+upper
    enc=lambda z:[float(z.real),float(z.imag)]
    data=[]
    for i,name in enumerate(['a<p','p<=a<2p']):
        data.append(dict(sector=name,actual=enc(actual[i].sum()),
            model=enc(model[i].sum()),density=enc(den[i].sum()),
            primeCorrection=enc(prpart[i].sum()),unsaturatedCorrection=enc(upper[i].sum()),
            actualMinusModel=enc((actual[i]-model[i]).sum()),
            realColumnAbsoluteSum=float(np.abs(actual[i].real).sum())))
    joined=actual.sum()
    return dict(N=N,y=y,X=X,L=L,cofactorRange=[first,last],
        markedPrimes=len(ps),divisorCutoff=cutoff,sectors=data,
        joined=enc(joined),joinedAbs=float(abs(joined)),
        joinedRealOverSeparatedRealAbs=float(abs(joined.real)/
            sum(abs(row.sum().real) for row in actual)),
        certified=False,allOriginalMasksVerified=False,
        nonownerAllocationIncluded=False,countsTailPaid=False,
        seconds=time.monotonic()-start)

def check_atoms():
    """Independent finite-divisor regressions, not interval certificates.

    Include cofactors above and below p and X. This checks the sign of the
    unsaturated correction against the original two-hinge response, then
    checks the factorial polynomial against the unexpanded owner weight.
    """
    X=53;L=math.log(X);N=16;y=54.;u=10001/20000
    prime,mu=arithmetic(2*X*X)
    def hinge(b,n):
        return sum(int(mu[d])*max(0.,b-math.log(d))
                   for d in range(1,n+1) if n%d==0)
    checked=0;regions=set()
    for p in (13,23,37,47):
        for a in range(2,2*p):
            if mu[a]==0 or prime[a]:
                continue
            assert math.gcd(p,a)==1
            assert all(q<p for q in range(2,a+1) if prime[q] and a%q==0)
            t=math.log(p);v=math.log(a);T=t+v
            response=hinge(L-t,a)-int(mu[a])*max(0.,v-L)
            assert abs(response+hinge(L,p*a))<1e-11
            allocated=sum(math.comb(N+1,k)*(v/T)**k*(t/T)**(N+1-k)
                          for k in unpaid_orders(N))
            poly=sum(math.comb(N+1,k)*t**(N+1-k)*v**k
                     for k in range(N+2) if k not in unpaid_orders(N))
            assert abs(poly/T**(N+1)-(1-allocated))<1e-12
            original=(-(1-allocated)*T/L*hinge(L,p*a)
                      *np.exp((-1.5-1j*y)*T)*T**N/math.factorial(N))
            expanded=(poly/L*response*np.exp((-1.5-1j*y)*T)
                      /math.factorial(N))
            scale=u**(N+1)
            assert abs(scale*(original-expanded))<1e-12*max(1,abs(scale*original))
            regions.add((a<p,a<=X));checked+=1
    assert regions=={(True,True),(False,True),(False,False)}
    return checked

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-order',type=int,choices=[14,16,18],default=16)
    ap.add_argument('--height',type=float,default=54.)
    ap.add_argument('--check-only',action='store_true')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    checked=check_atoms()
    if args.check_only:
        print(json.dumps(dict(floatingAtomChecks=checked,certified=False)))
    else:
        rows=[]
        for N in (14,16,18):
            if N<=args.max_order:
                row=run(N,args.height);rows.append(row)
                print(json.dumps(row),flush=True)
        if args.output:
            payload=dict(scope=__doc__.strip(),floatingAtomChecks=checked,
                         source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                         rows=rows)
            args.output.parent.mkdir(parents=True,exist_ok=True)
            args.output.write_text(json.dumps(payload,indent=2)+'\n')

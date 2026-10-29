#!/usr/bin/env python3
"""Exact cubic Gauss certificate over (Z/N)[z,t]/(Phi7(z),Phi3(t)).
Returns only a verified proper factor, a conditional two-residue palette, or
DECLINE. Does not implement HH or verify native scalar/order preparation.
Source: Schoof arXiv:0801.3840, Proposition 3.3(i).
"""
import argparse,json,math
from pathlib import Path

D=12

def monomial(z,t):
    z%=7;t%=3
    zs=[(z,1)] if z!=6 else [(i,-1) for i in range(6)]
    ts=[(t,1)] if t!=2 else [(i,-1) for i in range(2)]
    out=[0]*D
    for i,a in zs:
        for j,b in ts:out[2*i+j]+=a*b
    return out

TABLE=[[monomial(i//2+j//2,i%2+j%2) for j in range(D)] for i in range(D)]

class Ring:
    def __init__(self,N):self.N=N
    def scalar(self,x):return [x%self.N]+[0]*(D-1)
    def add(self,a,b):return [(x+y)%self.N for x,y in zip(a,b)]
    def scale(self,a,k):return [(x*k)%self.N for x in a]
    def mul(self,a,b):
        out=[0]*D
        for i,x in enumerate(a):
            if not x:continue
            for j,y in enumerate(b):
                if not y:continue
                xy=x*y
                for k,v in enumerate(TABLE[i][j]):
                    if v:out[k]+=xy*v
        return [v%self.N for v in out]
    def power(self,a,n):
        assert n>=0
        out=self.scalar(1)
        while n:
            if n&1:out=self.mul(out,a)
            a=self.mul(a,a);n//=2
        return out
    def transform(self,a,zpower=1,tpower=1):
        out=self.scalar(0)
        for i,x in enumerate(a):
            if x:out=self.add(out,self.scale(monomial(zpower*(i//2),tpower*(i%2)),x))
        return out

LOG7={pow(3,k,7):k%3 for k in range(6)}

def gauss(ring):
    out=ring.scalar(0)
    for x in range(1,7):out=ring.add(out,ring.scale(monomial(x,LOG7[x]),-1))
    return out

def cubic_root_ceil(x):
    lo,hi=0,1
    while hi**3<x:hi*=2
    while lo<hi:
        mid=(lo+hi)//2
        if mid**3<x:lo=mid+1
        else:hi=mid
    return lo

def check_K(K):
    if K%2:raise ValueError('K must be 2*3^e, e>=3')
    x=K//2;e=0
    while x>1 and x%3==0:x//=3;e+=1
    if x!=1 or e<3:raise ValueError('K must be 2*3^e, e>=3')
    return e

def acquire(N,K):
    if N<=1:raise ValueError('N must exceed 1')
    e=check_K(K)
    result=dict(N=N,K=K,ring_rank=D,
        basis='z^i*t^j indexed 2*i+j; 0<=i<6,0<=j<2',
        source='https://arxiv.org/pdf/0801.3840 Proposition 3.3(i)',
        not_checked=['native semiprime/order preparation','HH execution or complete runtime'])
    for p in (3,7):
        g=math.gcd(N,p)
        if 1<g<N:return dict(result,status='FACTOR',factor=g,cofactor=N//g)
        if g==N:return dict(result,status='DECLINE',reason='auxiliary prime divides entire input')
    R=Ring(N);tau=gauss(R);conj=R.transform(tau,-1,-1)
    assert R.mul(tau,conj)==R.scalar(7),'universal Gauss unit identity failed'
    inverse=R.scale(conj,pow(7,-1,N))
    gamma=R.mul(R.transform(tau,tpower=N),R.power(inverse,N))
    checks=[];passed=None
    for k in (1,2):
        difference=R.add(gamma,R.scale(monomial(0,k),-1))
        g=N
        for coefficient in difference:g=math.gcd(g,coefficient)
        checks.append(dict(primitive_exponent=k,coefficient_gcd=g))
        if 1<g<N:return dict(result,status='FACTOR',factor=g,cofactor=N//g,
                              gamma=gamma,checks=checks)
        if g==N:passed=k
    result.update(gamma=gamma,checks=checks)
    if passed is None:return dict(result,status='DECLINE',reason='no certified global primitive cubic congruence')
    x=N*N-1;t=0
    while x%3==0:t+=1;x//=3
    n=3**min(t,e)
    threshold=cubic_root_ceil(K)
    eligible=n>=threshold and N<=K**6
    return dict(result,status='PALETTE',primitive_exponent=passed,
                modulus=n,residues=sorted({1%n,(-1)%n}),v3_N_squared_minus_1=t,
                public_HH_budget_eligible=eligible,
                budget_threshold=threshold,
                meaning='certificate proves every prime divisor is +/-1 mod modulus; HH needs supplied native preparation')

def self_test():
    tau_integer=[-sum(monomial(x,LOG7[x])[i] for x in range(1,7)) for i in range(D)]
    conjugate_integer=[0]*D
    for i,x in enumerate(tau_integer):
        for k,v in enumerate(monomial(-(i//2),-(i%2))):conjugate_integer[k]+=x*v
    product_integer=[0]*D
    for i,x in enumerate(tau_integer):
        for j,y in enumerate(conjugate_integer):
            for k,v in enumerate(TABLE[i][j]):product_integer[k]+=x*y*v
    assert product_integer==[7]+[0]*(D-1)
    gauss_checks=frobenius_checks=0
    for p in (5,11,13):
        R=Ring(p);tau=gauss(R)
        assert R.mul(tau,R.transform(tau,-1,-1))==R.scalar(7)
        gauss_checks+=1
        # tau^p=chi(p)^(-p)*sigma_p(tau), sigma_p fixes additive z.
        rhs=R.mul(monomial(0,(-p*LOG7[p%7])%3),R.transform(tau,tpower=p))
        assert R.power(tau,p)==rhs
        frobenius_checks+=1
    prime_palette=acquire(5,54)
    assert prime_palette['status']=='PALETTE' and prime_palette['residues']==[1,2]
    factor=acquire(15,54)
    assert factor['status']=='FACTOR' and 15%factor['factor']==0
    decline=acquire(55,54)
    assert decline['status']=='DECLINE',decline
    return dict(status='PASS',exact_integer_Gauss_identity=True,
                prime_palette_control=5,gauss_identity_checks=gauss_checks,
                prime_Frobenius_checks=frobenius_checks,
                composite_factor_control=15,composite_decline_control=55,
                scope='structural controls only; no semiprime coverage/success campaign')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--N',type=int)
    group=ap.add_mutually_exclusive_group()
    group.add_argument('--K',type=int);group.add_argument('--e',type=int)
    ap.add_argument('--self-test',action='store_true')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    if args.self_test:out=self_test()
    else:
        if args.N is None:ap.error('--N is required unless --self-test')
        if args.K is None and args.e is None:ap.error('supply --K or --e')
        K=args.K if args.K is not None else 2*3**args.e
        try:out=acquire(args.N,K)
        except ValueError as exc:ap.error(str(exc))
    encoded=json.dumps(out,indent=2)+'\n'
    if args.output:args.output.write_text(encoded)
    print(encoded,end='')
if __name__=='__main__':main()

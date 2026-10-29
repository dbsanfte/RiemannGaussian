#!/usr/bin/env python3
"""Exact rational controls for D.4/D.5; no contraction/factoring implementation."""
from fractions import Fraction as F
from math import comb
import json
from pathlib import Path

def v2(x):
    x=F(x)
    if not x:return 10**9
    def z(n):
        n=abs(n);return (n&-n).bit_length()-1
    return z(x.numerator)-z(x.denominator)
def add(a,b):
    out=[F(0)]*max(len(a),len(b))
    for i,x in enumerate(a):out[i]+=x
    for i,x in enumerate(b):out[i]+=x
    return out

def mul(a,b,n=None):
    if n is None:n=len(a)+len(b)-1
    out=[F(0)]*min(n,len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j<len(out):out[i+j]+=x*y
    return out

def shift(a,t,alpha,n=None):
    if n is None:n=len(a)
    out=[F(0)]*n
    for x in reversed(a):
        out=mul(out,[F(t),F(alpha)],n)
        out[0]+=x
    return out

def residue(x,p):
    x=F(x);assert v2(x)>=0
    return x.numerator*pow(x.denominator,-1,1<<p)%(1<<p)

def wpoly(a,x,y):
    L=1<<a;S=range(-L,L);d=y-x
    den=1
    for q in S:
        if q:den*=-q
    out=[F(1)]
    for q in S:
        if q!=d:out=mul(out,[F(-q),F(1)])
    return [z/den for z in out]

def main():
    tally=dict(cauchy_polynomials=0,cauchy_local_coefficients=0,
               valuation_counts=0,precision_weights=0,hermite_reconstructions=0)
    cases=[]
    for a in (1,2,3):
        L=1<<a;alpha=2*L;S=list(range(-L,L))
        for x in range(L):
            for y in range(L):
                W=wpoly(a,x,y);assert W[0]==int(x==y)
                tally['cauchy_polynomials']+=1
                for t in S:
                    local=shift(W,t,alpha)
                    assert all(v2(z)>=0 for z in local)
                    tally['cauchy_local_coefficients']+=len(local)
        for u in range(1,a+1):
            M=max(u,3);h=(3*M+u-1)//u;p=5
            qm=lambda i:h*max(0,u-i)
            active=[t for t in S if t and qm(v2(t))]
            N=sum(qm(v2(t)) for t in active)
            assert N>M*(2*L-1)
            # An actual Cauchy-product linear combination; no arbitrary integrality assumed.
            P=[F(1)]
            for k in range(M):P=mul(P,wpoly(a,k%L,(2*k+1)%L))
            Q=[F(1)]
            for k in range(M):Q=mul(Q,wpoly(a,(k+1)%L,(k+1)%L))
            poly=add([F(1)],add([2*z for z in P],[3*z for z in Q]))
            assert len(poly)-1<=M*(2*L-1) and v2(poly[0])>=0
            reconstructed=F(0);max_loss=0
            for t in active:
                i=v2(t);D=L//(1<<i);qt=qm(i)
                E0=F(1)
                for q in active:
                    if q!=t:E0*=F(-q,t-q)**qm(v2(q))
                expected=D*sum((F(j,1<<j)*(qm(i+j)-qm(i))
                                for j in range(1,a-i+1)),F(0))
                assert v2(E0)==expected and v2(E0)>=-6*D*h
                tally['valuation_counts']+=1
                invE=[F(1)]
                for q in active:
                    if q==t:continue
                    c=F(alpha,t-q);assert v2(c)>=1
                    k=qm(v2(q))
                    fac=[(-1)**j*comb(k+j-1,j)*c**j for j in range(qt)]
                    invE=mul(invE,fac,qt)
                local=shift(poly,t,alpha,qt)
                assert all(v2(z)>=0 for z in local+invE)
                pt=p+8*h*D+8*M*(a+1)
                # Legal residues plus independent precision-sized perturbations.
                approximate=[F(residue(z,pt)+(1<<pt)*((-1)**j))
                             for j,z in enumerate(local)]
                quotient=mul(approximate,invE,qt)
                for j in range(qt):
                    weight=E0*F(-t,alpha)**j
                    assert pt+v2(weight)>=p
                    tally['precision_weights']+=1
                    max_loss=max(max_loss,-v2(weight))
                    reconstructed+=weight*quotient[j]
            assert v2(reconstructed-poly[0])>=p
            tally['hermite_reconstructions']+=1
            cases.append(dict(a=a,u=u,M=M,total_multiplicity=N,
                              degree=len(poly)-1,max_actual_weight_loss=max_loss,
                              reconstruction_error_v2=v2(reconstructed-poly[0])))
    out=dict(status='PASS',counts=tally,cases=cases,
             scope='exact rational finite controls; universal proof reconstructed separately; no D1 implementation')
    Path(__file__).with_name('precision-checks.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))
if __name__=='__main__':main()

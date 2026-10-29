#!/usr/bin/env python3
"""Structural native weighted-Gauss support experiment. No group arithmetic/factorer.
Exact 2D Gauss reduction follows the nearest-integer convention of repository
scripts/probe_semiprime_sparse_residue_gauss.py; uses the weighted rank-2
lattice (K,0),(s,1) in the actual pure-weighted-common-tag construction.
"""
import math,json,time,argparse,csv
from pathlib import Path

def prime(n):
    assert n<2**64, "deterministic Miller-Rabin fixture bound"
    if n<2:return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%p==0:return n==p
    d=n-1;s=0
    while d%2==0:s+=1;d//=2
    for a in (2,325,9375,28178,450775,9780504,1795265022):
        if a%n==0:continue
        x=pow(a,d,n)
        if x in (1,n-1):continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1:break
        else:return False
    return True

def nextprime(n):
    n=max(3,n|1)
    while not prime(n):n+=2
    return n

def nearest(a,b):
    q,r=divmod(a,b);return q+(2*r>b)

def gauss(N,K,s,B):
    # Coordinates are (a,b), with physical embedding (a B^2,b N).
    u,v=(K,0),(s,1)
    def dot(x,y):return x[0]*y[0]*B**4+x[1]*y[1]*N*N
    while True:
        if dot(v,v)<dot(u,u):u,v=v,u
        norm=dot(u,u);ip=dot(u,v)
        if 2*abs(ip)<=norm:break
        z=nearest(ip,norm);v=(v[0]-z*u[0],v[1]-z*u[1])
    a,b=u
    if a<0 or (a==0 and b<0):a,b=-a,-b
    assert (a-s*b)%K==0 and (a or b)
    assert 3*dot((a,b),(a,b))**2<=4*(K*B*B*N)**2
    return a,b

def union_size(groups):
    size=count=0
    for intervals in groups.values():
        intervals.sort();a,b=intervals[0]
        for x,y in intervals[1:]:
            if x<=b+1:b=max(b,y)
            else:size+=b-a+1;count+=1;a,b=x,y
        size+=b-a+1;count+=1
    return size,count

def inversion_fold(groups,H):
    folded={}
    for phase,intervals in groups.items():
        target=min(phase,H-phase) if phase else 0
        out=folded.setdefault(target,[])
        for a,b in intervals:
            if phase==0:
                assert not a<=0<=b
                out.append((-b,-a) if b<0 else (a,b))
            elif phase==H//2:
                if a<0:out.append((-min(b,-1)-1,-a-1))
                if b>=0:out.append((max(a,0),b))
            elif phase>H//2:out.append((-b-1,-a-1))
            else:out.append((a,b))
    return union_size(folded)

def measure(e,shape):
    K=2*3**e;H=K*K
    P=nextprime(K**3*shape//100);Q=nextprime(K**3*70//shape)
    if P>Q:P,Q=Q,P
    N=P*Q
    assert Q!=P and N<=K**6 and P>16*H
    sq=math.isqrt(N);D=math.isqrt(K*N)
    if D*D<K*N:D+=1
    M=(4*D+H-1)//H+2;h=2*M+1
    # Public dyadic bins spanning the promised factor interval.
    lo=(16*H).bit_length()-1;hi=sq.bit_length()
    bins=[1<<x for x in range(lo,hi+1)]
    # Include the complementary-factor dyadic bin as allowed by symmetric setup.
    bins=sorted(set(bins+[1<<(Q.bit_length()-1)]))
    result=[]
    for B in bins:
        groups={};J=0;removed=0;axes=0;original=K//3
        for j in range(1,K,2):
            if j%3==0:continue
            inv=pow(j,-1,K);s=N*inv*inv%K
            a,b=gauss(N,K,s,B)
            assert abs(a)<=K and abs(b)<=K
            dj=(a*j*j-b*N)//K
            assert (a*j*j-b*N)%K==0
            t=dj*inv%K;ell=(-2*a*j+K*t)%H
            if ell>=H//2:ell-=H
            assert (a*j*j+ell*j+b*N)%H==0
            assert (2*a*j+ell)%K==0
            r=ell-a-b*N
            for R in (P,Q):
                if B<=R<2*B and j==R%K:
                    numerator=a*R+b*(N//R)+ell
                    assert numerator%H==0 and abs(numerator//H)<=M
                    assert r-H*(numerator//H)!=0
            if r%H==0 and -M<=r//H<=M:
                removed+=1;continue
            axes+=not(a and b);J+=1
            c,res=divmod(r,H)
            groups.setdefault(res,[]).append((c-M,c+M))
        S,C=union_size(groups)
        S_inv,C_inv=inversion_fold(groups,H)
        assert S<=2*S_inv and S_inv<=S
        result.append(dict(e=e,K=K,N=N,P=P,Q=Q,shape=shape,B=B,
            correct_P_bin=B<=P<2*B,correct_Q_bin=B<=Q<2*B,
            original_J=original,J=J,removed_rows=removed,axis_rows=axes,h=h,
            C_union=C,S_inv=S_inv,C_inv=C_inv,S_inv_over_S_union=S_inv/S if S else 1,
            sqrtS_inv_over_K=math.sqrt(S_inv)/K,residue_classes=len(groups),S_union=S,Jh=J*h,
            S_over_Jh=S/(J*h) if J else 0,sqrtS_over_K=math.sqrt(S)/K))
    return result

def main():
    p=argparse.ArgumentParser();p.add_argument('--max-e',type=int,default=9)
    p.add_argument('--output',default='support-union.json');a=p.parse_args()
    start=time.monotonic();rows=[]
    for e in range(3,a.max_e+1):
        for shape in (55,75):rows.extend(measure(e,shape))
    Path(a.output).write_text(json.dumps(dict(kind='exact structural support only',
        elapsed_seconds=time.monotonic()-start,rows=rows),indent=2)+'\n')
    with Path(a.output).with_suffix('.csv').open('w',newline='') as stream:
        writer=csv.DictWriter(stream,fieldnames=list(rows[0]))
        writer.writeheader();writer.writerows(rows)
    print(json.dumps(dict(rows=len(rows),elapsed_seconds=time.monotonic()-start,
        by_e=[dict(e=e,min_ratio=min(r['sqrtS_over_K'] for r in rows if r['e']==e),
        max_ratio=max(r['sqrtS_over_K'] for r in rows if r['e']==e))
        for e in range(3,a.max_e+1)])))
if __name__=='__main__':main()

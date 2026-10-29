#!/usr/bin/env python3
"""Tiny exact algebra diagnostics, not a fast multiplication implementation.
No native coverage, factoring success-rate or complexity simulation.
"""
import argparse, itertools, json, math
from pathlib import Path

def run(n,q,h,roots):
    checks=[]
    def iv(x): return pow(x%n,-1,n)
    def add(a,b):
        c=[0]*max(len(a),len(b))
        for i,x in enumerate(a): c[i]=(c[i]+x)%n
        for i,x in enumerate(b): c[i]=(c[i]+x)%n
        return c
    def sc(a,x): return [v*x%n for v in a]
    def mul(a,b):
        c=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b): c[i+j]=(c[i+j]+x*y)%n
        return c
    def product(ps):
        c=[1]
        for p in ps:c=mul(c,p)
        return c
    def ev(p,x):
        c=0
        for a in reversed(p):c=(c*x+a)%n
        return c
    def detpoly(a):
        out=[0]
        for perm in itertools.permutations(range(len(a))):
            sign=(-1)**sum(perm[i]>perm[j] for i in range(len(a)) for j in range(i+1,len(a)))
            out=add(out,sc(product(a[i][perm[i]] for i in range(len(a))),sign))
        return out
    def eq(name,a,b):
        assert a==b,(name,a,b)
        checks.append(name)
    j=len(roots); d=product([[-x%n,1] for x in roots]); b=pow(q,h-1,n)
    dp=[i*d[i]%n for i in range(1,len(d))]
    gates=[q,q-1,ev(d,b)]
    gates += [x for x in roots]+[ev(dp,x) for x in roots]
    gates += [x-b for x in roots]+[x-iv(q) for x in roots]
    gates += [1-pow(q,r,n) for r in range(1,h+j+1)]
    assert all(math.gcd(x,n)==1 for x in gates)
    # Polynomial Lagrange numerator: no inverse of q*x-y is required.
    m=[[math.prod((q*x-z)%n for k,z in enumerate(roots) if k!=col)*iv(ev(dp,y))%n for col,y in enumerate(roots)] for x in roots]
    r=[pow(q,h,n)*(x-iv(q))*iv(x-b)%n for x in roots]
    a=[[r[i]*m[i][k]%n for k in range(j)] for i in range(j)]
    dense=detpoly([[[(1 if i==k else 0),-a[i][k]%n] for k in range(j)] for i in range(j)])
    principal=[0]*(j+1);principal[0]=1
    for size in range(1,j+1):
        for idx in itertools.combinations(range(j),size):
            minor=detpoly([[[a[i][k]] for k in idx] for i in idx])[0]
            principal[size]=(principal[size]+(-1)**size*minor)%n
    aa=[[1,-pow(q,k,n)%n] for k in range(j)]
    bb=[[1,-pow(q,h+k,n)%n] for k in range(j)]
    w=[d[s]*pow(b,s,n)%n for s in range(j+1)]
    def balanced(l,r):
        if r-l==1:return aa[l],bb[l],sc(bb[l],w[l])
        mid=(l+r)//2
        al,bl,ql=balanced(l,mid); ar,br,qr=balanced(mid,r)
        return mul(al,ar),mul(bl,br),add(mul(ql,br),mul(al,qr))
    ap,bp,total=balanced(0,j)
    chi=sc(add(total,sc(ap,w[j])),iv(ev(d,b)))
    eq('balanced versus dense determinant',chi,dense)
    eq('balanced versus independent principal minors',chi,principal)
    eq('constant coefficient',chi[0],1)
    eq('chi(1)',ev(chi,1),d[0]*math.prod((1-pow(q,h+k,n))%n for k in range(j))*iv(ev(d,b))%n)
    assert math.gcd(ev(chi,1),n)==1
    # Direct subset higher responses, independent of the Cauchy determinant formula.
    for size in range(j+1):
        out=0
        for idx in itertools.combinations(range(j),size):
            inside=set(idx);v=pow(q,size*(size-1)//2,n)
            for i in idx:
                v=v*r[i]%n
                for k in range(j):
                    if k not in inside:v=v*(q*roots[i]-roots[k])*iv(roots[i]-roots[k])%n
            out=(out+v)%n
        eq('subset response '+str(size),chi[size],(-1)**size*out%n)
    return {'modulus':n,'q':q,'h':h,'roots':roots,'interior_hit_indices':[i for i in range(1,h-1) if pow(q,i,n) in roots],'all_required_gates_unit':True,'zero_adjacency_pairs':[[i,k] for i,x in enumerate(roots) for k,y in enumerate(roots) if (q*x-y)%n==0],'checks':checks,'chi':chi}

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=Path(__file__).with_name('higher-response-checks.json'))
args=parser.parse_args()
fixtures=[run(1009,11,9,[pow(11,3,1009),2,7]),run(101*103,2,8,[8,3,7]),run(1009,11,8,[pow(11,4,1009),2,7,19]),run(1009,11,8,[2,22,7])]
assert fixtures[-1]['zero_adjacency_pairs'], 'division-free fixture must contain an exact q-adjacency'
result={'status':'PASS','implementation':'standard-library naive polynomial diagnostic; not a soft-J implementation','checks':sum(len(x['checks']) for x in fixtures),'fixtures':fixtures}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'checks':result['checks'],'fixtures':len(fixtures)}))

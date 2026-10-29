#!/usr/bin/env python3
"""Deterministic exact finite-field checks; standard library only.
No native coverage or factoring claim is tested.
"""
import argparse
import json
from pathlib import Path
P, Q = 1009, 11
checks = []

def inv(x):
    assert x % P
    return pow(x % P, -1, P)
def add(a,b):
    c=[0]*max(len(a),len(b))
    for i,x in enumerate(a): c[i]=(c[i]+x)%P
    for i,x in enumerate(b): c[i]=(c[i]+x)%P
    return c

def scale(a,c): return [x*c%P for x in a]
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]=(c[i+j]+x*y)%P
    return c

def ev(a,x):
    r=0
    for c in reversed(a): r=(r*x+c)%P
    return r

def poly(roots):
    a=[1]
    for r in roots: a=mul(a,[-r%P,1])
    return a

def prod(xs):
    r=1
    for x in xs: r=r*x%P
    return r

def det(a):
    a=[r[:] for r in a]; d=1
    for i in range(len(a)):
        k=next((k for k in range(i,len(a)) if a[k][i]%P),None)
        if k is None: return 0
        if k!=i: a[i],a[k]=a[k],a[i]; d=-d
        pivot=a[i][i]%P; d=d*pivot%P
        for k in range(i+1,len(a)):
            t=a[k][i]*inv(pivot)%P
            for j in range(i,len(a)): a[k][j]=(a[k][j]-t*a[i][j])%P
    return d%P

def rem(a,d):
    a=a[:]
    while len(a)>=len(d):
        c=a[-1]%P; off=len(a)-len(d)
        for j,x in enumerate(d): a[off+j]=(a[off+j]-c*x)%P
        a.pop()
    return a

def ell(a,d):
    r=rem(a,d); j=len(d)-2
    return r[j] if j<len(r) else 0

def assert_eq(name,a,b):
    assert a==b,(name,a,b)
    checks.append(name)

def shift(a,s): return [x*pow(Q,s*i,P)%P for i,x in enumerate(a)]
def ore_mul(a,b):
    c={}
    for i,x in a.items():
        for j,y in b.items(): c[i+j]=add(c.get(i+j,[]),mul(x,shift(y,i)))
    return c

def ore_pow(a,n):
    r={0:[1]}
    for _ in range(n): r=ore_mul(r,a)
    return r

def op_poly(d,l):
    r={}
    for k,c in enumerate(d):
        for s,a in ore_pow(l,k).items(): r[s]=add(r.get(s,[]),scale(a,c))
    return r

h=9
nodes=[pow(Q,i,P) for i in range(h)]
assert len(set(nodes))==h
# Regular delta checks use direct divided differences versus convolution.
for roots in ([3,7],[2,2,17],[4,8,19,23]):
    d=poly(roots)
    for delta in (0,1,13):
        dd=d[:]; dd[0]=(dd[0]+delta)%P
        if any(ev(dd,x)==0 for x in nodes): continue
        fac=[1]
        for i in range(1,h): fac.append(fac[-1]*(1-pow(Q,i,P))%P)
        a=[pow(-1,i,P)*inv(ev(dd,nodes[i]))*inv(fac[i])%P for i in range(h)]
        b=[pow(Q,i*(i-1)//2,P)*inv(fac[i])%P for i in range(h)]
        c=mul(a,b)[:h]
        for m in range(h):
            f=sum(inv(ev(dd,nodes[i]))*inv(prod(nodes[i]-nodes[l] for l in range(m+1) if l!=i)) for i in range(m+1))%P
            assert_eq(f'Newton J{len(roots)} delta{delta} m{m}',c[m],pow(Q,m*(m-1)//2,P)*f%P)
        # Independently apply L=(1+z)S repeatedly to C.
        out=[0]*h; v=c[:]
        for coefficient in dd:
            out=add(out,scale(v,coefficient))[:h]
            v=mul(shift(v,1),[1,1])[:h]
        assert_eq(f'operator J{len(roots)} delta{delta}',out,[1]+[0]*(h-1))

# Residues are computed termwise from poles, without taking a numerical delta limit.
for name,roots in [('first',[nodes[0],3,3]),('last',[nodes[-1],3,3]),('middle',[nodes[4],3,3]),('multiple',[nodes[1],nodes[5],3,3])]:
    d=poly(roots)
    residues=[]
    for m in range(h):
        residues.append(sum(inv(prod(nodes[i]-nodes[l] for l in range(m+1) if l!=i)) for i in range(m+1) if ev(d,nodes[i])==0)%P)
    fac=[1]
    for i in range(1,h): fac.append(fac[-1]*(1-pow(Q,i,P))%P)
    pole_a=[pow(-1,i,P)*inv(fac[i])%P if ev(d,nodes[i])==0 else 0 for i in range(h)]
    euler_b=[pow(Q,i*(i-1)//2,P)*inv(fac[i])%P for i in range(h)]
    pole_c=mul(pole_a,euler_b)[:h]
    for m in range(h):
        assert_eq(f'residue convolution {name} m{m}',pole_c[m],pow(Q,m*(m-1)//2,P)*residues[m]%P)
    if name!='multiple':
        target=next(x for x in nodes if ev(d,x)==0)
        locator=(nodes[-1]+residues[-2]*inv(residues[-1]))%P
        assert_eq(f'locator {name}',locator,target)
        cn=pow(Q,(h-1)*(h-2)//2,P)*residues[-1]%P
        cp=pow(Q,(h-2)*(h-3)//2,P)*residues[-2]%P
        assert_eq(f'coefficient locator {name}',(nodes[-1]+pow(Q,h-2,P)*cp*inv(cn))%P,target)

# Ore products catch both highest-shift linear coefficients, including lower D terms.
for j in range(1,6):
    d=poly(list(range(2,j+2))); d[0]=(d[0]+13)%P
    lp={1:[1,1]}; lm={1:[1,-1%P]}
    first=ore_mul(op_poly(scale([x*((-1)**i) for i,x in enumerate(d)],(-1)**j),lp),op_poly(d,lp))
    second=ore_mul(op_poly(d,lm),op_poly(d,lp))
    assert_eq(f'Graeffe variable J{j}',first[2*j][1],sum(pow(Q,t,P) for t in range(2*j))%P)
    assert_eq(f'Graeffe reflection J{j}',second[2*j][1],(-(1-pow(Q,j,P))**2*inv(1-Q))%P)

# Cleared E sum is independent of Hankel construction and is valid even at hits.
for roots in ([3,7],[3,3,17],[nodes[0],3,7],[nodes[4],3,3],[nodes[1],nodes[5],3]):
    d=poly(roots); j=len(roots)
    for n in range(7):
        vals=[ev(d,x) for x in nodes[:n+1]]
        e=sum(prod(vals[l] for l in range(n+1) if l!=i)*inv(prod(nodes[i]-nodes[l] for l in range(n+1) if l!=i)) for i in range(n+1))%P
        # Polynomial built separately, with (a_i-X) orientation.
        pn=[1]
        for a in nodes[:n+1]: pn=mul(pn,[a,-1%P])
        moments=[ell([0]*k+pn,d) for k in range(2*j-1)]
        hjm=det([[moments[r+s] for s in range(j-1)] for r in range(j-1)])
        hj=det([[moments[r+s] for s in range(j)] for r in range(j)])
        assert_eq(f'Hankel minor roots{roots} n{n}',hjm,((-1)**(j*(j-1)//2+n)*e)%P)
        assert_eq(f'Hankel full roots{roots} n{n}',hj,((-1)**(j*(j-1)//2)*prod(vals))%P)
        if all(vals):
            f=sum(inv(vals[i])*inv(prod(nodes[i]-nodes[l] for l in range(n+1) if l!=i)) for i in range(n+1))%P
            assert_eq(f'cleared E roots{roots} n{n}',e,prod(vals)*f%P)

result={'status':'PASS','field_prime':P,'q':Q,'checks':len(checks),'scope':'Tiny exact algebra fixtures, not native coverage or complexity tests','check_names':checks}
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=Path(__file__).with_name('scalar-reduction-checks.json'),help='JSON results path (default: beside this script)')
args=parser.parse_args()
out=args.output
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='check_names'}))

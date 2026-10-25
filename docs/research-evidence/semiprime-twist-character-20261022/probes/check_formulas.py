from itertools import product
from math import gcd, isqrt

def prime(p): return p>1 and all(p%d for d in range(2,isqrt(p)+1))
def gm(x,y): return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def norm(x): return x[0]*x[0]+x[1]*x[1]
def rem(x,y):
    d=norm(y); z=gm(x,(y[0],-y[1]))
    q=tuple((2*t+d)//(2*d) for t in z)
    v=gm(q,y)
    return (x[0]-v[0],x[1]-v[1])
def primary(x): return x[1]%2==0 and (x[0]+x[1])%4==1
units=[(1,0),(0,1),(-1,0),(0,-1)]
def quartic(a,b):
    assert norm(b)%2
    b=next(gm(b,u) for u in units if primary(gm(b,u)))
    out=0
    while True:
        if norm(b)==1: return out%4
        a=rem(a,b)
        if a==(0,0): return None
        c,d=b; m=0
        while (a[0]+a[1])%2==0:
            a=((a[0]+a[1])//2,(a[1]-a[0])//2); m+=1
        n=next(n for n in range(4) if primary(gm(a,units[-n%4])))
        a=gm(a,units[-n%4]); e,f=a
        out+=m*((c-d-d*d-1)//4)-n*((c-1)//2)+2*((e-1)*(c-1)//4)
        a,b=b,a

def fp_mul(x,y,p,delta):
    return ((x[0]*y[0]+delta*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
def fp_pow(x,n,p,delta):
    out=(1,0)
    while n:
        if n&1:out=fp_mul(out,x,p,delta)
        x=fp_mul(x,x,p,delta);n//=2
    return out

def quartic_local(a,b,p):
    if p%4==1:
        t=next(t for t in range(p) if t*t%p==p-1)
        out=0
        for rt in (t,-t%p):
            y=pow((a+b*rt)%p,(p-1)//4,p)
            out+=next(h for h in range(4) if pow(rt,h,p)==y)
        return out%4
    y=fp_pow((a%p,b%p),(p*p-1)//4,p,-1)
    return next(h for h,u in enumerate(units) if (u[0]%p,u[1]%p)==y)

def torus_phase(a,b,p):
    n=(a*a+b*b)%p
    z=((a*a-b*b)*pow(n,-1,p)%p,2*a*b*pow(n,-1,p)%p)
    e=1 if p%4==1 else -1
    if e<0:z=(z[0],-z[1]%p)
    y=fp_pow(z,(p-e)//4,p,-1)
    return next(h for h,u in enumerate(units) if (u[0]%p,u[1]%p)==y)

def octic_local(coeff,p):
    f=1 if p%8==1 else 2
    delta=next(d for d in range(2,p) if pow(d,(p-1)//2,p)==p-1)
    candidates=((x,0) for x in range(1,p)) if f==1 else product(range(p),repeat=2)
    z=next(x for x in candidates if fp_pow(x,4,p,delta)==(p-1,0))
    reps={1:(1,3,5,7),3:(1,5),5:(1,3),7:(1,3)}[p%8]
    total=0
    for j in reps:
        val=(0,0)
        for k,c in enumerate(coeff):
            t=fp_pow(z,j*k,p,delta)
            val=((val[0]+c*t[0])%p,(val[1]+c*t[1])%p)
        assert val!=(0,0)
        y=fp_pow(val,(p**f-1)//8,p,delta)
        total+=next(h for h in range(8) if fp_pow(z,j*h,p,delta)==y)
    return total%8

def cm(x,y):
    t=[0]*7
    for i,a in enumerate(x):
        for j,b in enumerate(y):t[i+j]+=a*b
    for j in range(6,3,-1):t[j-4]-=t[j]
    return tuple(t[:4])
def conj8(x,j):
    y=[0]*4
    for k,a in enumerate(x):
        q,r=divmod(k*j,4);y[r]+=a*(-1)**q
    return tuple(y)
def norm8(x):
    n=(1,0,0,0)
    for j in (1,3,5,7):n=cm(n,conj8(x,j))
    assert n[1:]==(0,0,0)
    return n[0]

ps=[p for p in range(3,100) if prime(p)]
count=0
for p in ps:
    for a,b in product(range(-3,4),repeat=2):
        if (a*a+b*b)%p==0:continue
        s=quartic_local(a,b,p)
        assert s==quartic((a,b),(p,0))==torus_phase(a,b,p),(p,a,b,s)
        leg=pow((a*a+b*b)%p,(p-1)//2,p)
        assert (-1 if s%2 else 1)==(1 if leg==1 else -1)
        assert octic_local((a,0,b,0),p)==(-2*s)%8
        count+=1
full=0
for p in ps:
    for coeff in ((1,1,1,0),(2,1,0,1),(1,2,-1,1),(3,-1,2,1)):
        nn=norm8(coeff)
        if nn%p==0:continue
        h=octic_local(coeff,p)
        assert pow(nn%p,(p-1)//2,p)==(1 if h%2==0 else p-1)
        full+=1
for p,q in ((3,7),(3,11),(5,13),(5,7),(7,17),(13,17)):
    N=p*q
    for a,b in product(range(-5,6),repeat=2):
        if gcd(a*a+b*b,N)>1:continue
        assert quartic((a,b),(N,0))==(quartic_local(a,b,p)+quartic_local(a,b,q))%4
couplings=0
for p in ps:
    for a in range(1,p):
        if (a*a+1)%p==0:continue
        h=quartic_local(a,1,p)
        jj=0 if pow(2,(p-1)//2,p)==1 else 2
        assert quartic_local(-a,1,p)==-h%4
        assert quartic_local(pow(a,-1,p),1,p)==(jj-h)%4
        assert quartic_local(-pow(a,-1,p),1,p)==(jj+h)%4
        couplings+=1
    for coeff in ((1,1,1,0),(2,1,0,1),(1,2,-1,1),(3,-1,2,1)):
        if norm8(coeff)%p==0:continue
        h=octic_local(coeff,p)
        for j in (1,3,5,7):assert octic_local(conj8(coeff,j),p)==j*h%8
        eta=cm(coeff,conj8(coeff,5))
        assert eta[1]==eta[3]==0
        assert quartic_local(eta[0],eta[2],p)==h%4
print({"cross_parameter_cases":couplings,"gaussian_local_and_torus_cases":count,"full_octic_cases":full,"prime_mod8_branches":sorted({p%8 for p in ps})})

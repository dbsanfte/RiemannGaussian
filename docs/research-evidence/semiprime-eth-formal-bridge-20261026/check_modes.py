#!/usr/bin/env python3
"""Exact tiny D.12/D.16 controls. No asymptotic proof or factoring test."""
import argparse,itertools,json,math
from fractions import Fraction
from pathlib import Path

def izadd(x,y):return (x[0]+y[0],x[1]+y[1])
def izmul(x,y):return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0]-x[1]*y[1])
def v2(x):
    if not x:return 10**6
    if isinstance(x,Fraction):return v2(x.numerator)-v2(x.denominator)
    x=abs(x);return (x&-x).bit_length()-1

class Ring:
    # u^2+u+1=0, irreducible modulo2; exact unramified rank2 control.
    def __init__(self,p):self.p=p;self.n=1<<p;self.zero=(0,0);self.one=(1,0)
    def elt(self,x):return (x%self.n,0) if isinstance(x,int) else (x[0]%self.n,x[1]%self.n)
    def add(self,x,y):return self.elt(izadd(x,y))
    def neg(self,x):return self.elt((-x[0],-x[1]))
    def sub(self,x,y):return self.add(x,self.neg(y))
    def mul(self,x,y):return self.elt(izmul(x,y))
    def scale(self,x,c):return self.elt((x[0]*c,x[1]*c))
    def pow(self,x,k):
        z=self.one
        while k:
            if k&1:z=self.mul(z,x)
            x=self.mul(x,x);k//=2
        return z
    def inv(self,x):
        d=x[0]*x[0]-x[0]*x[1]+x[1]*x[1]
        assert d%2
        return self.scale(self.elt((x[0]-x[1],-x[1])),pow(d,-1,self.n))
    def frac(self,x):
        out=[]
        for a in x:
            a=Fraction(a);assert a.denominator%2
            out.append(a.numerator*pow(a.denominator,-1,self.n)%self.n)
        return tuple(out)

def fixture(t,zeta,p,active=None):
    a=2;L=1<<a;alpha=2*L;S=list(range(-L,L));i=v2(t);step=1<<(i+1)
    if active is None:active=list(range(L))
    R=Ring(p);T=(t+alpha*zeta[0],alpha*zeta[1])
    cp=math.prod(-s for s in S if s)
    c=(1,0)
    for s in S:c=izmul(c,izadd(T,(-s,0)))
    assert min(v2(Fraction(x,cp)) for x in c)>=a+1
    def exact_w(x,y):
        out=(1,0)
        for s in S:
            if s!=y-x:out=izmul(out,izadd(T,(-s,0)))
        return R.frac(tuple(Fraction(z,cp) for z in out))
    W=[[exact_w(x,y) for y in range(L)] for x in range(L)]
    rowgroup=lambda x:(x>>i)&1
    colgroup=lambda y:1-((y>>i)&1)
    modes=[];coeff={};checks=0
    for y0 in range(step):
        ys=[y for y in range(y0,L,step) if y in active];source=colgroup(y0);target=1-source
        for b in range(p-1):
            if b and not any(pow((y-y0)//step,b,R.n) for y in ys):continue
            idx=len(modes);modes.append(dict(y0=y0,b=b,w=b+1,source=source,target=target,ys=ys))
            for x in range(L):
                if rowgroup(x)!=target:continue
                d=izadd(T,(x-y0,0));v=min(v2(d[0]),v2(d[1]));assert v<=i
                unit=R.elt((d[0]//(1<<v),d[1]//(1<<v)))
                factor=tuple(Fraction(z*(step**b),cp*(1<<(v*(b+1)))) for z in c)
                assert min(v2(z) for z in factor)>=b+1
                coeff[x,idx]=R.mul(R.frac(factor),R.pow(R.inv(unit),b+1))
    for x in range(L):
        for y in active:
            if rowgroup(x)==colgroup(y):continue
            got=R.zero
            for m,info in enumerate(modes):
                if info['y0']==y%step:
                    got=R.add(got,R.scale(coeff[x,m],pow(y//step,info['b'],R.n)))
            assert got==W[x][y],(t,zeta,p,x,y,got,W[x][y]);checks+=1
    return R,W,modes,coeff,rowgroup,colgroup,checks

def contraction_control(t,zeta,p,forced=False,active=None):
    R,W,modes,coef,rg,cg,checks=fixture(t,zeta,p,active);L=len(W);nm=len(modes);zero=(0,)*nm
    if active is None:active=list(range(L))
    rows=[[x for x in active if rg(x)==g] for g in range(2)]
    cols=[[y for y in active if cg(y)==g] for g in range(2)]
    assignments=[tuple(dict(zip(active,bits)).get(k,0) for k in range(L)) for bits in itertools.product((0,1),repeat=len(active))]
    def kernel(X,Y,local=False):
        out=R.one
        for x in active:
            z=R.zero
            for y in active:
                if X[y] and (not local or rg(x)==cg(y)):z=R.add(z,W[x][y])
            out=R.mul(out,z if Y[x] else R.sub(R.one,z))
        return out
    forced_pair=None
    if forced:
        forced_pair=next((X,Y) for X in assignments for Y in assignments if kernel(X,Y)!=kernel(X,Y,True))
    def weights(X,Y):
        if forced:return R.one if (X,Y)==forced_pair else R.zero
        val=1
        for g in range(2):
            xr=sum(X[y]<<k for k,y in enumerate(cols[g]));yr=sum(Y[x]<<k for k,x in enumerate(rows[g]))
            val*=((yr+1)*(g+1)+1)*(xr*xr+g+1)
        return R.elt(val)
    direct=R.zero;local=R.zero
    for X in assignments:
        for Y in assignments:
            w=weights(X,Y);direct=R.add(direct,R.mul(w,kernel(X,Y)));local=R.add(local,R.mul(w,kernel(X,Y,True)))
    local_data=[[],[]];supports=[set(),set()]
    def pmul(A,B):
        out={}
        for ex,c in A.items():
            for ey,d in B.items():
                ez=tuple(x+y for x,y in zip(ex,ey));out[ez]=R.add(out.get(ez,R.zero),R.mul(c,d))
        return out
    for g in range(2):
        for xb in itertools.product((0,1),repeat=len(cols[g])):
            X=dict(zip(cols[g],xb))
            for yb in itertools.product((0,1),repeat=len(rows[g])):
                Y=dict(zip(rows[g],yb));pol={zero:R.one}
                for x in rows[g]:
                    loc=R.zero
                    for y in cols[g]:
                        if X[y]:loc=R.add(loc,W[x][y])
                    aff={zero:loc if Y[x] else R.sub(R.one,loc)}
                    for m,info in enumerate(modes):
                        if info['target']==g:
                            ex=list(zero);ex[m]=1;aff[tuple(ex)]=coef[x,m] if Y[x] else R.neg(coef[x,m])
                    pol=pmul(pol,aff)
                for ex,c in pol.items():
                    assert min(v2(x) for x in c)>=min(p,sum(e*mo['w'] for e,mo in zip(ex,modes)))
                supports[g].update(pol)
                if forced:
                    weight=R.one if all(forced_pair[0][y]==X[y] for y in cols[g]) and all(forced_pair[1][x]==Y[x] for x in rows[g]) else R.zero
                else:
                    xr=sum(X[y]<<k for k,y in enumerate(cols[g]));yr=sum(Y[x]<<k for k,x in enumerate(rows[g]))
                    weight=R.elt(((yr+1)*(g+1)+1)*(xr*xr+g+1))
                source=[]
                for info in modes:
                    source.append(sum(pow((y-info['y0'])//(1<<(v2(t)+1)),info['b'],R.n)*X.get(y,0) for y in info['ys'])%R.n if info['source']==g else 0)
                local_data[g].append((pol,weight,source))
    total=R.zero;tuple_count=0
    for ex0 in sorted(supports[0]):
        for ex1 in sorted(supports[1]):
            beta=tuple(x+y for x,y in zip(ex0,ex1));wt=sum(e*mo['w'] for e,mo in zip(beta,modes))
            if wt>=p:continue
            tuple_count+=1;child=[]
            for g in range(2):
                target=tuple(e if mo['target']==g else 0 for e,mo in zip(beta,modes));acc=R.zero
                for pol,w,source in local_data[g]:
                    val=R.mul(w,pol.get(target,R.zero))
                    for m,info in enumerate(modes):
                        if info['source']==g:val=R.scale(val,pow(source[m],beta[m],R.n))
                    acc=R.add(acc,val)
                child.append(acc)
            total=R.add(total,R.mul(child[0],child[1]))
    assert total==direct,(t,zeta,p,total,direct)
    if forced:assert direct!=local,'negative control must expose crossing contribution'
    return dict(t=t,zeta=list(zeta),precision=p,active_slots=active,modes=nm,mode_weight_tuples=tuple_count,crossing_entry_checks=checks,direct=list(direct),children=list(total),local_only=list(local),forced=forced)

ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=Path(__file__).with_name('mode-controls.json'));args=ap.parse_args()
entry_checks=0
for t in (-1,1,2):
    for z in ((0,0),(1,0),(0,1),(1,1)):
        for p in (4,6,7):entry_checks+=fixture(t,z,p)[-1]
fixtures=[contraction_control(1,(1,0),6),contraction_control(1,(0,1),6,True),contraction_control(-1,(1,1),6,True),contraction_control(2,(0,1),6,True),contraction_control(2,(1,0),6,True,[0,1,3]),contraction_control(2,(0,1),6,True,[0,1])]
# Creation-time lifting is entrywise, not a ring homomorphism.
oldp,newp=3,7
x=(1<<oldp)-1;y=2
lift_product=(x*y)%(1<<oldp)
assert lift_product!=(x*y)%(1<<newp)
# The canonical lifted initial tensor entries still give the right contraction modulo old precision.
old_tables=[[7,4],[6,3]]
old_contraction=sum(a*b for a,b in zip(*old_tables))%(1<<oldp)
lifted_contraction=sum(a*b for a,b in zip(*old_tables))%(1<<newp)
assert lifted_contraction%(1<<oldp)==old_contraction
result=dict(status='PASS',scope='tiny exact local algebra controls; not a full D.4 proof or factoring campaign',ring='(Z/2^p)[u]/(u^2+u+1)',crossing_entry_checks=entry_checks,contraction_fixtures=fixtures,creation_time_lift=dict(nonmultiplicative_example=[x,y,lift_product,(x*y)%(1<<newp)],reduction_consistent=True))
args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(status='PASS',crossing_entry_checks=entry_checks,contraction_fixtures=len(fixtures))))

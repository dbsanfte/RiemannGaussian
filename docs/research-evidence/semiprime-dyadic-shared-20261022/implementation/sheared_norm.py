"""Exact reference: product-tree moments, inverse transposed Vandermonde, dyadic norms.
Polynomial kernels are schoolbook; this module is not a soft-linear timing certificate.
"""
from math import gcd

class NonunitError(ValueError):
    def __init__(self, divisor, modulus, context):
        self.divisor, self.modulus, self.context = divisor, modulus, context
        super().__init__(f"{context}: gcd={divisor} modulo {modulus}")

def inv(x, n):
    g=gcd(x,n)
    if g != 1: raise NonunitError(g,n,"inverse")
    return pow(x,-1,n)

def trim(a):
    a=list(a)
    while a and a[-1]==0: a.pop()
    return a

def add(a,b,n):
    c=[0]*max(len(a),len(b))
    for i,x in enumerate(a): c[i]=(c[i]+x)%n
    for i,x in enumerate(b): c[i]=(c[i]+x)%n
    return trim(c)

def mul(a,b,n,limit=None):
    if not a or not b: return []
    size=len(a)+len(b)-1
    if limit is not None: size=min(size,limit)
    c=[0]*size
    for i,x in enumerate(a):
        for j,y in enumerate(b[:max(0,size-i)]): c[i+j]=(c[i+j]+x*y)%n
    return trim(c)

def series_inverse(a,t,n):
    if t==0: return []
    b=[inv(a[0] if a else 0,n)]
    while len(b)<t:
        k=min(2*len(b),t)
        ab=mul(a[:k],b,n,k)
        correction=[(-x)%n for x in ab]+[0]*(k-len(ab))
        correction[0]=(correction[0]+2)%n
        b=mul(b,correction,n,k)+[0]*k
        b=b[:k]
    return b

def rem(a,b,n):
    a=trim(a); b=trim(b)
    if not b or b[-1]!=1: raise ValueError("remainder requires monic divisor")
    while len(a)>=len(b):
        c=a[-1]; d=len(a)-len(b)
        for j,x in enumerate(b): a[d+j]=(a[d+j]-c*x)%n
        a=trim(a)
    return a

def product_tree(points,n):
    if not points: return None
    if len(points)==1: return ([-points[0]%n,1],None,None)
    h=len(points)//2
    l=product_tree(points[:h],n);r=product_tree(points[h:],n)
    return (mul(l[0],r[0],n),l,r)

def multipoint(poly,points,n):
    tree=product_tree(points,n)
    if tree is None:return []
    def descend(f,t):
        f=rem(f,t[0],n)
        if t[1] is None:return [f[0] if f else 0]
        return descend(f,t[1])+descend(f,t[2])
    return descend(poly,tree)

def rational_moments(coeff,nodes,t,n):
    """First t moments sum_i coeff_i nodes_i^j by rational product tree."""
    if not nodes:return [0]*t
    def build(lo,hi):
        if hi-lo==1:return [coeff[lo]%n],[1,-nodes[lo]%n]
        h=(lo+hi)//2
        p,q=build(lo,h);r,s=build(h,hi)
        return add(mul(p,s,n),mul(r,q,n),n),mul(q,s,n)
    p,q=build(0,len(nodes))
    out=mul(p,series_inverse(q,t,n),n,t)
    return out+[0]*(t-len(out))

def inverse_moments(values,nodes,n):
    """Inverse transposed Vandermonde using rational numerator and remainder tree."""
    t=len(nodes)
    if len(values)!=t:raise ValueError("one moment per known node required")
    if not t:return []
    inverse_nodes=[inv(x,n) for x in nodes]
    def den(lo,hi):
        if hi-lo==1:return [1,-nodes[lo]%n]
        h=(lo+hi)//2
        return mul(den(lo,h),den(h,hi),n)
    d=den(0,t)
    p=mul(d,values,n,t)
    dp=[i*d[i]%n for i in range(1,len(d))]
    pvals=multipoint(p,inverse_nodes,n)
    deriv=multipoint(dp,inverse_nodes,n)
    # Unit derivatives certify pairwise unit node separation. On a bad input,
    # individual pair fallback can distinguish proper from saturated collisions.
    for v in deriv:
        g=gcd(v,n)
        if g!=1:
            if g==n:
                for i,x in enumerate(nodes):
                    for y in nodes[:i]:
                        h=gcd(x-y,n)
                        if 1<h<n:raise NonunitError(h,n,"node separation")
            raise NonunitError(g,n,"node separation")
    return [(-nodes[i]*pvals[i]*inv(deriv[i],n))%n for i in range(t)]

def sparse_product(a,b,support,eta,n):
    """Multiply on a SUPPLIED full candidate support; actual geometric moments."""
    support=tuple(sorted(set(support)))
    if not support:
        if a or b:raise ValueError("candidate support omits input")
        return {}
    maxj=max(j for j,e in support);base=maxj+1
    encoded={key:j+base*e for key in support for j,e in [key]}
    if len(set(encoded.values()))!=len(support):raise ValueError("encoding collision")
    if any(e<0 or j<0 for j,e in support):raise ValueError("normalize Laurent input first")
    if not set(a)<=set(support) or not set(b)<=set(support):
        raise ValueError("candidate support omits input")
    nodes=[pow(eta,encoded[key],n) for key in support]
    va=rational_moments([a.get(key,0) for key in support],nodes,len(nodes),n)
    vb=rational_moments([b.get(key,0) for key in support],nodes,len(nodes),n)
    coeff=inverse_moments([x*y%n for x,y in zip(va,vb)],nodes,n)
    return {key:c for key,c in zip(support,coeff) if c}

def _put(d,key,value,n):
    d[key]=(d.get(key,0)+value)%n
    if not d[key]:del d[key]

def norm_tangent(m,s,gamma,t,u,n,eta,precision=None):
    """Norm over X^m=Y of F+eps U. U is a scalar coefficient list.

    Returns (Q,V,ledger), sparse (z_degree,Y_exponent)->coefficient dictionaries.
    Optional precision=h returns exact coefficients z^j for j<h.
    Full products are reconstructed through degree 2q before truncation.
    Assumes separated interpolation nodes; raises NonunitError on guard failure.
    """
    if type(m) is not int or m<1 or m&(m-1):raise ValueError("m must be a power of two")
    if type(n) is not int or n<3 or n%2==0:raise ValueError("modulus must be odd >=3")
    if precision is not None and (type(precision) is not int or precision<1):
        raise ValueError("precision must be a positive integer or None")
    h=m+1 if precision is None else precision
    u=trim([x%n for x in u])
    if len(u)>2*m+1:raise ValueError("U degree must be <=2m")
    inv(eta,n)
    q={};v={}
    for e,c in enumerate([gamma*gamma,2*gamma,1]):_put(q,(0,e),c,n)
    for e,c in enumerate([1,2*gamma,gamma*gamma]):_put(q,(1,s+e),-t*t*c,n)
    for e,c in enumerate(u):_put(v,(0,e),c,n)
    degree_u=max(0,len(trim([x%n for x in u]))-1)
    q={key:c for key,c in q.items() if key[0]<h}
    v={key:c for key,c in v.items() if key[0]<h}
    p=1;ledger=[]
    while p<m:
        degree=min(p,h-1)
        shear=s//p;r=s-shear*p
        def normalize(f):
            return {(j,e-shear*j):c for (j,e),c in f.items()}
        qn,vn=normalize(q),normalize(v)
        if any(e<0 for j,e in list(qn)+list(vn)):raise AssertionError("negative normalized exponent")
        def conjugate(f):
            return {(j,e):(-c if (e+shear*j)%2 else c)%n for (j,e),c in f.items()}
        width=4+(degree_u+p-1)//p
        support=[]
        for j in range(2*degree+1):
            low=(r*j+p-1)//p
            high=(r*j)//p+width
            support.extend((j,e) for e in range(low,high+1))
        qb=conjugate(qn);vb=conjugate(vn)
        qq=sparse_product(qn,qb,support,eta,n)
        vq=sparse_product(vn,qb,support,eta,n)
        qv=sparse_product(qn,vb,support,eta,n)
        vv=dict(vq)
        for key,c in qv.items():_put(vv,key,c,n)
        def filter_even(f):
            out={}
            for (j,e),c in f.items():
                actual=e+shear*j
                if actual%2:
                    if c%n:raise AssertionError("odd coefficient did not cancel")
                elif j<h:_put(out,(j,actual//2),c,n)
            return out
        q,v=filter_even(qq),filter_even(vv)
        base=2*degree+1
        span=max((j+base*e for j,e in support),default=0)
        ledger.append(dict(p=p,q=degree,radix=base,precision=h,shear=shear,remainder=r,support=len(support),span=span))
        p*=2
    return q,v,ledger

def evaluate_sparse(poly,z,y,n):
    return sum(c*pow(z,j,n)*pow(y,e,n) for (j,e),c in poly.items())%n

def trace_prefix(q,v,length,n):
    """Specialize Y=1 and expand V/Q to requested precision."""
    def at_one(f):
        a=[0]*(1+max((j for j,e in f),default=0))
        for (j,e),c in f.items():a[j]=(a[j]+c)%n
        return a
    out=mul(at_one(v),series_inverse(at_one(q),length,n),n,length)
    return out+[0]*(length-len(out))

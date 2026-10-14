"""Independent exact arithmetic and conditional fixed-filter admission.

Prime Euler locals, not production convolution routines, generate targets.
No finite Gram, numerical minimizer or pole-budget admission proves a bound.
"""
from fractions import Fraction
from itertools import combinations, product
from math import comb, isqrt

DIVISORS=[1,2,3,4,5,6,7,8,9,12,16]
TARGETS=[{'r':r,'l':k-r} for k in (1,2,3) for r in range(k+1)]


def integer(n,minimum=0):
    if type(n) is not int or n<minimum:raise ValueError('integer outside exact domain')
    return n


def rational(n):
    if isinstance(n,(bool,float)) or not isinstance(n,(int,str,Fraction)):raise ValueError('exact rational required')
    return Fraction(n)


def local_coefficient(r,l,j):
    """[z^j](1-z)^(r+l)/(1-z^2)^l, arbitrary nonnegative integer arities."""
    integer(r);integer(l);integer(j)
    k=r+l
    if not k:raise ValueError('positive total arity required')
    if l==0:return (-1)**j*comb(k,j) if j<=k else 0
    return sum((-1)**a*comb(k,a)*comb(l+(j-a)//2-1,(j-a)//2)
               for a in range(min(k,j)+1) if (j-a)%2==0)


def factor_structure(N):
    integer(N,1);least=list(range(N+1))
    for p in range(2,isqrt(N)+1):
        if least[p]!=p:continue
        for n in range(p*p,N+1,p):
            if least[n]==n:least[n]=p
    exponent=[0]*(N+1);core=[0]*(N+1);core[1]=1
    for n in range(2,N+1):
        p=least[n];rest=n//p
        if rest%p==0:exponent[n]=exponent[rest]+1;core[n]=core[rest]
        else:exponent[n]=1;core[n]=rest
    return exponent,core


def actual_coefficients(N,r,l,structure=None):
    integer(N,1);integer(r);integer(l)
    if not r+l:raise ValueError('positive total arity required')
    exponent,core=structure or factor_structure(N)
    if min(len(exponent),len(core))<=N:raise ValueError('complete factor structure required')
    local=[local_coefficient(r,l,j) for j in range(N.bit_length())]
    out=[0]*(N+1);out[1]=1
    for n in range(2,N+1):out[n]=out[core[n]]*local[exponent[n]]
    return out


def prefix(coefficients):
    if not coefficients or coefficients[0]!=0:raise ValueError('zero sentinel required')
    out=[0];total=0
    for a in coefficients[1:]:total+=a;out.append(total)
    return out


def canonical_filter(terms):
    weights={}
    for term in terms:
        if isinstance(term,dict):
            if set(term)!={'divisor','weight'}:raise ValueError('fixed divisor and rational weight only')
            d,w=term['divisor'],term['weight']
        elif isinstance(term,(tuple,list)) and len(term)==2:d,w=term
        else:raise ValueError('fixed filter term required')
        integer(d,1);weights[d]=weights.get(d,Fraction(0))+rational(w)
    return [{'divisor':d,'weight':str(w)} for d,w in sorted(weights.items()) if w]


def filtered_prefix(sums,terms):
    terms=canonical_filter(terms)
    return [sum((rational(t['weight'])*sums[n//t['divisor']] for t in terms),Fraction(0)) for n in range(len(sums))]


def covariance(sums,X,divisors=DIVISORS,max_products=1000000000):
    """Full complete Python-integer Gram; no int64 arithmetic or dropped pairs."""
    integer(X,1);integer(max_products,1)
    if len(sums)<=2*X-1:raise ValueError('complete block prefix required')
    if not sums or sums[0]!=0 or any(type(v) is not int for v in sums):raise ValueError('complete integer prefix required')
    ds=list(divisors)
    if any(type(d) is not int or d<1 for d in ds) or len(set(ds))!=len(ds):raise ValueError('distinct positive divisors required')
    products=X*len(ds)*(len(ds)+1)//2
    if products>max_products:raise RuntimeError('complete covariance work budget exceeded')
    columns=[[sums[n//d] for n in range(X,2*X)] for d in ds]
    matrix=[[None]*len(ds) for _ in ds]
    for i in range(len(ds)):
        for j in range(i,len(ds)):
            value=sum(a*b for a,b in zip(columns[i],columns[j]));matrix[i][j]=matrix[j][i]=str(Fraction(value,X*X))
    return matrix


def filtered_energy(matrix,terms,divisors=DIVISORS):
    terms=canonical_filter(terms);index={d:i for i,d in enumerate(divisors)}
    if any(t['divisor'] not in index for t in terms):raise ValueError('unavailable full covariance column')
    return sum((rational(a['weight'])*rational(b['weight'])*rational(matrix[index[a['divisor']]][index[b['divisor']]])
                for a in terms for b in terms),Fraction(0))


def conditional_certificate(r,l,terms):
    """Independent projected pole-budget theorem; no estimate assumed proved."""
    integer(r);integer(l);k=r+l
    if not k:raise ValueError('positive total arity required')
    terms=canonical_filter(terms);m=len(terms);admitted=bool(m) and m<=k
    return {'target':{'r':r,'l':l},'filter':terms,'support_size':m,
            'conditional_bridge_admitted':admitted,'maximum_filter_zero_multiplicity':max(0,m-1),
            'minimum_surviving_pole_order':k-m+1 if admitted else None,
            'estimate_proved':False,'RH_proved':False}


def boxed_least_squares(matrix,support,divisors=DIVISORS,box=8):
    """Exact finite minimization, independently checkable by convex KKT signs."""
    support=list(support);box=rational(box)
    if box<=0 or len(support) not in (1,2) or len(set(support))!=len(support) or any(d not in divisors[1:] for d in support):raise ValueError('one/two nonleading distinct support required')
    indices=[divisors.index(d) for d in support];H=[[rational(matrix[i][j]) for j in indices] for i in indices]
    g=[rational(matrix[0][i]) for i in indices];a=rational(matrix[0][0])
    if any(H[i][j]!=H[j][i] for i in range(len(indices)) for j in range(len(indices))):raise ValueError('symmetric support required')
    if H[0][0]<=0 or (len(indices)==2 and (H[1][1]<=0 or H[0][0]*H[1][1]-H[0][1]**2<=0)):
        return {'status':'missing','reason':'singular_or_nonpositive_support; explicit enumerated grid fallback retained','support':support,'choices':[]}
    def clip(x):return min(box,max(-box,x))
    choices=[]
    if len(indices)==1:choices=[{'kind':'clipped_exact_stationary','weights':[clip(-g[0]/H[0][0])]}]
    else:
        det=H[0][0]*H[1][1]-H[0][1]**2
        x=(g[1]*H[0][1]-g[0]*H[1][1])/det;y=(g[0]*H[0][1]-g[1]*H[0][0])/det
        if abs(x)<=box and abs(y)<=box:choices.append({'kind':'interior','weights':[x,y]})
        for x in (-box,box):choices.append({'kind':'edge_first','weights':[x,clip(-(g[1]+H[0][1]*x)/H[1][1])]})
        for y in (-box,box):choices.append({'kind':'edge_second','weights':[clip(-(g[0]+H[0][1]*y)/H[0][0]),y]})
        for x,y in product((-box,box),repeat=2):choices.append({'kind':'corner','weights':[x,y]})
    def objective(w):return a+2*sum(g[i]*w[i] for i in range(len(w)))+sum(H[i][j]*w[i]*w[j] for i in range(len(w)) for j in range(len(w)))
    best=min(choices,key=lambda c:(objective(c['weights']),tuple(c['weights']),c['kind']))
    w=best['weights']
    for i,x in enumerate(w):
        gradient=g[i]+sum(H[i][j]*w[j] for j in range(len(w)))
        if (x==-box and gradient<0) or (x==box and gradient>0) or (-box<x<box and gradient):raise ValueError('quadratic candidate violates exact convex KKT signs')
    return {'status':'available','support':support,'pooled_matrix':[[str(v) for v in row] for row in H],'linear':list(map(str,g)),
            'constant':str(a),'choices':[{'kind':c['kind'],'weights':list(map(str,c['weights'])),'objective':str(objective(c['weights']))} for c in choices],
            'exact_weights':list(map(str,w)),'objective':str(objective(w)),'quantized_weights':[str(v.limit_denominator(64)) for v in w],
            'solver':'exact constrained quadratic interior/edges/corners; no floating solver'}


PROOF_SCOPE='''For every actual target mu^{*r}*lambda^{*l}, k=r+l>=1,
its prime-local generating function is (1-z)^k/(1-z^2)^l. Its global
Dirichlet function is zeta(2s)^l/zeta(s)^k initially for Re(s)>1. A fixed
nonzero m-term filter has multiplier P(s)=sum_j w_j d_j^(-s). If P and its
first m-1 derivatives vanished together, the distinct real logs(log d_j)
would give an invertible derivative Vandermonde, forcing each nonzero
w_j d_j^(-s) to vanish. Thus every filter zero has multiplicity at most
m-1. At an ordinary zeta zero rho with Re(rho)>1/2, zeta(2rho)^l is nonzero;
a zero of multiplicity v produces pole order kv-(m-1)>=k-m+1 when m<=k.
A genuinely proved cofinal filtered critical block energy estimate makes
the filtered Dirichlet function analytic on Re(s)>1/2 by dyadic Mellin
Cauchy-Schwarz, excludes every such pole, and implies RH via symmetry.
No finite numerical estimate or coefficient-fitting procedure supplies
that critical premise. A normalized innovation premise for nonnegative
filtered energy implies the direct energy premise by the exact dyadic
geometric telescope, initialized by G(1)=1 when w1=1. All covariance
terms and filter signs must be retained before taking the squared energy.
'''

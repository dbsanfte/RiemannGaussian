"""Development arithmetic only: complete signed inverse-control Gram profiles.
No finite profile supplies an all-scale bound. Index zero is a zero sentinel.
"""
from fractions import Fraction

class ResourceMissing(Exception): pass
class Budget:
    def __init__(self, limit):
        if type(limit) is not int or limit<0: raise ValueError('nonnegative integer work budget required')
        self.limit=limit; self.used=0
    def charge(self,n=1):
        if self.used+n>self.limit: raise ResourceMissing('work_budget_exceeded')
        self.used+=n

def _positive_n(N):
    if type(N) is not int or N<1: raise ValueError('positive integer N required')

def _exact(x):
    if isinstance(x,bool) or isinstance(x,float): raise ValueError('bool/float coefficients forbidden')
    if isinstance(x,int) or isinstance(x,Fraction): return x
    if isinstance(x,str):
        v=Fraction(x)
        return v.numerator if v.denominator==1 else v
    raise ValueError('exact int, Fraction or rational string required')

def convolution(a,b,N,budget):
    _positive_n(N)
    if len(a)<=N or len(b)<=N: raise ValueError('complete convolution inputs required')
    budget.charge(3*(N+1))
    a=[_exact(x) for x in a[:N+1]]; b=[_exact(x) for x in b[:N+1]]
    out=[0]*(N+1)
    for i in range(1,N+1):
        if not a[i]: continue
        for j in range(1,N//i+1):
            budget.charge(); out[i*j]+=a[i]*b[j]
    return out

def prefix(a,budget=None):
    if budget: budget.charge(2*len(a))
    out=[0]*len(a)
    for n in range(1,len(a)): out[n]=out[n-1]+a[n]
    return out

def complete_arithmetic(N,budget):
    """Complete linear prime sieve followed by generic product-loop convolutions."""
    _positive_n(N); budget.charge(7*(N+1))
    mu=[0]*(N+1); lam=[0]*(N+1); primes=[]; composite=[False]*(N+1)
    if N: mu[1]=lam[1]=1
    for n in range(2,N+1):
        budget.charge()
        if not composite[n]: primes.append(n); mu[n]=-1; lam[n]=-1
        for p in primes:
            m=n*p
            if m>N: break
            budget.charge(); composite[m]=True; lam[m]=-lam[n]
            if n%p==0: mu[m]=0; break
            mu[m]=-mu[n]
    one=[0]+[1]*N
    c=convolution(mu,lam,N,budget)
    h=convolution(one,[x*x for x in mu],N,budget)
    if h!=[abs(x) for x in c]: raise ValueError('actual h != abs(c)')
    return mu,lam,c,h

def inverse(a,N,budget):
    _positive_n(N); budget.charge(N+1)
    if len(a)<=N: raise ValueError("complete inverse input required")
    a=[_exact(x) for x in a[:N+1]]
    if a[1]!=1: raise ValueError('inverse control requires a[1]=1')
    out=[0]*(N+1); out[1]=1
    # Independent generic convolution recurrence: contributions propagate by multiples.
    for d in range(1,N+1):
        if not out[d]: continue
        for j in range(2,N//d+1):
            budget.charge(); out[d*j]-=out[d]*a[j]
    return out

def _profile(a,h,scales,budget,verify):
    N=4*max(scales)-1
    if len(a)<=N or len(h)<=N: raise ValueError('complete coefficient coverage required')
    budget.charge(10*(N+1))
    a=[_exact(x) for x in a[:N+1]]; h=[_exact(x) for x in h[:N+1]]
    if a[0] or h[0]: raise ValueError('index zero must be zero')
    identity=None
    if verify:
        ah=convolution(a,h,N,budget)
        identity=all(v==(1 if n==1 else 0) for n,v in enumerate(ah))
        if not identity: raise ValueError('a*h != delta; Gram inverse identity unavailable')
    C=prefix(a,budget); squares=[x*x for x in C]
    inc=[0]+[squares[n]-squares[n-1] for n in range(1,N+1)]
    diagonal_at_t=prefix(convolution([x*x for x in h],inc,N,budget),budget)
    energy=prefix(squares,budget); diagonal=prefix(diagonal_at_t,budget)
    gram_prefix=prefix(convolution(a,h,N,budget),budget)
    gram_energy=prefix([x*x for x in gram_prefix],budget)
    def block(P,X): return P[2*X-1]-P[X-1]
    rows=[]
    for X in scales:
        budget.charge(20)
        A=block(energy,X); A2=block(energy,2*X); S=block(diagonal,X); S2=block(diagonal,2*X)
        G=block(gram_energy,X); G2=block(gram_energy,2*X)
        rows.append(dict(X=X,gram_energy_X=G,gram_energy_2X=G2,A_X=A,A_2X=A2,Delta=A2-4*A,S_X=S,S_2X=S2,Delta_S=S2-4*S,
                         other_diagonal_X=S-h[1]*h[1]*A,other_diagonal_2X=S2-h[1]*h[1]*A2,
                         cross_X=G-S,cross_2X=G2-S2,
                         Delta_cross=(G2-S2)-4*(G-S)))
    return dict(coefficients=a,control=h,prefix=C,rows=rows,inverse_identity_verified=identity,
                full_divisor_diagonal=True,global_bound_proved=False,
                cost_scope="charged scalar arithmetic and list allocation cells; not bit complexity, serialization or interpreter overhead",
                coefficient_bit_complexity_certified=False)

def _serial(v):
    if isinstance(v,Fraction): return str(v)
    if isinstance(v,list): return [_serial(x) for x in v]
    if isinstance(v,dict): return {k:_serial(x) for k,x in v.items()}
    return v

def profile_from_coefficients(a,h,scales,*,work_budget=30000000,max_n=1048575,verify_inverse=True):
    B=None; N=None
    try:
        scales=list(scales)
        if not scales or any(type(x) is not int or x<1 for x in scales): raise ValueError('positive integer scales required')
        N=4*max(scales)-1; B=Budget(work_budget)
        if type(max_n) is not int or max_n<1: raise ValueError('positive integer max_n required')
        if N>max_n: raise ResourceMissing('coefficient_lookahead_limit')
        value=_profile(a,h,scales,B,verify_inverse)
        return dict(status='available',value=_serial(value),reason=None,cost=B.used,lookahead=N)
    except ResourceMissing as e: return dict(status='missing',value=None,reason=str(e),cost=B.used if B else 0,lookahead=N)
    except (ValueError,TypeError,IndexError,ZeroDivisionError) as e: return dict(status='invalid',value=None,reason=str(e),cost=B.used if B else 0,lookahead=N)

def arithmetic_profile(scales,*,sequence='convolution',control='inverse_abs',shift=0,dilate=1,work_budget=30000000,max_n=1048575,return_tau_profile=False):
    B=None; N=None
    try:
        scales=list(scales)
        if not scales or any(type(x) is not int or x<1 for x in scales): raise ValueError('positive integer scales required')
        if type(return_tau_profile) is not bool: raise ValueError('boolean return_tau_profile required')
        if type(max_n) is not int or max_n<1: raise ValueError('positive integer max_n required')
        if type(shift) is not int or type(dilate) is not int or dilate<1: raise ValueError('integer shift and positive dilation required')
        N=4*max(scales)-1; source_N=max(N,dilate*N+shift,1); B=Budget(work_budget)
        if max(N,source_N)>max_n: raise ResourceMissing('coefficient_lookahead_limit')
        mu,lam,c,h=complete_arithmetic(source_N,B)
        sources={'convolution':c,'mu':mu,'liouville':lam,'unsigned_h':h}
        if sequence not in sources: raise ValueError('unsupported sequence')
        src=sources[sequence]; a=[0]+[src[dilate*n+shift] if 1<=dilate*n+shift<=source_N else 0 for n in range(1,N+1)]
        if control=='inverse_abs':
            inv=inverse(a,N,B); hc=[abs(x) for x in inv]
            # Absolute inverse is generally not an inverse: retain precise distinction.
            verify=hc==inv
        elif control=='inverse': hc=inverse(a,N,B); verify=True
        elif control=='actual_h': hc=h[:N+1]; verify=True
        elif control=='divisor_count': hc=convolution([0]+[1]*N,[0]+[1]*N,N,B); verify=False
        elif control=='one': hc=[0]+[1]*N; verify=False
        else: raise ValueError('unsupported control')
        value=_profile(a,hc,scales,B,verify)
        if control=='divisor_count':
            value['constraint_scope']='filtered c*tau=square-indicator only for unmoved actual c; no full signed bound'
        if return_tau_profile:
            tau=convolution([0]+[1]*N,[0]+[1]*N,N,B)
            tp=_profile(a,tau,scales,B,False)
            hp=_profile(a,h[:N+1],scales,B,sequence=='convolution' and shift==0 and dilate==1)
            value['tau_profile']=tp
            value['actual_h_profile']=hp
            value['tau_minus_h_diagonal']=[dict(X=t['X'],at_X=t['S_X']-r['S_X'],at_2X=t['S_2X']-r['S_2X']) for t,r in zip(tp['rows'],hp['rows'])]
            value['tau_constraint_scope']='c*tau=square-indicator for unmoved actual c; filtered identity not full signed bound'
        value.update(sequence=sequence,control_kind=control,shift=shift,dilate=dilate,source_lookahead=source_N,
                     index_semantics="source[dilate*n+shift], zero outside positive indices",
                     provenance='complete linear prime sieve; generic full product-loop Dirichlet convolutions',development_only=True)
        return dict(status='available',value=_serial(value),reason=None,cost=B.used,lookahead=max(N,source_N))
    except ResourceMissing as e: return dict(status='missing',value=None,reason=str(e),cost=B.used if B else 0,lookahead=N)
    except (ValueError,TypeError,IndexError,ZeroDivisionError) as e: return dict(status='invalid',value=None,reason=str(e),cost=B.used if B else 0,lookahead=N)

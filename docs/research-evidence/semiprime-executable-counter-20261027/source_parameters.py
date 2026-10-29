"""Exact finite guards for the PINNED complete-block layout, not the old layout.
Independent Python implementation of PackingGuard + centered spectral guard.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import isqrt


def ceil_log2(n):
    if type(n) is not int or n < 1:
        raise ValueError('positive integer required')
    return (n-1).bit_length()


@dataclass(frozen=True)
class Parameters:
    r: int
    Q: int
    R: int
    epsilon: Fraction
    @property
    def dimension(self): return self.r**(2*self.Q)
    @property
    def A0(self):
        # Source TailInterval: floor((Q-1)*(r-1)/(2r) - R/2), clipped at zero.
        return max(0, ((self.Q-1)*(self.r-1)-self.r*self.R)//(2*self.r))


def scope_statistics(n, scopes):
    if type(n) is not int or n < 0: raise ValueError('invalid variable count')
    occurrences=[0]*n; M=w=0
    for scope in scopes:
        if len(set(scope)) != len(scope): raise ValueError('repeated port in factor')
        for v in scope:
            if type(v) is not int or not 0 <= v < n: raise ValueError('invalid port')
            occurrences[v]+=1
        M+=len(scope);w=max(w,len(scope))
    return dict(n=n,M=M,B=max(occurrences,default=0),w=w,
                covered=all(occurrences),occurrences=tuple(occurrences))


def check_stats(n,M,B,w,p):
    """Integer/rational sufficient tests for actual source hypotheses.

    log(2/eps) <= ceil(log2(ceil(2/eps))) for eps<=1/2; no floating logarithm.
    The last tau test is an EXTRA frozen-counter API compatibility condition.
    """
    if any(type(z) is not int for z in (n,M,B,w,p.r,p.Q,p.R)):
        raise ValueError('integer dimensions required')
    eps=Fraction(p.epsilon); failures=[]
    if min(n,M,B,w) <= 0 or not n <= M <= B*n: failures.append('positive covered incidence')
    if p.r<2 or p.Q<2 or p.R<4 or 4*p.R>p.Q or not 0<eps<=Fraction(1,2):
        failures.append('source parameter range')
    if failures: return dict(accepted=False,reasons=failures)
    D=p.dimension
    if 4*(B+w)*D*D > eps*eps*M: failures.append('source packing load')
    if 16*p.Q*p.r*p.r>n: failures.append('source head balance')
    upper=(2*eps.denominator+eps.numerator-1)//eps.numerator
    log_bound=ceil_log2(upper)
    if 32*(p.Q-1)*log_bound>p.R*p.R: failures.append('source spectral width')
    if eps*M>Fraction(n,2): failures.append('frozen-counter tau compatibility')
    return dict(accepted=not failures,reasons=failures,dimension=D,
                log_upper=log_bound,source_interval=(p.A0,p.A0+p.R),
                measurement_count_bound=2*eps*M)


def scheduled_guard(n,M,B,w):
    if type(n) is not int or n<2:
        return None,dict(accepted=False,reasons=['small input'])
    lam=ceil_log2(n)
    if lam<2:return None,dict(accepted=False,reasons=['small logarithm'])
    nu=ceil_log2(lam);r=isqrt(lam)//(nu*nu);Q=lam//(128*nu)
    R=4*(isqrt(lam)+int(isqrt(lam)**2!=lam))
    if r<2 or Q<2 or R<4 or 4*R>Q:
        return None,dict(accepted=False,reasons=['schedule range'])
    p=Parameters(r,Q,R,Fraction(1,r*lam))
    return p,check_stats(n,M,B,w,p)

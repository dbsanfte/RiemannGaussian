"""Complete actual mu*lambda prime-power cancellation matchings.

Supplied arithmetic pairing method, not learned RH-strength cancellation.
Every unmatched term is retained; budgets never return a partial success.
"""
from hashlib import sha256
import json
from math import isqrt


class Exhausted(Exception):pass


def integer(n,minimum=0):
    if type(n) is not int or n<minimum:raise ValueError('integer outside domain')
    return n


class Meter:
    def __init__(self,operations,cells,bits):
        integer(operations,1);integer(cells,1);integer(bits,1)
        self.limit=operations;self.cell_limit=cells;self.bit_limit=bits
        self.operations=0;self.cells=0;self.peak_bits=0
    def work(self,n=1):
        if self.operations+n>self.limit:raise Exhausted('operation_budget_exhausted')
        self.operations+=n
    def reserve(self,n):
        if self.cells+n>self.cell_limit:raise Exhausted('cell_budget_exhausted')
        self.cells+=n
    def array(self,n):
        self.reserve(n);self.work(n);return [0]*n
    def number(self,n):
        bits=abs(n).bit_length();self.peak_bits=max(self.peak_bits,bits)
        if bits>self.bit_limit:raise Exhausted('coefficient_bit_budget_exhausted')
        return n
    def record(self):
        return {'operations':self.operations,'allocated_scalar_cells':self.cells,'peak_coefficient_bits':self.peak_bits,'limits':{'operations':self.limit,'cells':self.cell_limit,'bits':self.bit_limit},'scope':'charged integer-loop/list/record scalar work; not physical bytes, serialization cost or total bit complexity'}


def digest(value):
    return sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def root(n,k,meter):
    integer(n);integer(k,1)
    if n<2 or k==1:return n
    if k>=n.bit_length():return 1
    lo,hi=0,n+1
    while hi-lo>1:
        meter.work(k);m=(lo+hi)//2
        if meter.number(m**k)<=n:lo=m
        else:hi=m
    return lo


def prime(p,meter):
    integer(p,2)
    for d in range(2,isqrt(p)+1):
        meter.work()
        if p%d==0:return False
    return True


def source(X,meter):
    """Complete sieve + exact actual local c(p^j)=2(-1)^j recurrence."""
    spf=meter.array(X+1);c=meter.array(X+1);h=meter.array(X+1)
    primes=[]
    for p in range(2,X+1):
        meter.work()
        if spf[p]:continue
        meter.reserve(1);primes.append(p);meter.work()
        for n in range(p,X+1,p):
            meter.work()
            if not spf[n]:spf[n]=p
    if X:c[1]=h[1]=1
    for n in range(2,X+1):
        meter.work();p=spf[n];m=n//p
        c[n]=meter.number(-c[m] if m%p==0 else -2*c[m]);h[n]=abs(c[n])
    return c,h,primes


def selected_primes(selector,X,primes,meter):
    if not isinstance(selector,dict):raise ValueError('exact selector dictionary required')
    kind=selector.get('kind')
    if kind=='fixed':
        if set(selector)!={'kind','primes'} or not isinstance(selector['primes'],list):raise ValueError('fixed prime list required')
        meter.reserve(len(selector['primes']));result=selector['primes'][:]
        if len(result)!=len(set(result)):raise ValueError('duplicate selected primes')
        for p in result:
            if not prime(p,meter):raise ValueError('selected actual prime required')
        return result
    if kind=='all_primes':
        if set(selector)!={'kind'}:raise ValueError('unexpected selector parameters')
        meter.reserve(len(primes));return primes[:]
    if kind=='fractional_prime_cutoff':
        if set(selector)!={'kind','numerator','denominator'}:raise ValueError('exact fractional cutoff required')
        a=integer(selector['numerator']);b=integer(selector['denominator'],1)
        cutoff=min(X,a*X//b)
    elif kind=='root_prime_cutoff':
        if set(selector)!={'kind','order'}:raise ValueError('root order required')
        cutoff=root(X,selector['order'],meter)
    else:raise ValueError('unsupported exact selector')
    meter.work(len(primes));result=[p for p in primes if p<=cutoff];meter.reserve(len(result));return result


def valuation(n,p):
    e=0
    while n%p==0:n//=p;e+=1
    return e,n


def edge_certificate(coefficients,n,p,X,*,meter=None):
    integer(X);integer(n,1);integer(p,2)
    if not prime(p,meter or Meter(5000000,2000000,1000000)):raise ValueError('actual prime required for an edge')
    if n*p>X or len(coefficients)<=n*p:raise ValueError('complete edge support missing')
    exponent,core=valuation(n,p)
    if exponent<1 or exponent%2!=1:raise ValueError('lower exponent must be positive odd')
    if coefficients[n]+coefficients[n*p]!=0 or abs(coefficients[n])!=abs(coefficients[n*p]):raise ValueError('signed equal-weight premise failed')
    return {'prime':p,'lower':n,'upper':n*p,'core':core,'lower_exponent':exponent,'upper_exponent':exponent+1,'c_lower':coefficients[n],'c_upper':coefficients[n*p],'pair_sum':0,'unsigned_weight_cancelled':2*abs(coefficients[n]),'scope':'local edge only; this function alone does not authenticate global actual arithmetic'}


def matching(X,selector,*,operation_budget=5000000,cell_budget=2000000,bit_budget=1000000):
    meter=None
    try:
        integer(X);meter=Meter(operation_budget,cell_budget,bit_budget)
        c,h,primes=source(X,meter);chosen=selected_primes(selector,X,primes,meter)
        matched=meter.array(X+1);edges=[];passes=[]
        for p in chosen:
            before=len(edges)
            # Every potential lower odd endpoint is a multiple p <=X/p.
            for n in range(p,X//p+1,p):
                meter.work()
                if matched[n] or matched[n*p]:continue
                e,core=valuation(n,p);meter.work(e+1)
                if e%2==0:continue
                edge=edge_certificate(c,n,p,X,meter=meter);meter.work();meter.reserve(len(edge))
                matched[n]=n*p;matched[n*p]=n
                edges.append(edge)
            meter.reserve(3);passes.append({'prime':p,'new_edges':len(edges)-before,'no_inside_partner_possible':p*p>X})
        residual=[];signed=0;unsigned=0;direct=0;total_unsigned=0
        for n in range(1,X+1):
            meter.work();direct=meter.number(direct+c[n]);total_unsigned=meter.number(total_unsigned+h[n])
            if not matched[n]:
                meter.reserve(2);residual.append({'n':n,'c':c[n]});signed=meter.number(signed+c[n]);unsigned=meter.number(unsigned+h[n])
            elif matched[matched[n]]!=n:raise RuntimeError('matching not involutive')
        if signed!=direct or 2*len(edges)+len(residual)!=X:raise RuntimeError('incomplete signed matching')
        meter.work();cancelled=meter.number(total_unsigned-unsigned)
        if cancelled+unsigned!=total_unsigned:raise RuntimeError('unsigned partition failure')
        return {'status':'available','value':{'schema':1,'X':X,'exact_selector':selector,'selector_sha256':digest(selector),'selected_prime_order':chosen,'actual_primes_through_X':primes,'source':'actual complete c=mu*lambda, constructed from complete prime sieve and every local coefficient2(-1)^j','source_coefficients':c,'source_coefficients_sha256':digest(c),'passes':passes,'edges':edges,'residual':residual,'complete_domain':[1,X],'domain_count':X,'matched_count':2*len(edges),'residual_count':len(residual),'complete_disjoint_involution':True,'signed_prefix':direct,'signed_residual':signed,'unsigned_original_charge':total_unsigned,'unsigned_residual_charge':unsigned,'unsigned_cancelled_charge':cancelled,'critical_signed_bound_proved':False,'RH_proved':False,'parameter_origin':'supplied exact selector, no numerical selector fitting inside this function'},'reason':None,'cost':meter.record()}
    except Exhausted as e:return {'status':'missing','value':None,'reason':str(e),'cost':meter.record() if meter else None}
    except (ValueError,TypeError,KeyError) as e:return {'status':'invalid','value':None,'reason':str(e),'cost':meter.record() if meter else None}


def fixed_prime_residual_formula(X,p):
    """Exact one-prime residual decomposition, independent of matched edge list."""
    integer(X);integer(p,2);meter=Meter(5000000,2000000,1000000)
    if not prime(p,meter):raise ValueError('actual prime required')
    c,h,primes=source(X,meter)
    core_signed=sum(c[n] for n in range(1,X+1) if n%p)
    core_unsigned=sum(h[n] for n in range(1,X+1) if n%p)
    boundaries=[];signed=core_signed;unsigned=core_unsigned
    odd=p;even=p*p
    while odd<=X:
        lo=X//even;hi=X//odd
        signed_core=sum(c[m] for m in range(lo+1,hi+1) if m%p)
        unsigned_core=sum(h[m] for m in range(lo+1,hi+1) if m%p)
        boundaries.append({'odd_power':odd,'even_partner_power':even,'core_lower_exclusive':lo,'core_upper_inclusive':hi,'signed_core_sum':signed_core,'unsigned_core_charge':unsigned_core})
        signed-=2*signed_core;unsigned+=2*unsigned_core;odd*=p*p;even*=p*p
    return {'X':X,'prime':p,'e0_signed_core':core_signed,'e0_unsigned_core':core_unsigned,'odd_top_boundaries':boundaries,'signed_residual':signed,'unsigned_residual_charge':unsigned,'critical_signed_bound_proved':False,'RH_proved':False}


def absolute_residual_obstruction_certificate(X):
    """Supplied all-matching obstruction, with exact rational constants.

    No coefficient/prime response is queried. Valid for actual c and EVERY
    same-core odd-positive/even-exponent partial matching inside[1,X].
    """
    integer(X,1)
    return {'schema':1,'X':X,'matching_class':'actual same-core odd exponent>=1 to next even exponent, either orientation, all endpoints<=X','isolated_class':'every squarefree integer n with X/2<n<=X','squarefree_count_lower_before_sqrt':'X/8-sqrt(X)','prime_square_reciprocal_upper':'3/4','threshold_for_linear_bound':256,'linear_bound_applies':X>=256,'squarefree_count_linear_lower':{'numerator':X,'denominator':16} if X>=256 else None,'unsigned_residual_linear_lower':{'numerator':X,'denominator':8} if X>=256 else None,'exact_threshold_check':X>=256 and X*X>=256*X,'proof':'squarefree count in(X/2,X] >=X/2-(X/2)*sum_p p^-2-sqrtX >=X/8-sqrtX; forX>=256 sqrtX<=X/16; every isolated n>1 has|c(n)|>=2','no_actual_scores_consumed':True,'signed_prefix_lower_bound_proved':False,'critical_signed_bound_proved':False,'RH_proved':False}

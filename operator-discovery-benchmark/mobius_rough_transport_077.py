"""Signed rough-prime states and exact factor-parity terminal constructions.

These identities keep prime/composite interaction. They do not bound the
coupled signed state uniformly or replace its arithmetic proof obligation.
"""
from array import array
from bisect import bisect_left,bisect_right
from fractions import Fraction as Q
from math import isqrt

import mobius_residual_fold_077 as P

MAX_PRODUCTS=500_000
_LIMIT=1
_PRIMES=array('I')


def primes_through(limit,meter):
    global _LIMIT,_PRIMES
    if type(limit) is not int or not 0<=limit<=P.MAX_HORIZON:raise ValueError('bounded prime horizon')
    meter.reserve(16*1024**2+8*(limit+_LIMIT+2))
    if limit>_LIMIT:
        sieve=bytearray(b'\x01')*(limit+1);sieve[:2]=b'\x00\x00'
        for p in range(2,isqrt(limit)+1):
            if sieve[p]:sieve[p*p:limit+1:p]=b'\x00'*((limit-p*p)//p+1)
        _PRIMES=array('I',(p for p in range(2,limit+1) if sieve[p]));_LIMIT=limit
        meter.charge(20*(limit+1))
    return _PRIMES[:bisect_right(_PRIMES,limit)]


def excluded_primes(primes):
    P.admit_primes(primes)
    if list(primes)!=sorted(primes):raise ValueError('canonical excluded prime list')


def cutoff(value):
    if type(value) is not int or value<1 or value.bit_length()>4096:raise ValueError('positive bounded-bit cutoff')
    return value


def rational_cutoff(horizon,gamma):
    """Exact ceiling of H^gamma; no square/cube/root whitelist."""
    if type(horizon) is not int or not 1<=horizon<=P.MAX_HORIZON:raise ValueError('positive bounded horizon')
    g=P.S.B.rational(gamma)
    if g<0 or horizon.bit_length()*g.numerator+g.denominator>100000:raise ValueError('nonnegative cutoff power and intermediate bit gate')
    target=horizon**g.numerator
    floor=int(P.S.B.fmpz(target).root(g.denominator))
    if not floor**g.denominator<=target<(floor+1)**g.denominator:raise ArithmeticError('exact cutoff root')
    return cutoff(floor if floor**g.denominator==target else floor+1)


def dilate(intervals,p,meter=None):
    meter=meter or P.S.Meter()
    if not P.OLD.prime(p):raise ValueError('prime dilation')
    state=P.decode(intervals,meter);result=[]
    for l,r,w in state:
        left,right=l//p,r//p
        if left>=right:continue
        if result and result[-1][1]==left and result[-1][2]==w:
            result[-1]=(result[-1][0],right,result[-1][2])
        else:result.append((left,right,w))
    return P.encode(result)


def transport(intervals,lower_cutoff,upper_cutoff,excluded=(),meter=None):
    meter=meter or P.S.Meter();excluded_primes(excluded)
    cutoff(lower_cutoff);cutoff(upper_cutoff)
    if upper_cutoff<lower_cutoff:raise ValueError('ordered roughness cutoffs')
    state=P.decode(intervals,meter);horizon=max((r for _,r,_ in state),default=0)
    primes=primes_through(min(upper_cutoff,horizon),meter)
    roster=[p for p in primes if p>lower_cutoff and p not in excluded]
    # All child coefficient functions retain the SAME parent count tokens.
    meter.reserve(32*1024**2+4*P.state_bytes(state)*(len(roster)+1)+8*(_LIMIT+1))
    children=[dict(prime=p,intervals=dilate(intervals,p,meter)) for p in roster]
    return dict(schema='rough-prime-transport-v1',lower_cutoff=lower_cutoff,
        upper_cutoff=upper_cutoff,excluded_primes=list(excluded),children=children)


def terminal_degree(horizon,y,max_degree=4):
    cutoff(y)
    if type(horizon) is not int or not 0<=horizon<=P.MAX_HORIZON or type(max_degree) is not int or not 0<=max_degree<=4:
        raise ValueError('bounded terminal domain and factor depth')
    for degree in range(max_degree+1):
        if y**(degree+1)>=horizon:return degree
    return None


def factor_terminal(intervals,y,degree,excluded=(),meter=None,max_products=MAX_PRODUCTS):
    meter=meter or P.S.Meter();excluded_primes(excluded);cutoff(y)
    state=P.decode(intervals,meter);horizon=max((r for _,r,_ in state),default=0)
    if type(degree) is not int or not 0<=degree<=4 or y**(degree+1)<horizon:
        raise ValueError('terminal factor-degree hypothesis is unpaid')
    if type(max_products) is not int or not 1<=max_products<=MAX_PRODUCTS:raise ValueError('bounded product work')
    primes=[p for p in primes_through(horizon,meter) if p>y and p not in excluded]
    meter.reserve(32*1024**2+8*P.state_bytes(state)+16*(degree+1)*(len(state)+1)+40*(_LIMIT+1))
    counts=[0]*(degree+1)
    histogram=[array('I',[0])*len(state) for _ in range(degree+1)]
    rights=[r for _,r,_ in state];visited=0
    def visit(value,start,level):
        nonlocal visited
        visited+=1
        if visited>max_products:raise ValueError('prospective distinct-prime product budget')
        counts[level]+=1;meter.charge(1)
        i=bisect_left(rights,value)
        if i<len(state) and state[i][0]<value:histogram[level][i]+=1
        if level==degree:return
        limit=horizon//value
        for k in range(start,len(primes)):
            p=primes[k]
            if p>limit:break
            visit(value*p,k+1,level+1)
    if horizon>=1:visit(1,0,0)
    layers=[]
    for row in histogram:
        poly={}
        for count,(_,_,weight) in zip(row,state):
            if count:
                for token,a in weight.items():
                    new=P.bounded_add(poly.get(token,Q(0)),P.bounded_mul(Q(count),a,meter),meter)
                    if new:poly[token]=new
                    else:poly.pop(token,None)
        layers.append(poly)
    signed={}
    for level,poly in enumerate(layers):P.add_poly(signed,poly,1 if level%2==0 else -1,meter)
    return dict(schema='rough-factor-terminal-v1',cutoff=y,degree=degree,
        excluded_primes=list(excluded),layer_polynomials=[P.OLD.saved(v) for v in layers],
        layer_counts=counts,signed_polynomial=P.OLD.saved(signed))


def route_obstruction(admission):
    """Consume an independently checked method obstruction without rejecting R."""
    if admission.get('status')!='VERIFIED_UNIFORM_COEFFICIENT_OBSTRUCTION' or admission.get('arithmetic_residual_refuted') is not False or not admission.get('uniform_l1_power_bound_obstructed'):
        raise ValueError('matching admitted method-only obstruction')
    return dict(fixed_finite_prime_l1_branch='REJECTED_AS_UNIFORM_BOUND_METHOD',
        signed_candidate='RETAINED_WITH_EXISTING_ARITHMETIC_OBLIGATIONS',
        next_grammar='rough-prime transport plus signed factor-parity terminal kernels',
        coupled_state='terminal_signed_prime_factor_polynomial minus the sum of small-prime rough child states',
        forbidden_shortcuts=['separate absolute bounds on prime and composite layers',
            'child normalization recomputed instead of inherited parent count tokens',
            'rank-one energy equal to the unresolved target presented as a proved improvement'],
        next_proof_requirements=['complete prime roster, strict factor order and all unit/boundary terms',
            'exact signed recombination, including every small-prime child',
            'a uniformly bounded coupled energy and a verified projection to the residual',
            'uniform closure for all generated smaller-child kernels and cutoff parameters'],
        uniform_residual_bound_proved=False,RH_proved=False)


def generate_feedback(results):
    return dict(schema='signed-rough-transport-feedback-v1',jobs=[dict(id=r['id'],aliases=r['aliases'],
        q=r['q'],excluded_primes=sorted(r['prime_schedule']),
        original_construction='construction_'+r['id']+'.json',
        old_dispositions_and_witnesses='input_programs076.json',
        routing=route_obstruction(r['uniform_coefficient_obstruction'])) for r in results],
        cutoff_power_API='rational_cutoff admits arbitrary nonnegative rational gamma under bit/work budgets',
        terminal_degree_cap=4,finite_terminal_identity_is_not_a_uniform_bound=True,
        signed_rough_transport_scientific_search_run=False,
        uniform_residual_bound_proved=False,RH_proved=False)

"""Exact interval prime-fold search and kernel-derived uniform obstructions.

No Mobius values enter the construction objective. Finite l1 certificates
and obstructions to that certificate are distinct from signed bounds.
"""
from bisect import bisect_right
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from math import isqrt

import mobius_residual_pairing_076 as OLD

S=OLD.C.S
KERNEL=[dict(divisor=d,weight=str(a)) for d,a in [(8,1),(10,-1),(4,-1),(5,1)]]
MAX_HORIZON=4_000_000
MAX_INTERVALS=100_000
MAX_TERMS=200_000
MAX_BITS=100_000


def reserve(meter,amount):
    meter.reserve(amount+getattr(meter,'fold_live_bytes',0)+40*(_PRIME_LIMIT+1))


def polynomial_bytes(poly):
    return 256+sum(512+4*len(t)+(a.numerator.bit_length()+a.denominator.bit_length()+7)//8 for t,a in poly.items())


def state_bytes(state):
    return 256+sum(256+polynomial_bytes(w) for _,_,w in state)


def bounded_add(a,b,meter):
    if not a:return b
    if not b:return a
    if a==-b:return Q(0)
    if max(a.numerator.bit_length()+b.denominator.bit_length(),b.numerator.bit_length()+a.denominator.bit_length())+1>MAX_BITS or a.denominator.bit_length()+b.denominator.bit_length()>MAX_BITS:
        raise ValueError('prospective rational addition bit gate')
    meter.charge(1+(a.numerator.bit_length()+a.denominator.bit_length()+b.numerator.bit_length()+b.denominator.bit_length())//64)
    return a+b


def bounded_mul(a,b,meter):
    if a.numerator.bit_length()+b.numerator.bit_length()>MAX_BITS or a.denominator.bit_length()+b.denominator.bit_length()>MAX_BITS:
        raise ValueError('prospective rational multiplication bit gate')
    meter.charge(1+(a.numerator.bit_length()+a.denominator.bit_length()+b.numerator.bit_length()+b.denominator.bit_length())//64)
    return a*b


def add_poly(target,value,sign,meter):
    for token,a in value.items():
        new=bounded_add(target.get(token,Q(0)),a if sign==1 else -a,meter)
        if new:target[token]=new
        else:target.pop(token,None)


def decode(intervals,meter=None):
    meter=meter or S.Meter()
    if type(intervals) is not list or len(intervals)>MAX_INTERVALS:
        raise ValueError('bounded interval list')
    terms=sum(len(x.get('weight',{})) for x in intervals if type(x) is dict)
    if terms>MAX_TERMS:raise ValueError('interval term budget')
    reserve(meter,8*1024**2+8192*(len(intervals)+terms+1))
    state=[];previous=0
    for row in intervals:
        if type(row) is not dict or set(row)!={'left','right','weight'}:raise ValueError('interval schema')
        left,right=row['left'],row['right']
        if type(left) is not int or type(right) is not int or not previous<=left<right<=MAX_HORIZON:
            raise ValueError('ordered disjoint finite intervals')
        weight=OLD.poly(row['weight'])
        if not weight:raise ValueError('omit zero intervals')
        state.append((left,right,weight));previous=right
    return state


def encode(state):
    return [dict(left=left,right=right,weight=OLD.saved(weight)) for left,right,weight in state]


def assemble(events,meter):
    active={};state=[];previous=1;output_bytes=256
    event_bytes=256+sum(256+polynomial_bytes(w) for w in events.values())
    for endpoint in sorted(events):
        if endpoint>previous and active:
            if state and state[-1][1]==previous-1 and state[-1][2]==active:
                state[-1]=(state[-1][0],endpoint-1,state[-1][2])
            else:
                output_bytes+=256+polynomial_bytes(active)
                reserve(meter,2*event_bytes+2*output_bytes+2*polynomial_bytes(active))
                state.append((previous-1,endpoint-1,active.copy()))
        add_poly(active,events[endpoint],1,meter);previous=endpoint
    if active:raise ArithmeticError('unpaid terminal coefficient')
    if len(state)>MAX_INTERVALS or sum(len(w) for _,_,w in state)>MAX_TERMS:
        raise ValueError('output interval term budget')
    meter.charge(sum(len(w) for w in events.values())+len(events))
    return state


def fold_state(state,p,meter=None):
    meter=meter or S.Meter()
    if not OLD.prime(p):raise ValueError('bounded actual prime')
    reserve(meter,8*1024**2+8*state_bytes(state))
    events={}
    for left,right,weight in state:
        for l,r,sign in ((left,right,1),(left//p,right//p,-1)):
            if l<r:
                add_poly(events.setdefault(l+1,{}),weight,sign,meter)
                add_poly(events.setdefault(r+1,{}),weight,-sign,meter)
    return assemble(events,meter)


def fold_intervals(intervals,p,prior_primes=(),meter=None):
    meter=meter or S.Meter()
    admit_primes(prior_primes)
    if p in prior_primes:raise ValueError('distinct fold primes')
    return encode(fold_state(decode(intervals,meter),p,meter))


def admit_primes(primes):
    if type(primes) not in (list,tuple) or len(primes)>10 or len(set(primes))!=len(primes) or any(not OLD.prime(p) for p in primes):
        raise ValueError('at most ten distinct bounded primes')


@lru_cache(maxsize=4096)
def signed_divisors(primes,horizon):
    admit_primes(primes)
    values=[(1,1)]
    for p in primes:
        values += [(d*p,-sign) for d,sign in values if d<=horizon//p]
    return tuple(sorted(values))


def count_coprime(left,right,divisors):
    return sum(sign*(right//d-left//d) for d,sign in divisors)


def bound_state(state,token_intervals,primes=(),meter=None):
    meter=meter or S.Meter();admit_primes(primes)
    reserve(meter,8*1024**2+8*state_bytes(state))
    tokens=OLD.intervals_for_tokens(token_intervals)
    horizon=max((r for _,r,_ in state),default=0)
    divisors=signed_divisors(tuple(sorted(primes)),horizon)
    lower=upper=Q(0);bounds={};support=0
    for left,right,weight in state:
        count=count_coprime(left,right,divisors)
        if not 0<=count<=right-left:raise ArithmeticError('complete coprime count')
        if not count:continue
        support+=count;key=tuple(sorted(weight.items()))
        if key not in bounds:
            lo=hi=Q(0)
            for token,a in key:
                if token not in tokens:raise ValueError('missing token enclosure')
                x,y=bounded_mul(a,tokens[token][0],meter),bounded_mul(a,tokens[token][1],meter)
                lo=bounded_add(lo,min(x,y),meter);hi=bounded_add(hi,max(x,y),meter)
            bounds[key]=(Q(0) if lo<=0<=hi else min(abs(lo),abs(hi)),max(abs(lo),abs(hi)))
        a,b=bounds[key]
        lower=bounded_add(lower,bounded_mul(Q(count),a,meter),meter)
        upper=bounded_add(upper,bounded_mul(Q(count),b,meter),meter)
    meter.charge(len(state)*(len(divisors)+10)+10*sum(len(w) for _,_,w in state))
    return dict(lower=str(lower),upper=str(upper),coprime_support=support,intervals=len(state))


def bound_intervals(intervals,token_intervals,primes=(),meter=None):
    meter=meter or S.Meter()
    return bound_state(decode(intervals,meter),token_intervals,primes,meter)


_PRIME_LIMIT=1
_PRIMES=[]


def prime_groups(row,spec,meter=None):
    """Only prime membership; do not compute or consult mu for construction."""
    global _PRIME_LIMIT,_PRIMES
    meter=meter or S.Meter()
    theta,_=S.parse_spec(spec)
    u=row['u'];X=u//4
    cuts=[S.B.floor_power(X,t) for t in theta]
    if row['X']!=X or row['cuts']!=cuts:raise ValueError('matching exact source cutoffs')
    limit=cuts[-1]
    if not 0<=limit<=MAX_HORIZON:raise ValueError('bounded prime horizon')
    reserve(meter,80*(limit+1)+8192*len(theta))
    if limit>_PRIME_LIMIT:
        sieve=bytearray(b'\x01')*(limit+1)
        sieve[:2]=b'\x00\x00'
        for p in range(2,isqrt(limit)+1):
            if sieve[p]:sieve[p*p:limit+1:p]=b'\x00'*((limit-p*p)//p+1)
        _PRIMES=[p for p in range(2,limit+1) if sieve[p]];_PRIME_LIMIT=limit
        meter.charge(20*(limit+1))
    groups=[]
    for i,(lo,hi) in enumerate(zip(cuts,cuts[1:])):
        group=dict(Counter(u//p for p in _PRIMES[bisect_right(_PRIMES,lo):bisect_right(_PRIMES,hi)]))
        if sum(group.values())!=row['counts'][i]:raise ValueError('saved actual prime count differs')
        groups.append(group)
        meter.charge(8*sum(group.values())+len(group))
    return groups


def compile_row(program,row,meter=None):
    meter=meter or S.Meter()
    coefficients=list(map(S.B.rational,program['operator']))
    if sum(a.numerator.bit_length()+a.denominator.bit_length() for a in coefficients)>MAX_BITS//4:
        raise ValueError('compiled coefficient combination bit budget')
    groups=prime_groups(row,program['spec'],meter)
    compiled=OLD.residual_components(program,row,groups)
    intervals=OLD.stencil_intervals(compiled['components'],meter)
    return dict(u=row['u'],prime_groups=groups,compiled=compiled,intervals=intervals)


def kernel_bands(kernel,child_min_divisor):
    if type(child_min_divisor) is not int or child_min_divisor<2:raise ValueError('strictly smaller children')
    if type(kernel) is not list or not 1<=len(kernel)<=64:raise ValueError('bounded prefix kernel')
    parsed=[]
    for term in kernel:
        if type(term) is not dict or set(term)!={'divisor','weight'} or type(term['divisor']) is not int or not 1<=term['divisor']<=100000:
            raise ValueError('prefix kernel schema')
        parsed.append((Q(1,term['divisor']),S.B.rational(term['weight'])))
    horizon=max(x for x,_ in parsed)
    breaks=sorted({Q(0),horizon/2,horizon/child_min_divisor}|{x for x,_ in parsed})
    bands=[]
    for lo,hi in zip(breaks,breaks[1:]):
        value=sum((a for x,a in parsed if x>=hi),Q(0))
        if value and lo>=max(horizon/child_min_divisor,horizon/2):
            bands.append((lo,hi,value))
    return bands


def uniform_obstruction(kernel,child_min_divisor,primes,q):
    """Discover a protected kernel band and its exact uniform price barrier."""
    admit_primes(primes);q=S.B.rational(q)
    if not 1<=q<2:raise ValueError('subquadratic squared coefficient target')
    bands=kernel_bands(kernel,child_min_divisor)
    if not bands:return dict(status='NO_KERNEL_BARRIER_FOUND',arithmetic_residual_refuted=False,RH_proved=False)
    lo,hi,c=max(bands,key=lambda x:(abs(x[2])*(x[1]-x[0]),x))
    delta=Q(1)
    for p in primes:delta*=Q(p-1,p)
    A=abs(c)*delta*(hi-lo);E=abs(c)*(1<<len(primes))
    threshold=(2*E/A).__ceil__()
    return dict(lower=str(lo),upper=str(hi),coefficient=str(c),delta=str(delta),
        A=str(A),E=str(E),threshold_u=threshold,q=str(q))


def search_schedules(compiled_rows,q,primes=(2,3,5,7,11,13),depth=4,width=3,meter=None):
    meter=meter or S.Meter();admit_primes(primes);q=S.B.rational(q)
    if not compiled_rows or type(depth) is not int or not 0<=depth<=min(8,len(primes)) or type(width) is not int or not 1<=width<=8:
        raise ValueError('bounded nonempty construction search')
    states=[decode(row['intervals'],meter) for row in compiled_rows]
    input_bytes=8*1024**2+8*sum(state_bytes(s) for s in states)
    tokens=[row['compiled']['token_intervals'] for row in compiled_rows]
    normal=[S.B.power_bounds(row['u'],q,20)[0] for row in compiled_rows]
    def evaluate(ss,schedule):
        bounds=[bound_state(state,t,schedule,meter) for state,t in zip(ss,tokens)]
        return max(Q(b['upper'])**2/n for b,n in zip(bounds,normal)),bounds
    initial,initial_bounds=evaluate(states,())
    beam=[((),states,initial,initial_bounds)]
    proposals=[]
    for level in range(depth):
        best=[];seen=set()
        for schedule,before,old_score,old_bounds in beam:
            for p in primes:
                if p in schedule:continue
                canonical=tuple(sorted(schedule+(p,)))
                if canonical in seen:continue
                seen.add(canonical)
                after=[]
                retained=input_bytes+2*sum(state_bytes(s) for _,ss,_,_ in beam+best for s in ss)
                for state in before:
                    meter.fold_live_bytes=retained+2*sum(state_bytes(s) for s in after)
                    reserve(meter,8*state_bytes(state))
                    after.append(fold_state(state,p,meter))
                meter.fold_live_bytes=retained+2*sum(state_bytes(s) for s in after)
                new=schedule+(p,);score,bounds=evaluate(after,new)
                if any(Q(a['upper'])>Q(b['upper']) for a,b in zip(bounds,old_bounds)):
                    raise ArithmeticError('paid coefficient triangle price increased')
                proposals.append(dict(primes=list(new),normalized_squared_upper=str(score),intervals=sum(len(s) for s in after)))
                best.append((new,after,score,bounds))
                best.sort(key=lambda x:(x[2],sum(len(s) for s in x[1]),tuple(sorted(x[0]))))
                del best[width:]
        if not best:break
        beam=best
    meter.fold_live_bytes=0
    schedule,after,score,bounds=min(beam,key=lambda x:(x[2],sum(len(s) for s in x[1]),tuple(sorted(x[0]))))
    return dict(prime_schedule=list(schedule),initial_normalized_squared_upper=str(initial),
        normalized_squared_upper=str(score),initial_bounds=initial_bounds,bounds=bounds,
        proposals=proposals,final_intervals=[encode(state) for state in after],
        finite_coefficient_bound_only=True,mobius_values_used_for_selection=False,
        uniform_residual_proved=False,RH_proved=False)

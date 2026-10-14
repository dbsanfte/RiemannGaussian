"""Synthesize weighted shared-sign energies and frustrated parity cycles.

The resulting inequalities are exact and finite. Their all-scale cost is
a separate theorem obligation, never inferred from a finite price decrease.
"""
from fractions import Fraction as Q
from math import isqrt

from prime_transfer_algebra_058 import Meter
from mobius_quadratic_contraction_064 import prime_masks

WEIGHT_POWERS=('-1/2','0','1/3','1/2','3/5','2/3','7/8','1','3/2')
MAX_POWER_BITS=1_000_000
MAX_SQUARE_PAIRS=100000
MAX_ENERGY_TERMS=60000


def _q(text):
    if type(text) is not str or not 1<=len(text)<=2500:raise ValueError('canonical rational exponent')
    value=Q(text)
    if str(value)!=text or max(abs(value.numerator).bit_length(),value.denominator.bit_length())>4096:
        raise ValueError('canonical rational exponent capacity')
    return value


def _export(value):
    if max(abs(value.numerator).bit_length(),value.denominator.bit_length())>4096:
        raise OverflowError('certificate rational output capacity')
    return str(value)


def dyadic_power_weight(value,exponent,precision=4,meter=None):
    """Round value**exponent UP to a bounded binary significand, exactly.

    Any rational exponent is allowed within the integer-power work cap.
    Using bounded significands avoids introducing a new large odd divisor
    for every row when the energies subsequently divide by these weights.
    """
    meter=Meter() if meter is None else meter
    if not isinstance(value,Q) or value<=0:raise ValueError('positive exact row scale')
    if type(precision) is not int or not 0<=precision<=12:raise ValueError('bounded binary significand precision')
    t=_q(exponent)
    if t<0:value=1/value;t=-t
    a,b=t.numerator,t.denominator
    if not a:meter.charge();return Q(1)
    estimate=a*(value.numerator.bit_length()+value.denominator.bit_length())+b*(precision+2)
    if estimate>MAX_POWER_BITS:raise OverflowError('rational-power work capacity')
    A=pow(value.numerator,a);D=pow(value.denominator,a);meter.charge(estimate)
    e=A.bit_length()-D.bit_length()
    below=A<(D<<e) if e>=0 else (A<<(-e))<D
    if below:e-=1
    k=e//b;unit_shift=k-precision
    shift=-unit_shift*b
    if max(A.bit_length()+max(shift,0),D.bit_length()+max(-shift,0))>MAX_POWER_BITS:
        raise OverflowError('scaled rational-power work capacity')
    numerator=A<<max(shift,0);denominator=D<<max(-shift,0)
    low=(1<<precision)-1;high=1<<(precision+1)
    while high-low>1:
        mid=(low+high)//2;meter.charge(estimate+abs(shift)+32)
        if pow(mid,b)*denominator>=numerator:high=mid
        else:low=mid
    answer=Q(high*(1<<unit_shift)) if unit_shift>=0 else Q(high,1<<(-unit_shift))
    _export(answer);return answer


def ceil_sqrt(value,denominator=4096,meter=None):
    meter=Meter() if meter is None else meter
    if value<0 or type(denominator) is not int or not 1<=denominator<=2**20:
        raise ValueError('nonnegative root and finite rational rounding grid')
    n=(value.numerator*denominator**2+value.denominator-1)//value.denominator
    r=isqrt(n)
    if r*r<n:r+=1
    meter.charge(32+8*n.bit_length());answer=Q(r,denominator);_export(answer);return answer


def compile_parent(parent,meter=None):
    meter=Meter() if meter is None else meter
    H,K=parent['H'],parent['K'];B=max(H,K)
    primes,_=prime_masks(B,meter);positions={p:i for i,p in enumerate(primes)}
    masks={1:0};integers={0:1};conditioned=set(parent['conditioned_primes'])
    def mask(index):
        if index in masks:return masks[index]
        n=index;out=0
        for p in primes:
            if p*p>n:break
            meter.charge(8)
            if n%p==0:
                n//=p
                if n%p==0 or p in conditioned:raise ValueError('unconditioned squarefree parent character')
                out|=1<<positions[p]
        if n>1:
            if n not in positions or n in conditioned:raise ValueError('remaining parent prime within query radius')
            out|=1<<positions[n]
        masks[index]=out;integers[out]=index;return out
    all_rows=[];pair_count=0
    for endpoint in parent['endpoints']:
        rows=[]
        for row in endpoint['rows']:
            terms={mask(t['index']):Q(t['coefficient']) for t in row['terms']}
            pair_count+=len(terms)*(len(terms)+1)//2;rows.append(terms)
        all_rows.append(rows)
    if pair_count>MAX_SQUARE_PAIRS:raise OverflowError('prospective shared energy expansion pairs')
    meter.reserve(16*1024**2+2048*pair_count)
    squares=[];costs=[]
    for rows in all_rows:
        endpoint=[];prices=[]
        for row in rows:
            square={};items=list(row.items())
            for i,(a,u) in enumerate(items):
                for b,v in items[i:]:
                    key=a^b;term=u*v*(1 if a==b else 2)
                    square[key]=square.get(key,Q(0))+term;meter.charge(40)
            endpoint.append({key:q for key,q in square.items() if q})
            prices.append(sum(map(abs,row.values()),Q(0)))
        squares.append(endpoint);costs.append(prices)
    return {'primes':primes,'rows':all_rows,'squares':squares,'row_l1':costs,
        'integer_keys':integers,'expanded_square_pairs':pair_count}


def integer_key(mask,compiled,meter):
    known=compiled['integer_keys']
    if mask in known:return known[mask]
    n=1;bits=mask
    while bits:
        bit=bits&-bits;n*=compiled['primes'][bit.bit_length()-1];bits-=bit;meter.charge(8)
    known[mask]=n;return n


def weighted_energy(squares,weights,meter):
    energy={}
    for square,w in zip(squares,weights):
        if not square:
            if w:raise ValueError('empty row has zero weight')
            continue
        if w<=0:raise ValueError('strict positive energy weight')
        for key,q in square.items():
            energy[key]=energy.get(key,Q(0))+q/w;meter.charge(32)
            if len(energy)>MAX_ENERGY_TERMS:raise OverflowError('weighted energy term capacity')
    return {key:q for key,q in energy.items() if q}


def pack_cycles(energy,max_cycles=64,meter=None):
    """Greedily find inconsistent preferred character signs by GF(2) reduction.

    A packed cycle uses a capacity shared by every one of its coefficients.
    Rebuilding the basis after each cycle permits new dependencies; all
    steps are deterministic and the independent checker verifies the pack.
    """
    meter=Meter() if meter is None else meter
    if type(max_cycles) is not int or not 0<=max_cycles<=4096:raise ValueError('finite cycle search budget')
    capacity={key:abs(q) for key,q in energy.items() if key};cycles=[]
    for _ in range(max_cycles):
        order=sorted((key for key in capacity if capacity[key]),key=lambda key:(-capacity[key],key.bit_count(),key))
        meter.charge(32*len(order));basis={};found=None
        for key in order:
            reduced=key;support={key}
            while reduced:
                pivot=reduced.bit_length()-1;meter.charge(16+len(support))
                if pivot not in basis:basis[pivot]=(reduced,support.copy());break
                other,origin=basis[pivot];reduced^=other;support.symmetric_difference_update(origin)
            if not reduced and sum(energy[k]<0 for k in support)%2:
                if len(support)<3:raise ArithmeticError('distinct nonconstant parity cycle')
                amount=min(capacity[k] for k in support)
                found={'masks':sorted(support),'mass':amount}
                for k in support:capacity[k]-=amount;meter.charge(16)
                break
        if found is None:break
        cycles.append(found)
    return cycles


def construct(parent,compiled,weights,max_cycles=64,meter=None):
    meter=Meter() if meter is None else meter;endpoints=[];raw_bounds=[]
    for e,pe in enumerate(parent['endpoints']):
        energy=weighted_energy(compiled['squares'][e],weights[e],meter)
        cycles=pack_cycles(energy,max_cycles,meter)
        mass=sum(weights[e],Q(0));l1=sum(map(abs,energy.values()),Q(0))
        if energy.get(0,Q(0))<0:raise ArithmeticError('energy constant must be nonnegative')
        upper=l1-2*sum((c['mass'] for c in cycles),Q(0))
        if upper<0:raise ArithmeticError('cycle packing cannot make SOS upper negative')
        vb=ceil_sqrt(mass*upper,meter=meter);raw_bounds.append(_export(ceil_sqrt(mass*l1,meter=meter)))
        terms=sorted((integer_key(key,compiled,meter),q) for key,q in energy.items())
        endpoints.append({'ratio':pe['ratio'],'weights':list(map(_export,weights[e])),
            'energy_terms':[{'index':n,'coefficient':_export(q)} for n,q in terms],
            'cycles':[{'indices':sorted(integer_key(k,compiled,meter) for k in c['masks']),
                'mass':_export(c['mass'])} for c in cycles],
            'weight_mass':_export(mass),'energy_l1':_export(l1),'energy_upper':_export(upper),'variation_bound':_export(vb)})
    certificate={'schema':'mobius-walsh-energy-bound-v1',**{k:parent[k] for k in ('N','y','H','K','conditioned_primes')},
        'endpoints':endpoints,'budget':str(max(Q(e['variation_bound']) for e in endpoints))}
    return {'certificate':certificate,'uncycled_endpoint_variation_bounds':raw_bounds,
        'cycle_counts':[len(e['cycles']) for e in endpoints],
        'uniform_growth_proved':False}


def discover(parent,meter=None,powers=None,precision=4,max_cycles=64):
    meter=Meter() if meter is None else meter
    powers=WEIGHT_POWERS if powers is None else powers
    if type(powers) not in (tuple,list) or not 1<=len(powers)<=64:raise ValueError('finite rational weight policy budget')
    compiled=compile_parent(parent,meter);results=[];seen={}
    for power in powers:
        _q(power)
        weights=[[dyadic_power_weight(v,power,precision,meter) if v else Q(0) for v in row] for row in compiled['row_l1']]
        key=tuple(tuple(row) for row in weights)
        if key in seen:results[seen[key]]['weight_powers'].append(power);continue
        candidate=construct(parent,compiled,weights,max_cycles,meter)
        candidate.update({'weight_powers':[power],'weight_binary_precision':precision})
        seen[key]=len(results);results.append(candidate)
    selected=min(range(len(results)),key=lambda i:(Q(results[i]['certificate']['budget']),i))
    return {'N':parent['N'],'y':parent['y'],'H':parent['H'],'K':parent['K'],
        'candidates':results,'selected_index':selected,'selected_budget':results[selected]['certificate']['budget'],
        'parent_coefficient_budget':parent['budget'],'expanded_square_pairs_reused_across_policies':compiled['expanded_square_pairs'],
        'uniform_growth_proved':False,'original_source_binding_requires_same_064_parent':True}

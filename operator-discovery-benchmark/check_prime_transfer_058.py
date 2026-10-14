"""Independent universal finite prime-transfer and pointwise-order admission.

Exact valuation-sector polynomials; inclusive unit and real scale pullbacks.
No producer imports, saved source authority or signed bound promotion.
"""
from fractions import Fraction as Q
from itertools import product
from math import isqrt,comb
from check_fractional_prime_rh_bridge_052 import Meter,_rational,_expect

MAX_PRIMES=8
MAX_PRIME=1_000_000
MAX_ATOMS=2048
MAX_EXPONENT=64
MAX_CASES=100000
MAX_ROWS=2_000_000
MAX_INTEGER_BITS=4096
MAX_INTERMEDIATE_BITS=16384
MAX_ESTIMATED_TABLE_BYTES=4*1024**3
ROW_BYTES_UPPER=512+2*(MAX_INTERMEDIATE_BITS//8)


def _table_capacity(rows):
    if rows>MAX_ROWS or rows*ROW_BYTES_UPPER>MAX_ESTIMATED_TABLE_BYTES:
        raise MemoryError('058 prospective sparse table capacity')


def _keys(value,keys):
    if type(value) is not dict or set(value)!=set(keys):raise ValueError('exact058 schema')


def _guard(value,meter):
    if type(value) is not Q:value=Q(value)
    bits=max(abs(value.numerator).bit_length(),value.denominator.bit_length())
    meter.charge(1+bits)
    if bits>MAX_INTERMEDIATE_BITS:raise OverflowError('058 exact rational intermediate capacity')
    return value


def _universe(values,meter):
    if type(values) is not list or len(values)>MAX_PRIMES:raise ValueError('bounded actual prime universe')
    previous=1
    for p in values:
        if type(p) is not int or not previous<p<=MAX_PRIME:raise ValueError('sorted distinct actual primes')
        for d in range(2,isqrt(p)+1):
            meter.charge(4)
            if p%d==0:raise ValueError('actual registered prime required')
        previous=p
    meter.charge(1+len(values));return tuple(values)


def _factor_integer(value,universe,meter):
    if type(value) is not int or value<1 or value.bit_length()>MAX_INTEGER_BITS:
        raise ValueError('bounded positive integer divisor/attenuation')
    rest=value;exponents=[]
    for p in universe:
        exponent=0
        while rest%p==0:
            rest//=p;exponent+=1;meter.charge(1+rest.bit_length())
            if exponent>MAX_EXPONENT:raise OverflowError('058 registered prime exponent capacity')
        exponents.append(exponent)
    if rest!=1:raise ValueError('divisor and attenuation must be supported on universe')
    meter.charge(1+value.bit_length());return tuple(exponents)


def _parse(request,meter,current_only=False):
    _keys(request,('universe','atoms','coefficients'))
    universe=_universe(request['universe'],meter)
    atoms=request['atoms'];coefficients=request['coefficients']
    if type(atoms) is not list or not 1<=len(atoms)<=MAX_ATOMS:
        raise ValueError('bounded nonempty complete atom list')
    if type(coefficients) is not list or len(coefficients)!=len(atoms):raise ValueError('aligned exact signed coefficient vector')
    parsed=[];atom_keys=set();caps=[0]*len(universe)
    for atom,text in zip(atoms,coefficients):
        _keys(atom,('primes','divisor','attenuation'))
        primes=atom['primes']
        if type(primes) is not list or any(type(p) is not int for p in primes) or primes!=sorted(set(primes)) or not set(primes)<=set(universe):
            raise ValueError('canonical registered-prime subset')
        divisors=_factor_integer(atom['divisor'],universe,meter)
        attenuation=_factor_integer(atom['attenuation'],universe,meter)
        key=(tuple(primes),divisors,attenuation)
        if key in atom_keys:raise ValueError('distinct literal atom columns required')
        atom_keys.add(key)
        coefficient=_rational(text,meter)
        if current_only and atom['divisor']!=1:raise ValueError('current-only pointwise source order requires everydivisor1')
        for i,e in enumerate(divisors):caps[i]=max(caps[i],e)
        parsed.append((frozenset(primes),divisors,attenuation,coefficient))
    cases=1
    for cap in caps:
        cases*=cap+2
        if cases>MAX_CASES:raise OverflowError('058 complete valuation-sector capacity')
    return universe,tuple(parsed),tuple(caps),cases


def _add(poly,exponent,coefficient,meter):
    value=_guard(poly.get(exponent,Q(0))+coefficient,meter)
    if value:poly[exponent]=value
    else:poly.pop(exponent,None)
    _table_capacity(len(poly))


def _atom_polynomial(attenuation,active,meter):
    rows={attenuation:Q(1)}
    for i in active:
        next_rows=dict(rows)
        for exponent,c in rows.items():
            shifted=list(exponent);shifted[i]+=1
            _add(next_rows,tuple(shifted),-c,meter)
        rows=next_rows
    return rows


def _case(universe,parsed,valuation,meter,cache,current_only=False):
    total={}
    for primes,divisors,attenuation,coefficient in parsed:
        meter.charge(1+len(universe))
        if not coefficient or current_only and any(divisors):continue
        if any(v<d for v,d in zip(valuation,divisors)):continue
        active=tuple(i for i,p in enumerate(universe) if p in primes or valuation[i]>divisors[i])
        key=(attenuation,active)
        if key not in cache:
            atom_poly=_atom_polynomial(attenuation,active,meter)
            used=cache.get('_row_count',0)+len(atom_poly)
            _table_capacity(used)
            cache[key]=atom_poly;cache['_row_count']=used
        rows=cache[key]
        for exponent,c in rows.items():_add(total,exponent,_guard(coefficient*c,meter),meter)
    return total


def _rows(poly):
    return [{'powers':list(exponent),'coefficient':str(value)} for exponent,value in sorted(poly.items())]


def verify_identity(request,meter=None):
    meter=Meter(cap=2_000_000_000,seconds=7200) if meter is None else meter
    universe,parsed,caps,cases=_parse(request,meter)
    cache={};seen=0
    current=_case(universe,parsed,(0,)*len(universe),meter,cache,True)
    for valuation in product(*(range(cap+2) for cap in caps)):
        poly=_case(universe,parsed,valuation,meter,cache)
        seen+=1
        if poly:
            first=next(iter(sorted(poly.items())))
            raise ValueError('universal identity fails valuation '+repr(valuation)+' at monomial '+repr((first[0],str(first[1]))))
    if seen!=cases:raise ArithmeticError('complete valuation coverage')
    return {'verified':True,'request':request,'universal_identity_proved':True,
        'domain':'everypositive realx andt; complete registered prime valuations',
        'valuation_caps':[cap+1 for cap in caps],'valuation_cases_checked':cases,
        'last_case_semantics':'v=cap=max_divisor_exponent+1 represents everylargervaluation',
        'current_zero_on_unregistered_sector':not bool(current),
        'current_unregistered_sector_polynomial':_rows(current),
        'inclusive_unit_retained':True,
        'unit_identity':'H_S(x,t)=h_S(x,t)+G_S(t)*v_x(1)',
        'unit_is_W':False,'outside_prime_factor_common':True,
        'signed_bound_proved':False,'free_prime_sector_bound_proved':False,
        'uniform_target_bound_proved':False,'RH_proved':False,'RH_refuted':False,
        'producer_imported':False,'source_arrays_read':False}


def _to_y(poly,meter):
    """Independent binomial substitution z_i=1-y_i, keeping signed terms."""
    result={}
    for exponent,c in poly.items():
        count=1
        for power in exponent:
            count*=power+1
            _table_capacity(count)
        meter.charge(count)
        for y_exponent in product(*(range(power+1) for power in exponent)):
            factor=c
            for power,j in zip(exponent,y_exponent):factor=_guard(factor*((-1)**j)*comb(power,j),meter)
            _add(result,y_exponent,factor,meter)
    return result


def _order_certificate(request,meter):
    universe,parsed,caps,count=_parse(request,meter,True)
    cache={};cases=[];global_order=None;global_envelope=Q(0);total_rows=0
    free_zero=False
    for presence in product((0,1),repeat=len(universe)):
        z_poly=_case(universe,parsed,presence,meter,cache)
        y_poly=_to_y(z_poly,meter)
        total_rows+=len(y_poly)
        _table_capacity(total_rows)
        order=min(map(sum,y_poly)) if y_poly else None
        envelope=Q(0)
        for exponent,c in y_poly.items():
            factor=abs(c)
            for p,e in zip(universe,exponent):factor=_guard(factor*(p**e),meter)
            envelope=_guard(envelope+factor,meter)
        if order is not None:
            global_order=order if global_order is None else min(global_order,order)
        global_envelope=max(global_envelope,envelope)
        if not any(presence):free_zero=not bool(y_poly)
        cases.append({'presence':list(presence),'terms':_rows(y_poly),
            'order':order,'envelope':str(envelope)})
    if len(cases)!=count:raise ArithmeticError('all current source presence cases required')
    certificate={'schema':'prime-transfer-source-order-v1','request':request,
        'cases':cases,'order':global_order,'envelope':str(global_envelope),
        'zero_source':global_order is None,
        'scope':{'N_minimum':2,'N_type':'integer','t_lower_exclusive':'0','t_upper':'1'},
        'whole_bound_proved':False,'RH_proved':False}
    return certificate,free_zero,parsed


def verify_source_order(request,certificate,meter=None):
    meter=Meter(cap=2_000_000_000,seconds=7200) if meter is None else meter
    expected,free_zero,_=_order_certificate(request,meter)
    _expect(certificate,expected);meter.charge(100+len(repr(expected)))
    return {'verified':True,'request':request,'order':expected['order'],
        'envelope':expected['envelope'],'zero_source':expected['zero_source'],
        'current_zero_on_unregistered_sector':free_zero,
        'pointwise_polynomial_bound_proved':True,
        'bound':'|registered-sector pointwise polynomial|<=envelope*t^order for0<t<=1',
        'all_presence_cases_retained':True,'signed_whole_target_bound_proved':False,
        'free_prime_sector_target_bound_proved':False,
        'RH_proved':False,'RH_refuted':False,'source_arrays_read':False,'producer_imported':False}


def verify_endpoint_bound(request,certificate,meter=None):
    meter=Meter(cap=2_000_000_000,seconds=7200) if meter is None else meter
    _keys(request,('operator','alpha','gamma','tau'))
    alpha=_rational(request['alpha'],meter);gamma=_rational(request['gamma'],meter);tau=_rational(request['tau'],meter)
    if not 0<alpha<1 or gamma<=0 or not 0<tau<1:raise ValueError('strict fractional source/end-cutoff domain')
    order_certificate,free_zero,parsed=_order_certificate(request['operator'],meter)
    k=order_certificate['order'];B=Q(order_certificate['envelope'])
    if k is None or not k>alpha:raise ValueError('nonzero current source requires pointwise order strictlyabovealpha')
    L=Q(0)
    for _,_,_,coefficient in parsed:L=_guard(L+abs(coefficient),meter)
    micro_constant=_guard(12*B/(k-alpha),meter)
    micro_power=_guard(1-gamma*(k-alpha),meter)
    tail_constant=_guard(16*L/(tau*tau*(1-tau)),meter)
    expected={'schema':'prime-transfer-endpoints-v1','request':request,
        'source_order':order_certificate,
        'microscopic':{'C':str(micro_constant),'N_power':str(micro_power)},
        'tail':{'C':str(tail_constant),'N_power':str(1-tau)},
        'middle_status':'OPEN','uniform_full_source_bound_proved':False,'RH_proved':False}
    _expect(certificate,expected);meter.charge(100+len(repr(expected)))
    return {'verified':True,'request':request,'microscopic':expected['microscopic'],
        'tail':expected['tail'],'pointwise_order':k,'coefficient_L1':str(L),
        'current_zero_on_unregistered_sector':free_zero,
        'both_end_region_bounds_proved':True,
        'domain':'everyintegerN>=2; epsilon=min(tau,N^-gamma); exactfullsource',
        'middle_status':'OPEN','uniform_full_source_bound_proved':False,
        'RH_proved':False,'RH_refuted':False,'source_arrays_read':False,'producer_imported':False}

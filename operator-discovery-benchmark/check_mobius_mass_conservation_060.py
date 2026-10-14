"""Independent periodic signed profile mass and final-copy-leftover rules.

No discovery producer, scientific source table, or numerical kernel is used.
Periodic finite replay proves an all-real floor identity. Only final unmatched
copy cost is paid; previously paired costs and full target growth remain OPEN.
"""
from fractions import Fraction as Q
from math import isqrt,prod
from check_fractional_prime_rh_bridge_052 import Meter,_rational,_fields,_expect

MAX_PERIOD=4096
MAX_INTERMEDIATE_BITS=32768


def _bounded(value,m):
    bits=max(abs(value.numerator).bit_length(),value.denominator.bit_length())
    m.charge(1+bits)
    if bits>MAX_INTERMEDIATE_BITS:raise OverflowError('mass identity rational intermediate capacity')
    return value


def _prime(p,m):
    if type(p) is not int or not 2<=p<=1_000_000:raise ValueError('bounded actual prime')
    for d in range(2,isqrt(p)+1):
        m.charge(4)
        if p%d==0:raise ValueError('actual prime required')
    m.charge();return p


def _parameters(obj,m):
    _fields(obj,('alpha','gamma','tau','primes','p','q'))
    alpha,gamma,tau=(_rational(obj[k],m) for k in ('alpha','gamma','tau'))
    if not 0<alpha<1 or gamma<=0 or not 0<tau<1:raise ValueError('fixed fractional band gates')
    ps=obj['primes']
    if type(ps) is not list or not 2<=len(ps)<=8:raise ValueError('bounded registered prime mask')
    for p in ps:_prime(p,m)
    if ps!=sorted(set(ps)):raise ValueError('distinct ascending prime mask')
    p,q=obj['p'],obj['q']
    if type(p) is not int or type(q) is not int or p not in ps or q not in ps or p>=q:
        raise ValueError('ordered source primes in mask')
    period=4*p*q
    if period>MAX_PERIOD:raise OverflowError('period replay capacity')
    return alpha,gamma,tau,ps,p,q,period


def _profile_vector(n,p,q,m):
    # v=n/4; each W(v/s) computed solely by integer division.
    a=n//p-3*(n//(2*p))+2*(n//(4*p))
    b=n//q-3*(n//(2*q))+2*(n//(4*q))
    m.charge(20)
    if a not in (-1,0,1) or b not in (-1,0,1):raise ArithmeticError('shell weight range')
    row=[0]*4
    if a or b:
        if not b:row[0]=a
        elif not a:row[1]=-b
        elif a==b:row[2]=a
        else:row[3]=a
    return row


def _identity(cert,m):
    _fields(cert,('schema','parameters','period','profile_coefficients','floor_coefficients'))
    _expect(cert['schema'],'mobius-profile-floor-identity-v1')
    alpha,gamma,tau,ps,p,q,period=_parameters(cert['parameters'],m)
    if type(cert['period']) is not int or cert['period']!=period:raise ValueError('complete joint period')
    xs=cert['profile_coefficients']
    if type(xs) is not list or len(xs)!=4:raise ValueError('P,Q,D,S coefficient coverage')
    xs=[_rational(x,m) for x in xs]
    floors=cert['floor_coefficients']
    if type(floors) is not list or len(floors)>MAX_PERIOD:raise ValueError('bounded divisor rows')
    cs={};last=0
    for row in floors:
        _fields(row,('d','c'));d=row['d'];c=_rational(row['c'],m)
        if type(d) is not int or not last<d<=period or period%d or not c:
            raise ValueError('nonzero canonical coefficients on ascending distinct period divisors')
        cs[d]=c;last=d
    if any(_profile_vector(0,p,q,m)):raise ArithmeticError('profile zero head')
    previous=Q(0)
    for n in range(1,period+1):
        vector=_profile_vector(n,p,q,m)
        current=Q(0)
        for x,v in zip(xs,vector):current=_bounded(current+x*v,m)
        jump=Q(0)
        for d,c in cs.items():
            m.charge(4)
            if n%d==0:jump=_bounded(jump+c,m)
        if _bounded(current-previous,m)!=jump:raise ValueError('a complete period jump fails')
        previous=current
    drift=Q(0);mass=Q(0)
    for d,c in cs.items():
        drift=_bounded(drift+c*(period//d),m)
        mass=_bounded(mass+abs(c),m)
    if previous or drift:raise ValueError('zero period drift required')
    return (alpha,gamma,tau,ps,p,q,period,xs,cs,mass)


def verify_identity(cert,meter=None):
    m=Meter() if meter is None else meter
    alpha,gamma,tau,ps,p,q,period,xs,cs,mass=_identity(cert,m)
    return {'verified':True,'schema':'verified-mobius-profile-floor-identity-v1',
        'parameters':cert['parameters'],'period':period,
        'profile_order':['P','Q','D','S'],'profile_coefficients':[str(x) for x in xs],
        'floor_coefficients':cert['floor_coefficients'],
        'all_period_jumps_checked':period,'zero_head_checked':True,'zero_period_drift_checked':True,
        'floor_identity_proved':True,'floor_identity_domain':'every real v, including all jump endpoints',
        'global_signed_mass_identity':{
            'left':'sum_(d<=4N,gcd(d,M)=1) mu(d)*sum_i x_i*f_i(N/d)',
            'right':'sum_b c_b*Psi_M(4N/b)',
            'Psi_M':'count of positive integers <=x with all prime divisors registered in M; unit included',
            'method':'mu_M*One=indicator_M_smooth; finite complete convolution',
            'domain':'every integer N>=2','proved':True,
            'd1_retained':True,'q_range_exits_retained':True,'zero_extension_horizon':'4N'},
        'signed_mass_upper':{'coefficient':str(mass),'log_degree':len(ps),
            'log_weight':'(1+log2(4N))^log_degree','proved':True},
        'whole_signed_target_bound_proved':False,'paired_cost_bound_proved':False,
        'RH_proved':False,'source_arrays_evaluated':False}


def verify_copy_bound(cert,meter=None):
    m=Meter() if meter is None else meter
    _fields(cert,('schema','identity','weights','magnitude_constant','coefficient','log_degree'))
    _expect(cert['schema'],'mobius-copy-leftover-bound-v1')
    alpha,gamma,tau,ps,p,q,period,xs,cs,mass=_identity(cert['identity'],m)
    weights=cert['weights']
    if type(weights) is not list or len(weights)!=4 or any(type(w) is not int or not 1<=w<=16 for w in weights):
        raise ValueError('four positive bounded integer copy weights')
    if xs!=[Q(w) for w in weights]:raise ValueError('copy weights must equal identity profile coefficients')
    magnitude=_bounded(Q(6*prod(ps))/(len(ps)-alpha),m)
    coefficient=_bounded(magnitude*mass/min(weights),m)
    if _rational(cert['magnitude_constant'],m)!=magnitude or _rational(cert['coefficient'],m)!=coefficient:
        raise ValueError('exact complete copy cost constants')
    if type(cert['log_degree']) is not int or cert['log_degree']!=len(ps):raise ValueError('smooth count logarithmic degree')
    m.charge(100)
    return {'verified':True,'schema':'verified-mobius-copy-leftover-bound-v1',
        'parameters':cert['identity']['parameters'],'weights':weights,
        'magnitude_constant':str(magnitude),'coefficient':str(coefficient),'log_degree':len(ps),
        'log_weight':'(1+log2(4N))^log_degree','domain':'every integer N>=2',
        'copy_definition':'each token of profile i is split into w_i equal signed copies of magnitude m_i/w_i',
        'pairing_requirements':'any legal opposite-sign initial copy pairings, followed by a COMPLETE global opposite-sign residual scan',
        'conservation':'final leftover count equals absolute signed weighted profile mass',
        'leftover_cost_bound_proved':True,'paired_cost_status':'OPEN',
        'whole_signed_target_bound_proved':False,'RH_proved':False,'source_arrays_evaluated':False}

"""Independent finite-cutoff tails and complete signed first jets.

No new producer imports, source arrays, numerical integrals or search calls.
Uniform low-core bounds stay OPEN, including after an exact first-jet zero.
"""
from fractions import Fraction as Q
from math import isqrt
from check_fractional_prime_rh_bridge_052 import Meter,_rational,_expect

MAX_PRIME=2_000_000
MAX_PRODUCT_BITS=256
MAX_FEATURES=64
MAX_INTERMEDIATE_BITS=32768


def _keys(obj,keys):
    if type(obj) is not dict or set(obj)!=set(keys):raise ValueError('exact056 rule schema')


def _guard(value,meter):
    bits=abs(value.numerator).bit_length()+value.denominator.bit_length()
    meter.charge(1+bits)
    if max(abs(value.numerator).bit_length(),value.denominator.bit_length())>MAX_INTERMEDIATE_BITS:
        raise OverflowError('056 rational intermediate resource capacity')
    return value


def _sum(values,meter):
    total=Q(0)
    for value in values:total=_guard(total+value,meter)
    return total


def _primes(primes,meter):
    if type(primes) is not list or len(primes)>12:raise ValueError('bounded canonical prime set')
    previous=1;product=1
    for p in primes:
        if type(p) is not int or not previous<p<=MAX_PRIME:raise ValueError('sorted distinct actual primes')
        for d in range(2,isqrt(p)+1):
            meter.charge()
            if p%d==0:raise ValueError('actual prime required')
        previous=p;product*=p
        if product.bit_length()>MAX_PRODUCT_BITS:raise OverflowError('squarefree source product capacity')
    meter.charge(1+len(primes));return product


def _tail_parameters(request,meter):
    _keys(request,('alpha','primes','tau'))
    alpha=_rational(request['alpha'],meter);tau=_rational(request['tau'],meter)
    if not 0<alpha<1:raise ValueError('strict fractional source exponent')
    if not 0<tau<=256:raise ValueError('positive finite rational cutoff capacity')
    R=_primes(request['primes'],meter)
    return alpha,tau,R


def _tail_shape(primes,tau,meter):
    count=2**len(primes)
    if tau<1:
        # Each exponential has base>=2: the empty-set d1 term iszero
        # because W(N)=0; nonempty sets retain d1 with externalR>=2.
        # 2/(log2)<=4, sum_d<=4N d^-tau<=(4N)^(1-tau)/(1-tau).
        constant=16*count/(tau**2*(1-tau));power=1-tau;log=Q(0)
    elif tau==1:
        constant=Q(12*count);power=Q(0);log=Q(4*count)
    else:
        constant=4*count*tau/(tau-1);power=Q(0);log=Q(0)
    for value in (constant,power,log):_guard(value,meter)
    meter.charge(100)
    return {'N_power':str(power),'constant':str(constant),'log_coefficient':str(log),'logarithm_base':'e'}


def verify_tail_bound(request,certificate,meter=None):
    meter=Meter() if meter is None else meter
    alpha,tau,R=_tail_parameters(request,meter)
    shape=_tail_shape(request['primes'],tau,meter)
    expected={'schema':'prime-insertion-finite-cutoff-tail-v1','request':request,
        'product':R,'integer_N_minimum':2,
        'filter':{'q':2,'coefficients':[2,-3,1],'normalization':'divide_by_alpha'},
        'integrand':'R^-t*sum_(d<=4N,gcd(d,R)=1)mu(d)*d^-t*sum_(e|R)mu(e)*W(N/(d*e))',
        'normalizer':'1/(alpha*I_alpha)','upper_bound':shape,
        'unpaid_core':'0<t<tau','tail_bound_proved':True,
        'complete_target_bound_proved':False,'RH_proved':False}
    _expect(certificate,expected);meter.charge(100+len(repr(expected)))
    return {'verified':True,'request':request,'upper_bound':shape,
        'tail_bound_proved':True,'complete_target_bound_proved':False,
        'RH_proved':False,'RH_refuted':False,'unpaid_core':'0<t<tau',
        'domain':'EVERY integer N>=2; fixed exact rational tau>0',
        'source_values_evaluated':False,'numerical_integral_evaluated':False,
        'source_scope':'ordinary-mu complete coprime divisor/cofactor sum with excluded unit',
        'empty_set_unit_gate':'W(N)=0 only at integer N',
        'nonempty_set_unit_gate':'d1 retained and external R>=2 supplies exponential decay'}


def _jet_parameters(request,meter):
    _keys(request,('features','coefficients'))
    features=request['features'];coefficients=request['coefficients']
    if type(features) is not list or not 1<=len(features)<=MAX_FEATURES:raise ValueError('nonempty bounded source feature list')
    for S in features:_primes(S,meter)
    if len({tuple(S) for S in features})!=len(features):raise ValueError('distinct canonical source features')
    if type(coefficients) is not list or len(coefficients)!=len(features):raise ValueError('complete signed rational mixture')
    a=[_rational(c,meter) for c in coefficients]
    if not any(a):raise ValueError('nontrivial signed mixture')
    primes=sorted({p for S in features for p in S})
    common=_sum(a,meter);exceptions=[]
    for p in primes:
        coefficient=-_sum((c for c,S in zip(a,features) if p in S),meter)
        exceptions.append({'prime':p,'coefficient':str(coefficient),
            'rational_abs_bound':'1' if p==2 else str(2*p)})
        meter.charge(20+len(features))
    return features,a,primes,common,exceptions


def verify_first_jet(request,certificate,meter=None):
    meter=Meter() if meter is None else meter
    features,a,primes,common,exceptions=_jet_parameters(request,meter)
    exact_zero=common==0 and all(row['coefficient']=='0' for row in exceptions)
    upper=None if common else str(_sum((abs(Q(row['coefficient']))*Q(row['rational_abs_bound']) for row in exceptions),meter))
    status='COMMON_PRIME_TERM_OPEN' if common else 'EXACT_FIRST_JET_ZERO' if exact_zero else 'UNIFORM_FIRST_JET_BOUND'
    expected={'schema':'prime-insertion-first-jet-v1','request':request,
        'generator_primes':primes,'integer_N_minimum':2,
        'common_coefficient':str(common),'exception_rows':exceptions,
        'common_prime_term':'Psi_P(N)=Psi(4N)-3*Psi(2N)+2*Psi(N)',
        'prime_exception_term':'b_p(N)=log(p)*(floor(log_p(4N))-3*floor(log_p(2N))+2*floor(log_p(N)))',
        'identity':"sum_i a_i*h_(S_i)'(0)=common_coefficient*Psi_P(N)+sum_p exception_coefficient(p)*b_p(N)",
        'status':status,'uniform_absolute_upper':upper,
        'first_jet_identity_proved':True,'first_jet_exact_zero_proved':exact_zero,
        'full_kernel_cancellation_proved':False,'low_core_bound_proved':False,'RH_proved':False}
    _expect(certificate,expected);meter.charge(100+len(repr(expected)))
    return {'verified':True,'request':request,'status':status,
        'common_coefficient':str(common),'exception_rows':exceptions,
        'uniform_absolute_upper':upper,'first_jet_identity_proved':True,
        'first_jet_exact_zero_proved':exact_zero,'full_kernel_cancellation_proved':False,
        'low_core_bound_proved':False,'RH_proved':False,'RH_refuted':False,
        'scope':'first derivative at t=0 of the complete finite source; higher jets and finite low-t core OPEN',
        'ordinary_common_prime_term_retained':True,'source_values_evaluated':False}


def verify_low_core_recovery(request,certificate,meter=None):
    meter=Meter() if meter is None else meter
    _keys(request,('tail_request','low_core'))
    alpha,tau,R=_tail_parameters(request['tail_request'],meter)
    low=request['low_core'];_keys(low,('constant','log_power','status'))
    Clow=_rational(low['constant'],meter);eta=_rational(low['log_power'],meter)
    if Clow<0 or eta<0 or low['status']!='OPEN' or type(low['status']) is not str:
        raise ValueError('nonnegative square-root log envelope with OPEN uniform provider')
    shape=_tail_shape(request['tail_request']['primes'],tau,meter)
    compatible=tau>=Q(1,2)
    # At tau1, logN<=2sqrtN. Otherwise the tail has power<=1/2
    # exactly when compatible. Multiply by (1+logN)^eta>=1.
    Ctail=_guard(Q(shape['constant'])+2*Q(shape['log_coefficient']),meter) if compatible else None
    Cfull=_guard(Clow+Ctail,meter) if compatible else None
    original=not request['tail_request']['primes'] and compatible
    expected={'schema':'prime-insertion-low-core-recovery-v1','request':request,
        'source_split':'t_S(N)=low_core_(0,tau)(N)+tail_(tau,infinity)(N)',
        'log_weight':'(1+log(N))^log_power',
        'tail_square_root_compatible':compatible,
        'tail_square_root_constant':str(Ctail) if compatible else None,
        'full_constant':str(Cfull) if compatible else None,
        'log_power':str(eta),'minimum':2,
        'status':'PAID_CONDITIONAL_IMPLICATION_WITH_OPEN_PREMISE' if compatible else 'TAIL_PROVIDER_INSUFFICIENT',
        'conditional_original_target_implication':original,
        'low_core_bound_proved':False,'complete_target_bound_proved':False,'RH_proved':False}
    _expect(certificate,expected);meter.charge(100+len(repr(expected)))
    return {'verified':True,'request':request,'status':expected['status'],
        'conditional_original_target_implication':original,
        'tail_square_root_constant':expected['tail_square_root_constant'],
        'full_constant':expected['full_constant'],'log_weight':expected['log_weight'],
        'scope':'IF |low_core(N)|<=C_low sqrt(N)(1+logN)^eta for EVERYintegerN>=2, complete insertion target obeys the displayed envelope',
        'recovery':'exact source split and triangle; no signed cross terms discarded',
        'low_core_bound_proved':False,'complete_target_bound_proved':False,
        'RH_proved':False,'RH_refuted':False}


verify_recovery=verify_low_core_recovery


def verify_low_core_recovery_schema(request,certificate,meter=None):
    """Same triangle implication, quantified in the UNPAID core constant."""
    meter=Meter() if meter is None else meter
    _keys(request,('tail_request','log_power'))
    alpha,tau,R=_tail_parameters(request['tail_request'],meter)
    eta=_rational(request['log_power'],meter)
    if eta<0:raise ValueError('nonnegative logarithmic envelope')
    shape=_tail_shape(request['tail_request']['primes'],tau,meter)
    compatible=tau>=Q(1,2)
    Ctail=_guard(Q(shape['constant'])+2*Q(shape['log_coefficient']),meter) if compatible else None
    original=not request['tail_request']['primes'] and compatible
    full={'C_low_coefficient':'1','offset':str(Ctail)} if compatible else None
    expected={'schema':'prime-insertion-low-core-recovery-schema-v1','request':request,
        'source_split':'t_S(N)=low_core_(0,tau)(N)+tail_(tau,infinity)(N)',
        'log_weight':'(1+log(N))^log_power',
        'tail_square_root_compatible':compatible,
        'tail_square_root_constant':str(Ctail) if compatible else None,
        'full_constant':full,'log_power':str(eta),'minimum':2,
        'status':'PAID_CONDITIONAL_IMPLICATION_WITH_OPEN_PREMISE' if compatible else 'TAIL_PROVIDER_INSUFFICIENT',
        'conditional_original_target_implication':original,
        'low_core_constant_quantifier':'FOR EVERY finite C_low>=0',
        'open_premise':'|low_core_(0,tau)(N)|<=C_low*sqrt(N)*(1+log(N))^log_power for EVERY integer N>=2',
        'low_core_bound_proved':False,'complete_target_bound_proved':False,'RH_proved':False}
    _expect(certificate,expected);meter.charge(100+len(repr(expected)))
    return {'verified':True,'request':request,'status':expected['status'],
        'conditional_original_target_implication':original,'full_constant':full,
        'tail_square_root_constant':expected['tail_square_root_constant'],
        'low_core_constant_quantifier':expected['low_core_constant_quantifier'],
        'open_premise':expected['open_premise'],
        'low_core_bound_proved':False,'complete_target_bound_proved':False,
        'RH_proved':False,'RH_refuted':False,
        'recovery':'complete signed source split and triangle, with no empirical core constant introduced'}


def verify_microscopic_bound(request,certificate,meter=None):
    """Paid shrinking near-zero endpoint for E_R, not D_S or whole source."""
    meter=Meter() if meter is None else meter
    _keys(request,('alpha','primes','gamma'))
    alpha=_rational(request['alpha'],meter);gamma=_rational(request['gamma'],meter)
    if not 0<alpha<1 or not 0<gamma<=256:raise ValueError('strict fractional exponent and positive rational moving-cutoff capacity')
    R=_primes(request['primes'],meter);k=len(request['primes'])
    if k==0:raise ValueError('nonempty E_R prime set supplies integrability at zero')
    constant=_guard(Q(12*R)/(k-alpha),meter)
    power=_guard(1-gamma*(k-alpha),meter)
    expected={'schema':'prime-insertion-microscopic-bound-v1','request':request,
        'product':R,'prime_count':k,'integer_N_minimum':2,
        'operator':'E_R K(n)=K(R*n), n>=2',
        'filter':{'q':2,'coefficients':[2,-3,1],'normalization':'divide_by_alpha'},
        'integrand':'sum_(2<=n<=4N)w_P(n,N)*prod_(p|R*n)(1-p^-t)',
        'filter_absolute_mass':'4*N','cutoff':'epsilon_N=min(1/2,N^-gamma)',
        'upper_bound':{'constant':str(constant),'N_power':str(power)},
        'unpaid_middle':'epsilon_N<t<1/2','near_zero_bound_proved':True,
        'complete_target_bound_proved':False,'RH_proved':False}
    _expect(certificate,expected);meter.charge(100+len(repr(expected)))
    return {'verified':True,'request':request,'upper_bound':expected['upper_bound'],
        'near_zero_bound_proved':True,'complete_target_bound_proved':False,
        'RH_proved':False,'RH_refuted':False,'unpaid_middle':expected['unpaid_middle'],
        'scope':'E_R full filtered source, EVERYintegerN>=2, only0<t<epsilon_N',
        'source_values_evaluated':False,'unit_gate':'excluded K(R) unit cancels only because P(1)=0',
        'recovery_requires_middle_control':True,'remaining_tail_also_requires_its_own_operator_provider':True}

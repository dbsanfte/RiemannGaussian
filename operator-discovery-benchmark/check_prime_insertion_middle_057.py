"""Independent finite E_R middle integrals and conditional parent transport.

Source reconstruction: trial factorization and complete radical products.
Numerics: integrated exponential Taylor with explicit Lagrange remainder.
No057 producer imports, archive flags, saved arrays or uniform drift admission.
"""
from fractions import Fraction as Q
from math import isqrt, factorial
from weakref import WeakKeyDictionary
from flint import arb,ctx
from check_fractional_prime_rh_bridge_052 import Meter,_rational,_expect

MAX_N=32768
MAX_PRIMES=8
MAX_PRODUCT=1_000_000
MAX_POWER_BITS=400_000
MAX_SOURCE_TERMS=2_000_000
MAX_CACHE_BYTES=4*1024**3
MAX_CONTEXTS=16
MAX_RESULT_BITS=16384
OUTPUT_BITS=160


def _keys(value,keys):
    if type(value) is not dict or set(value)!=set(keys):raise ValueError('exact057 schema')


def _primes(values,meter):
    if type(values) is not list or len(values)>MAX_PRIMES:raise ValueError('bounded prime list')
    previous=1;R=1
    for p in values:
        if type(p) is not int or not previous<p<=MAX_PRODUCT:raise ValueError('sorted distinct actual primes')
        for d in range(2,isqrt(p)+1):
            meter.charge(4)
            if p%d==0:raise ValueError('actual prime required')
        previous=p;R*=p
        if R>MAX_PRODUCT:raise OverflowError('057 source prime-product capacity')
    meter.charge(1+len(values));return R


def _feature(feature,meter,nonempty=False):
    _keys(feature,('primes','gamma','lower_fraction','upper_fraction'))
    R=_primes(feature['primes'],meter)
    gamma=_rational(feature['gamma'],meter)
    low=_rational(feature['lower_fraction'],meter);high=_rational(feature['upper_fraction'],meter)
    if gamma<=0 or not 0<=low<=high<=1:raise ValueError('positive cutoff and ordered affine band')
    if nonempty and not feature['primes']:raise ValueError('nonempty E_R source supplies universal middle envelope')
    return R,gamma,low,high


def _request(request,meter):
    _keys(request,('alpha','primes','N','gamma','lower_fraction','upper_fraction'))
    alpha=_rational(request['alpha'],meter)
    if not 0<alpha<1:raise ValueError('strict fractional ordinary-mu source')
    N=request['N']
    if type(N) is not int or not 2<=N<=MAX_N:raise ValueError('finite integer N2..32768')
    feature={k:request[k] for k in ('primes','gamma','lower_fraction','upper_fraction')}
    R,gamma,low,high=_feature(feature,meter)
    return alpha,tuple(request['primes']),N,R,gamma,low,high


class _Context:
    __slots__=('__weakref__',)


_CONTEXTS=WeakKeyDictionary()


def prepare_context(meter=None):
    if len(_CONTEXTS)>=MAX_CONTEXTS:raise MemoryError('live057 checker contexts')
    if meter is not None:meter.charge()
    context=_Context()
    _CONTEXTS[context]={'factors':{},'sources':{},'logs':{},'moments':{},'epsilon_gates':{},'bytes':0}
    return context


def _state(context):
    if type(context) is not _Context or context not in _CONTEXTS:raise ValueError('live checker-created context required')
    return _CONTEXTS[context]


def _store(state,table,key,value,size,meter):
    total=sum(other['bytes'] for other in _CONTEXTS.values())+size
    meter.charge(1+len(_CONTEXTS))
    if type(size) is not int or size<0 or total>MAX_CACHE_BYTES:raise MemoryError('prospective057 global cache capacity')
    state[table][key]=value;state['bytes']+=size
    return value


def _factor(n,state,meter):
    if n in state['factors']:meter.charge();return state['factors'][n]
    remaining=n;p=2;result=[]
    while p*p<=remaining:
        if remaining%p==0:
            result.append(p)
            while remaining%p==0:remaining//=p;meter.charge(4)
        p+=1;meter.charge(4)
    if remaining>1:result.append(remaining)
    return _store(state,'factors',n,tuple(result),80+32*len(result),meter)


def _source(primes,N,state,meter):
    key=(primes,N)
    if key in state['sources']:meter.charge();return state['sources'][key],True
    coefficients={};generated=0
    # w=-2 on(N,2N] and+1 on(2N,4N]; n1 and alln<=N have
    # weightzero. Enumerate every squarefree divisor of rad(R*n).
    for n in range(N+1,4*N+1):
        weight=-2 if n<=2*N else 1
        radical=sorted(set(primes).union(_factor(n,state,meter)))
        count=1<<len(radical);generated+=count
        if generated>MAX_SOURCE_TERMS:raise MemoryError('prospective complete radical expansion capacity')
        meter.charge(8*count+len(radical))
        divisors=[(1,1)]
        for p in radical:divisors += [(d*p,-sign) for d,sign in divisors]
        for d,sign in divisors:coefficients[d]=coefficients.get(d,0)+weight*sign
    if sum(coefficients.values())!=0 or coefficients.get(1,0)!=0:
        raise ArithmeticError('source zerojet and filtered unit must both cancel exactly')
    rows=tuple((d,c) for d,c in sorted(coefficients.items()) if c)
    if any(d<2 or abs(c)>4*N for d,c in rows):raise ArithmeticError('complete source coefficient bounds')
    size=256+96*len(rows)
    _store(state,'sources',key,(rows,generated),size,meter)
    return (rows,generated),False


def _aq(value):return arb(value.numerator)/value.denominator


def _dyadic(value,meter,up=False):
    if not value.is_finite():raise ArithmeticError('finite rigorous057 endpoint required')
    m,e=value.man_exp();m,e=int(m),int(e)
    shift=e+OUTPUT_BITS
    if abs(m).bit_length()+max(0,shift)>MAX_RESULT_BITS:raise OverflowError('057 endpoint result capacity')
    if shift>=0:n=m<<shift
    elif up:n=-((-m)>>(-shift))
    else:n=m>>(-shift)
    meter.charge(1+abs(m).bit_length()+max(0,shift))
    return Q(n,1<<OUTPUT_BITS)


def _output(text,meter):
    if type(text) is not str or not 1<=len(text)<=10000:raise ValueError('canonical finite interval output')
    try:value=Q(text)
    except (ValueError,ZeroDivisionError):raise ValueError('finite interval rational') from None
    if str(value)!=text or max(abs(value.numerator).bit_length(),value.denominator.bit_length())>MAX_RESULT_BITS:
        raise ValueError('output rational capacity')
    meter.charge(1+len(text));return value


def _epsilon(N,gamma,state,meter):
    key=(N,gamma)
    if key in state['epsilon_gates']:meter.charge();return state['epsilon_gates'][key]
    estimate=max(N.bit_length()*gamma.numerator,gamma.denominator+1)
    if estimate>MAX_POWER_BITS:raise OverflowError('exact moving-cutoff comparison capacity')
    meter.charge(estimate+N.bit_length()*gamma.numerator.bit_length()+1)
    half=pow(N,gamma.numerator)<=(1<<gamma.denominator)
    return _store(state,'epsilon_gates',key,half,128,meter)


def _log(n,precision,state,meter):
    key=(n,precision)
    if key in state['logs']:meter.charge();return state['logs'][key],False
    value=arb(n).log()
    meter.charge(precision*precision//16+n.bit_length())
    return _store(state,'logs',key,value,128+precision//4,meter),True


def _moments(primes,N,rows,degree,precision,state,meter):
    key=(primes,N,degree,precision)
    if key in state['moments']:meter.charge();return state['moments'][key],True
    moments=[arb(0) for _ in range(degree+1)];absolute_next=arb(0);new_logs=0
    minimum=max(1,len(primes))
    for d,coefficient in rows:
        logd,fresh=_log(d,precision,state,meter);new_logs+=int(fresh)
        value=logd**minimum
        for k in range(minimum,degree+1):
            moments[k]+=coefficient*value;value*=logd
            meter.charge(8+precision//64)
        # Every derivative below the number of inserted primes is EXACT0,
        # since each original summand retains those simplezero factors.
        absolute_next+=abs(coefficient)*value
        meter.charge(8+precision//64)
    payload=(tuple(moments),absolute_next,new_logs)
    _store(state,'moments',key,payload,512+(degree+2)*(128+precision//4),meter)
    return payload,False


def _integral_power(a,b,beta,meter,precision):
    # Stable even for beta=1-alpha verysmall: avoid subtracting two
    # nearlyequal powers. a,b>0 and beta>0 are exact source gates.
    value=(beta*b.log()).exp()*(-(beta*(a/b).log()).expm1())/beta
    meter.charge(precision*precision//8+32)
    return value


def _finite(request,meter,context,precision=256,degree=128):
    alpha,primes,N,R,gamma,low,high=_request(request,meter)
    state=_state(context)
    at_half=_epsilon(N,gamma,state,meter)
    if at_half or low==high:
        return Q(0),Q(0),{'status':'EXACT_ZERO_BAND','source_reconstructed':False,
            'exact_cutoff_half_gate':at_half,'source_support':4*N,'precision':precision,
            'method':'exact integer-powered cutoff gate or equal affine endpoints'}
    (rows,generated),source_hit=_source(primes,N,state,meter)
    if not rows:
        return Q(0),Q(0),{'status':'EXACT_ZERO_SOURCE','source_reconstructed':True,
            'source_support':4*N,'source_coefficient_count':0,'precision':precision}
    with ctx.workprec(precision):
        epsilon=(-_aq(gamma)*arb(N).log()).exp()
        a=epsilon+(arb(1)/2-epsilon)*_aq(low)
        b=epsilon+(arb(1)/2-epsilon)*_aq(high)
        if not a>0 or not b>0:raise ArithmeticError('positive integrated source endpoints')
        (moments,absolute_next,new_logs),moment_hit=_moments(primes,N,rows,degree,precision,state,meter)
        total=arb(0)
        minimum=max(1,len(primes))
        denominator=1
        for k in range(1,degree+1):
            denominator*=k
            if k<minimum:continue
            beta=_aq(Q(k)-alpha)
            integral=_integral_power(a,b,beta,meter,precision)
            total+=((-1)**k)*moments[k]*integral/denominator
            meter.charge(precision+denominator.bit_length())
        next_beta=_aq(Q(degree+1)-alpha)
        remainder=absolute_next*_integral_power(a,b,next_beta,meter,precision)/factorial(degree+1)
        normalizer=_aq(1-alpha).rgamma()
        if not normalizer>0:raise ArithmeticError('strict positive normalization')
        total*=normalizer;remainder*=normalizer
        meter.charge(precision*precision//8+32)
        lo=_dyadic(total.lower(),meter);hi=_dyadic(total.upper(),meter,True)
        radius=_dyadic(remainder.abs_upper(),meter,True)
        lo-=radius;hi+=radius
    return lo,hi,{'status':'FINITE_INTERVAL','source_reconstructed':True,
        'source_support':4*N,'prime_product':R,'source_coefficient_count':len(rows),
        'source_coefficient_sum':sum(c for _,c in rows),'source_coefficient_l1':sum(abs(c) for _,c in rows),
        'squarefree_product_terms_generated':generated,'source_cache_hit':source_hit,
        'moments_cache_hit':moment_hit,'new_log_atoms':0 if moment_hit else new_logs,
        'precision':precision,'Taylor_degree':degree,'integrated_remainder_upper':str(radius),
        'method':'complete trial-factored radical products; integrated exponential Taylor and explicit Lagrange remainder'}


def verify_middle_interval(request,proposal,meter=None,context=None):
    meter=Meter(cap=200_000_000_000,seconds=7200) if meter is None else meter
    _keys(proposal,('lower','upper'))
    lower=_output(proposal['lower'],meter);upper=_output(proposal['upper'],meter)
    if lower>upper:raise ValueError('ordered producer interval')
    context=prepare_context(meter) if context is None else context
    lo,hi,rebuild=_finite(request,meter,context)
    if not lower<=lo<=hi<=upper:
        lo,hi,rebuild=_finite(request,meter,context,384,160)
    if not lower<=lo<=hi<=upper:raise ValueError('independent Taylor interval is not contained in supplied middle interval')
    return {'verified':True,'request':request,'N':request['N'],'status':rebuild['status'],
        'lower':str(lo),'upper':str(hi),'rebuild':rebuild,'finite_only':True,
        'source_chain_replayed_here':rebuild['source_reconstructed'],
        'all_scale':False,'uniform_middle_bound_proved':False,'RH_proved':False,'RH_refuted':False,
        'archive_flags_used_as_authority':False,'producer_imported':False}


def _guard(value,meter):
    meter.charge(1+abs(value.numerator).bit_length()+value.denominator.bit_length())
    if max(abs(value.numerator).bit_length(),value.denominator.bit_length())>32768:
        raise OverflowError('parent transport rational intermediate capacity')
    return value


def verify_parent_recovery(request,certificate,meter=None):
    meter=Meter() if meter is None else meter
    _keys(request,('alpha','features','coefficients','lambda','weights','delta','C'))
    alpha=_rational(request['alpha'],meter)
    if not 0<alpha<1:raise ValueError('fractional middle source')
    features=request['features'];coefficients=request['coefficients']
    if type(features) is not list or not 1<=len(features)<=32:raise ValueError('bounded nonempty source feature family')
    envelopes=[];keys=[]
    for feature in features:
        R,gamma,low,high=_feature(feature,meter,True)
        keys.append((tuple(feature['primes']),gamma,low,high))
        envelopes.append(_guard(Q(12*R)/(len(feature['primes'])-alpha),meter))
    if len(set(keys))!=len(features):raise ValueError('distinct literal source bands')
    if type(coefficients) is not list or len(coefficients)!=len(features) or any(type(c) is not int or abs(c).bit_length()>1024 for c in coefficients):
        raise ValueError('complete bounded signed integer auxiliary vector')
    lam=_rational(request['lambda'],meter);delta=_rational(request['delta'],meter);C=_rational(request['C'],meter)
    if min(lam,delta,C)<0:raise ValueError('nonnegative energy/forcing parameters')
    weights=request['weights']
    if type(weights) is not list or len(weights)!=3:raise ValueError('three fixed parent offset weights')
    w=[_rational(x,meter) for x in weights]
    if min(w)<0 or sum(w)!=1:raise ValueError('nonnegative convex all-parent transport')
    terms=[]
    for i in range(len(coefficients)):
        for j in range(i,len(coefficients)):
            c=_guard(lam*coefficients[i]*coefficients[j]*(1 if i==j else 2)+int(i==j==0),meter)
            if c:terms.append({'i':i,'j':j,'coefficient':str(c)})
    mixture=Q(0)
    for a,b in zip(coefficients,envelopes):mixture=_guard(mixture+abs(a)*b,meter)
    base=_guard(5*(envelopes[0]**2+lam*mixture**2),meter)
    constant=_guard(base+2*C/delta,meter) if delta>0 else base
    expected={'schema':'prime-insertion-middle-parent-recovery-v1','request':request,
        'matrix_terms':terms,'source_envelopes':[str(x) for x in envelopes],'base_upper':str(base),
        'recurrence':{'minimum':3,'children':[0,1],'offsets':[-1,0,1],
            'formula':'F(2N+r)<=sum_s w_s*F(N+s)+C/N^delta','status':'OPEN'},
        'recovery':{'kind':'bounded' if delta>0 else 'logarithmic',
            'constant':str(constant),'log_coefficient':'0' if delta>0 else str(C),
            'logarithm_base':2,'argument_shift':2,'base_maximum':5},
        'uniform_recurrence_proved':False,'uniform_middle_bound_proved':False,'RH_proved':False}
    _expect(certificate,expected);meter.charge(100+len(repr(expected)))
    return {'verified':True,'request':request,'target_domination_proved':True,
        'source_free_base_proved':True,'conditional_parent_recovery_proved':True,
        'base_upper':str(base),'recovery':expected['recovery'],'recurrence_status':'OPEN',
        'domain':'EVERYintegerN>=2; seeds2..5, both children for everyparentN>=3',
        'log_branch':'B on2..5; thereafter B+C*max(0,floor(log2(N-2))-1)',
        'target_scope':'literal feature0 middle band only, not original K or complete source',
        'uniform_recurrence_proved':False,'uniform_middle_bound_proved':False,'RH_proved':False,'RH_refuted':False}


verify_recovery=verify_parent_recovery

"""Independent finite ordinary-Mobius transport and incomplete-gamma audit.

No059 producer imports or savedsource flags. Finite plan triangle certificates
are not uniform estimates. Every unit, rangeexit and unmatched token remains.
"""
from fractions import Fraction as Q
from math import isqrt,gcd
from weakref import WeakKeyDictionary
from flint import arb,ctx
from check_fractional_prime_rh_bridge_052 import Meter,_rational,_expect

MAX_N=32768
MAX_PRIMES=8
MAX_PRODUCT=1_000_000
MAX_POWER_BITS=400_000
MAX_PLANS=1024
MAX_PLAN_ENTRIES=8_000_000
MAX_CACHE_BYTES=4*1024**3
MAX_CONTEXTS=8
MAX_RESULT_BITS=16384
OUTPUT_BITS=160
PRECISIONS=(128,192,256,384,512)


def _keys(obj,keys):
    if type(obj) is not dict or set(obj)!=set(keys):raise ValueError('exact059 schema')


def _request(request,meter):
    _keys(request,('N','alpha','gamma','tau','primes','p','q'))
    N=request['N']
    if type(N) is not int or not 2<=N<=MAX_N:raise ValueError('finite integer N2..32768')
    alpha=_rational(request['alpha'],meter);gamma=_rational(request['gamma'],meter);tau=_rational(request['tau'],meter)
    if not 0<alpha<1 or gamma<=0 or not 0<tau<1:raise ValueError('fractional ordinary source and strictpositivecutoffs')
    primes=request['primes']
    if type(primes) is not list or not 2<=len(primes)<=MAX_PRIMES:raise ValueError('bounded actualprime M containingp,q')
    previous=1;R=1
    for prime in primes:
        if type(prime) is not int or not previous<prime<=MAX_PRODUCT:raise ValueError('sorted distinct actualprimes')
        for d in range(2,isqrt(prime)+1):
            meter.charge(4)
            if prime%d==0:raise ValueError('actualprime required')
        R*=prime;previous=prime
        if R>MAX_PRODUCT:raise OverflowError('059 source prime-product capacity')
    p,q=request['p'],request['q']
    if type(p) is not int or type(q) is not int or not p<q or p not in primes or q not in primes:
        raise ValueError('distinct actualp<q registeredinM')
    meter.charge(1+len(primes))
    return N,alpha,gamma,tau,tuple(primes),p,q,R


class _Context:
    __slots__=('__weakref__',)


_CONTEXTS=WeakKeyDictionary()


def prepare_context(meter=None):
    if len(_CONTEXTS)>=MAX_CONTEXTS:raise MemoryError('live059checkercontexts')
    if meter is not None:meter.charge()
    obj=_Context();_CONTEXTS[obj]={'mu':{},'tokens':{},'logs':{},'phi':{},'gates':{},'bytes':0}
    return obj


def _state(context):
    if type(context) is not _Context or context not in _CONTEXTS:raise ValueError('live checker-created059context required')
    return _CONTEXTS[context]


def _store(state,table,key,value,size,meter):
    if type(size) is not int or size<0:raise ValueError('prospectiveprivatecachecost')
    total=sum(s['bytes'] for s in _CONTEXTS.values())+size
    meter.charge(1+len(_CONTEXTS))
    if total>MAX_CACHE_BYTES:raise MemoryError('aggregateprospective059cachecapacity')
    state[table][key]=value;state['bytes']+=size;return value


def _mu(n,state,meter):
    if n in state['mu']:meter.charge();return state['mu'][n]
    remaining=n;p=2;sign=1
    while p*p<=remaining:
        meter.charge(4)
        if remaining%p==0:
            remaining//=p;sign=-sign;meter.charge(1+remaining.bit_length())
            if remaining%p==0:return _store(state,'mu',n,0,80,meter)
        p+=1
    if remaining>1:sign=-sign
    return _store(state,'mu',n,sign,80,meter)


def _W(N,a):return (4*N)//a-3*((2*N)//a)+2*(N//a)


def _tokens(data,state,meter):
    N,alpha,gamma,tau,primes,p,q,R=data;key=(N,primes,p,q)
    if key in state['tokens']:meter.charge();return state['tokens'][key],True
    tokens=[]
    for d in range(1,(4*N)//p+1):
        meter.charge(4+d.bit_length()+R.bit_length())
        if gcd(d,R)!=1:continue
        mu=_mu(d,state,meter)
        if not mu:continue
        a,b=_W(N,p*d),_W(N,q*d)
        if a not in (-1,0,1) or b not in (-1,0,1):raise ArithmeticError('completefiltercoefficientrange')
        if a==b==0:continue
        if not b:profile,sigma='P',a
        elif not a:profile,sigma='Q',-b
        elif a==b:profile,sigma='D',a
        else:profile,sigma='S',a
        tokens.append((d,profile,mu*sigma,sigma,mu))
    payload=tuple(tokens)
    return _store(state,'tokens',key,payload,256+160*len(payload),meter),False


def _public_tokens(tokens):
    return [{'d':d,'profile':profile,'sign':sign,'kernel_sign':sigma,'mu':mu}
        for d,profile,sign,sigma,mu in tokens]


def _plan(plan,tokens,meter):
    _keys(plan,('pairs','unmatched'))
    pairs=plan['pairs'];unmatched=plan['unmatched']
    if type(pairs) is not list or type(unmatched) is not list:raise ValueError('finitecompletepair/unmatchedlists')
    if len(pairs)*2+len(unmatched)!=len(tokens):raise ValueError('every nonzero token once')
    by_d={row[0]:row for row in tokens};seen=set()
    for pair in pairs:
        if type(pair) is not list or len(pair)!=2:raise ValueError('exactoppositesignpair')
        for d in pair:
            if type(d) is not int or d not in by_d or d in seen:raise ValueError('actualuniquetokencoverage')
            seen.add(d)
        if by_d[pair[0]][2]!=-by_d[pair[1]][2]:raise ValueError('oppositesourcesignsrequired')
        meter.charge(20)
    for d in unmatched:
        if type(d) is not int or d not in by_d or d in seen:raise ValueError('actualuniqueunmatchedcoverage')
        seen.add(d);meter.charge(10)
    if seen!=set(by_d):raise ValueError('no sourceunit/rangeexit/tokenomission')
    return by_d


def verify_plan(request,plan,meter=None):
    meter=Meter(cap=200_000_000_000,seconds=7200) if meter is None else meter
    data=_request(request,meter);context=prepare_context(meter);tokens,hit=_tokens(data,_state(context),meter)
    _plan(plan,tokens,meter)
    return {'verified':True,'request':request,'plan':plan,'tokens':_public_tokens(tokens),
        'identity_proved':True,'finite_triangle_bound_proved':True,
        'bound_formula':'sum_pairs |magnitude_i-magnitude_j|+sum_unmatched magnitude_i',
        'opposite_source_signs_retained':True,'cross_profile_pairs_allowed':True,
        'ordinary_mu_rebuilt':True,'unit_d1_retained':True,'all_range_exits_retained':True,
        'finite_only':True,'uniform_growth_bound_proved':False,'RH_proved':False,'RH_refuted':False,
        'producer_imported':False,'source_arrays_read':False}


def _aq(value):return arb(value.numerator)/value.denominator


def _dyadic(value,meter,up=False):
    if not value.is_finite():raise ArithmeticError('finite059endpointrequired')
    man,exponent=value.man_exp();man,exponent=int(man),int(exponent)
    shift=exponent+OUTPUT_BITS
    if abs(man).bit_length()+max(0,shift)>MAX_RESULT_BITS:raise OverflowError('059outwardendpointcapacity')
    numerator=man<<shift if shift>=0 else -((-man)>>(-shift)) if up else man>>(-shift)
    meter.charge(1+abs(man).bit_length()+max(0,shift))
    return Q(numerator,1<<OUTPUT_BITS)


def _interval(value,meter,nonnegative=False):
    lower=_dyadic(value.lower(),meter);upper=_dyadic(value.upper(),meter,True)
    if nonnegative:
        if upper<0:raise ArithmeticError('enclosureviolatesprovednonnegativekernel')
        lower=max(Q(0),lower)
    return {'lower':str(lower),'upper':str(upper)}


def _parse_interval(value,meter,nonnegative=False):
    _keys(value,('lower','upper'));values=[]
    for text in (value['lower'],value['upper']):
        if type(text) is not str or not 1<=len(text)<=10000:raise ValueError('canonical059interval')
        try:v=Q(text)
        except (ValueError,ZeroDivisionError):raise ValueError('exactfiniteendpoint') from None
        if str(v)!=text or max(abs(v.numerator).bit_length(),v.denominator.bit_length())>MAX_RESULT_BITS:
            raise ValueError('canonicalendpointcapacity')
        meter.charge(1+len(text));values.append(v)
    if values[0]>values[1] or nonnegative and values[0]<0:raise ValueError('orderednonnegativeboundinterval')
    return tuple(values)


def _band(data,state,meter,precision):
    N,alpha,gamma,tau,primes,p,q,R=data
    key=(N,gamma,tau)
    if key not in state['gates']:
        estimate=max(N.bit_length()*gamma.numerator+abs(tau.numerator).bit_length()*gamma.denominator,
            tau.denominator.bit_length()*gamma.denominator)
        if estimate>MAX_POWER_BITS:raise OverflowError('059exactpoweredcutoffcapacity')
        meter.charge(estimate+1)
        empty=pow(N,gamma.numerator)*pow(tau.numerator,gamma.denominator)<=pow(tau.denominator,gamma.denominator)
        _store(state,'gates',key,empty,160,meter)
    else:meter.charge()
    empty=state['gates'][key]
    if empty:return _aq(tau),_aq(tau),True
    meter.charge(precision*precision//8+N.bit_length())
    return (-_aq(gamma)*arb(N).log()).exp(),_aq(tau),False


def _log(n,precision,state,meter):
    key=(n,precision)
    if key in state['logs']:meter.charge();return state['logs'][key]
    meter.charge(precision*precision//16+n.bit_length())
    return _store(state,'logs',key,arb(n).log(),128+precision//4,meter)


def _phi(a,data,epsilon,tau,precision,state,meter):
    N,alpha,gamma,tauQ,primes,p,q,R=data;key=(N,alpha,gamma,tauQ,primes,a,precision)
    if key in state['phi']:meter.charge();return state['phi'][key],True
    if type(a) is not int or not 2<=a<=4*N:raise ValueError('fullfinitekernelbase2..4N')
    divisors=[(1,1)]
    for prime in primes:divisors += [(e*prime,-mu) for e,mu in divisors]
    total=arb(0)
    for e,mu in divisors:
        lam=_log(a*e,precision,state,meter)
        power=lam**_aq(alpha)
        lo=(lam*epsilon).gamma_upper(-_aq(alpha));hi=(lam*tau).gamma_upper(-_aq(alpha))
        total+=mu*power*(lo-hi)
        meter.charge(precision*precision//4+precision*3+64)
    total*=_aq(1-alpha).rgamma();meter.charge(precision*precision//8+64)
    result=_interval(total,meter,True)
    return _store(state,'phi',key,result,512+precision//2,meter),False


def _bounds_sum(intervals,meter):
    lower=sum((v[0] for v in intervals),Q(0));upper=sum((v[1] for v in intervals),Q(0))
    meter.charge(2*len(intervals)+1)
    if any(max(abs(v.numerator).bit_length(),v.denominator.bit_length())>MAX_RESULT_BITS for v in (lower,upper)):
        raise OverflowError('059aggregatefiniteendpointcapacity')
    return lower,upper


def _absolute_difference(a,b):
    lo=a[0]-b[1];hi=a[1]-b[0]
    return (Q(0) if lo<=0<=hi else min(abs(lo),abs(hi)),max(abs(lo),abs(hi)))


def _pair_result(plan,magnitudes,meter):
    pieces=[_absolute_difference(magnitudes[i],magnitudes[j]) for i,j in plan['pairs']]
    pieces += [magnitudes[d] for d in plan['unmatched']]
    lower,upper=_bounds_sum(pieces,meter)
    return {'lower':str(lower),'upper':str(upper)}


def _profile_optimum(tokens,magnitudes,meter):
    """Exact prefix-flux transport envelope within EACH monotoneprofile."""
    pieces=[]
    for profile in ('P','Q','D','S'):
        ids=[d for d,kind,sign,sigma,mu in tokens if kind==profile]
        signs={d:sign for d,kind,sign,sigma,mu in tokens if kind==profile}
        prefix=0
        for i,d in enumerate(ids):
            prefix+=signs[d];current=magnitudes[d]
            following=magnitudes[ids[i+1]] if i+1<len(ids) else (Q(0),Q(0))
            lower=max(Q(0),current[0]-following[1]);upper=current[1]-following[0]
            if upper<0:raise ArithmeticError('provedprofilemonotonicityviolated')
            pieces.append((abs(prefix)*lower,abs(prefix)*upper));meter.charge(16)
    lower,upper=_bounds_sum(pieces,meter)
    return {'lower':str(lower),'upper':str(upper)}


def verify_profile_dominance(policy,certificate,meter=None):
    meter=Meter() if meter is None else meter
    _keys(policy,('steps',));steps=policy['steps']
    if type(steps) is not list or len(steps)>2:raise ValueError('boundeddeclaredprofileonlypolicy')
    for step in steps:
        if type(step) is not dict:raise ValueError('typedexactpolicy step')
        kind=step.get('kind');group=step.get('group')
        if kind=='scan':
            keys=['kind','group','order','method']
            if group=='profile_residue':keys.append('modulus')
            elif group=='profile_block':keys.append('theta')
            elif group not in ('profile','sector','profile_quotient'):raise ValueError('crossprofilegroupisnotdominatedbyprofiletheorem')
            _keys(step,keys)
            if step['method'] not in ('stack','fifo'):raise ValueError('declaredscanmethod')
            if group=='profile_residue' and (type(step['modulus']) is not int or not 2<=step['modulus']<=100000):
                raise ValueError('exactresidueclasscapacity')
            if group=='profile_block' and not 0<=_rational(step['theta'],meter)<=1:raise ValueError('exactrationalblockpower0..1')
        elif kind=='prime_ratio':
            _keys(step,('kind','group','order'))
            if group!='profile':raise ValueError('primeedgesmuststaywithineachprofile')
        else:raise ValueError('licensedprofilepolicykind')
        if step['order'] not in ('asc','desc'):raise ValueError('declaredliteralorder')
        meter.charge(50)
    expected={'schema':'mobius-profile-dominance-v1','policy':policy,
        'reference':{'steps':[{'kind':'scan','group':'profile','order':'asc','method':'stack'}]},
        'bound':'B_reference<=B_policy','uniform_growth_bound_proved':False,'RH_proved':False}
    _expect(certificate,expected);meter.charge(100+len(repr(expected)))
    return {'verified':True,'policy':policy,'reference':expected['reference'],
        'finite_profile_transport_dominance_proved':True,
        'domain':'everyadmittedfinitearithmeticN andpositivekernelband; fixedprofileonlypolicies',
        'proof_rule':'positive monotoneprofile kernels; prefixflux optimum withunmatchedzero dummy',
        'uniform_growth_bound_proved':False,'RH_proved':False,'RH_refuted':False,
        'cross_profile_policy_dominated':False,'actual_arithmetic_refuted':False}


def evaluate_many(request,plans,precision=256,meter=None,context=None):
    meter=Meter(cap=200_000_000_000,seconds=7200) if meter is None else meter
    if type(precision) is not int or precision not in PRECISIONS:raise ValueError('bounded059Arbprecision')
    if type(plans) is not list or not 1<=len(plans)<=MAX_PLANS:raise ValueError('boundednonemptyplanbatch')
    data=_request(request,meter);context=prepare_context(meter) if context is None else context
    state=_state(context);start=meter.operations
    tokens,token_hit=_tokens(data,state,meter)
    if len(plans)*len(tokens)>MAX_PLAN_ENTRIES:raise MemoryError('prospective059planbatchcoveragecapacity')
    for plan in plans:_plan(plan,tokens,meter)
    N,alpha,gamma,tauQ,primes,p,q,R=data
    new_kernels=0;magnitudes={}
    with ctx.workprec(precision):
        epsilon,tau,empty=_band(data,state,meter,precision)
        if empty:
            magnitudes={row[0]:(Q(0),Q(0)) for row in tokens}
        else:
            phi={}
            for d,profile,sign,sigma,mu in tokens:
                for base in ((p*d,) if profile=='P' else (q*d,) if profile=='Q' else (p*d,q*d)):
                    if base not in phi:
                        interval,hit=_phi(base,data,epsilon,tau,precision,state,meter)
                        phi[base]=_parse_interval(interval,meter,True);new_kernels+=int(not hit)
                if profile=='P':magnitude=phi[p*d]
                elif profile=='Q':magnitude=phi[q*d]
                elif profile=='S':magnitude=(phi[p*d][0]+phi[q*d][0],phi[p*d][1]+phi[q*d][1])
                else:
                    magnitude=(max(Q(0),phi[p*d][0]-phi[q*d][1]),phi[p*d][1]-phi[q*d][0])
                    if magnitude[1]<0:raise ArithmeticError('provedPhi(pd)>Phi(qd)violatedbyinterval')
                magnitudes[d]=magnitude;meter.charge(20)
    signed=[]
    for d,profile,sign,sigma,mu in tokens:
        lo,hi=magnitudes[d];signed.append((lo,hi) if sign==1 else (-hi,-lo))
    signed_lo,signed_hi=_bounds_sum(signed,meter)
    absolute_lo,absolute_hi=_bounds_sum(list(magnitudes.values()),meter)
    profile_optimum=_profile_optimum(tokens,magnitudes,meter)
    rows=[]
    for i,plan in enumerate(plans):
        rows.append({'plan_index':i,'bound':_pair_result(plan,magnitudes,meter),
            'verification':{'verified':True,'complete_coverage':True,'opposite_sign_pairs':True,
                'finite_triangle_bound_proved':True,'uniform_growth_bound_proved':False,'RH_proved':False}})
    public_tokens=_public_tokens(tokens);meter.charge(5*len(tokens)+1)
    return {'request':request,'signed_sum':{'lower':str(signed_lo),'upper':str(signed_hi)},
        'absolute_sum':{'lower':str(absolute_lo),'upper':str(absolute_hi)},'rows':rows,
        'tokens':public_tokens,
        'profile_optimum':profile_optimum,'profile_optimum_scope':'minimumcostforsame_profile_onlyplans, notcrossprofileplans oractualJ',
        'counts':{'operations':meter.operations-start,'token_count':len(tokens),
            'token_cache_hit':token_hit,'new_Phi_kernels':new_kernels,'precision':precision,
            'cache_bytes_estimate':state['bytes']},
        'verified':True,'source_chain_replayed_here':not empty,'exact_zero_band':empty,
        'method':'independenttrialfactorordinarymu; exactsignedG_M expansion; Arbincompletegamma',
        'finite_only':True,'uniform_growth_bound_proved':False,'RH_proved':False,'RH_refuted':False,
        'producer_imported':False,'saved_source_flags_used_as_authority':False}


def evaluate(request,plan,precision=256,meter=None,context=None):
    result=evaluate_many(request,[plan],precision,meter,context)
    return dict(result,bound=result['rows'][0]['bound'])


def assess_bound(request,bound_interval,claim,meter=None):
    meter=Meter(cap=200_000_000_000,seconds=7200) if meter is None else meter
    data=_request(request,meter);_keys(claim,('C','beta'))
    C=_rational(claim['C'],meter);beta=_rational(claim['beta'],meter)
    if C<0 or not 0<=beta<=2:raise ValueError('nonnegativefiniteconstant/growthpower0..2')
    lower,upper=_parse_interval(bound_interval,meter,True)
    with ctx.workprec(256):
        value=_aq(C)*(arb(data[0])**beta.numerator if beta.denominator==1 else (_aq(beta)*arb(data[0]).log()).exp())
        allowance=_interval(value,meter,True)
    a_lo,a_hi=_parse_interval(allowance,meter,True)
    status='PASS' if upper<=a_lo else 'REFUTED' if lower>a_hi else 'UNRESOLVED'
    return {'status':status,'request':request,'claim':claim,'bound':bound_interval,'allowance':allowance,
        'domain':'thisfiniteintegerN only','uniform_growth_bound_proved':False,'RH_proved':False,'RH_refuted':False}


def verify_bound(request,plan,claim,precision=256,meter=None,context=None):
    meter=Meter(cap=200_000_000_000,seconds=7200) if meter is None else meter
    finite=evaluate(request,plan,precision,meter,context)
    return {'evaluation':finite,'assessment':assess_bound(request,finite['bound'],claim,meter)}

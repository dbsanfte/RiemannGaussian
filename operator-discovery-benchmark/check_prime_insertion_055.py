"""Independent ordinary-mu prime-insertion identities and finite intervals.

No055 producer imports or archived source authority. Shifted atoms are rebuilt
only for NEW selected finite audits using frozen053 independent primitives.
Symbolic positivity is pointwise n>=2, not a uniform prefix/energy theorem.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import gcd,isqrt
from weakref import WeakKeyDictionary
import numpy as np
from check_fractional_prime_rh_bridge_052 import Meter,_rational,_expect
import check_prime_scale_values_053 as VALUES

BITS=32
MAX_N=2_000_000
MAX_LIVE_CONTEXTS=64
MAX_MU_INDICES=4_000_000
MAX_ATOMS=1_000_000
MAX_OUTPUT_BITS=16384


def _keys(obj,keys):
    if type(obj) is not dict or set(obj)!=set(keys):raise ValueError('exact prime-insertion schema')


def _output_rational(text,meter):
    # Derived endpoints can contain the input alpha denominator AND the full
    # signed accumulation; they are not constrained to input-sized strings.
    if type(text) is not str or not 1<=len(text)<=10000:raise ValueError('bounded canonical output rational')
    try:value=Q(text)
    except (ValueError,ZeroDivisionError):raise ValueError('output rational') from None
    if str(value)!=text or max(abs(value.numerator).bit_length(),value.denominator.bit_length())>MAX_OUTPUT_BITS:
        raise ValueError('output rational resource capacity')
    meter.charge(len(text)+1);return value


def _parameters(request,meter,finite=False):
    _keys(request,('alpha','primes','q','coefficients','N') if finite else ('alpha','primes'))
    alpha=_rational(request['alpha'],meter)
    if not 0<alpha<1:raise ValueError('strict fractional exponent')
    primes=request['primes']
    if type(primes) is not list or len(primes)>8:raise ValueError('bounded canonical prime set')
    last=1;R=1
    for p in primes:
        if type(p) is not int or not last<p<=MAX_N:raise ValueError('distinct sorted actual primes')
        for d in range(2,isqrt(p)+1):
            meter.charge()
            if p%d==0:raise ValueError('actual prime required')
        last=p;R*=p
        if R>MAX_N:raise OverflowError('prime product resource capacity')
    subsets=[]
    for k in range(len(primes)+1):
        for subset in combinations(primes,k):
            product=1
            for p in subset:product*=p
            subsets.append((subset,product,(-1)**k));meter.charge(1+k)
    if not finite:return alpha,primes,R,subsets
    q=request['q'];cs=request['coefficients'];N=request['N']
    if type(q) is not int or not 2<=q<=64:raise ValueError('bounded integer scale')
    if type(cs) is not list or not 1<=len(cs)<=17 or cs[-1]==0 or any(type(c) is not int or abs(c).bit_length()>1024 for c in cs):
        raise ValueError('finite bounded integer coefficients')
    if type(N) is not int or not 2<=N<=MAX_N:raise ValueError('ordinary finite scale N>=2')
    horizon=q**(len(cs)-1)*N
    if R*horizon>MAX_N:raise OverflowError('complete shifted source horizon resource capacity')
    return alpha,primes,R,subsets,q,cs,N,horizon


class _Context:
    __slots__=('__weakref__',)


_CONTEXTS=WeakKeyDictionary()


def prepare_context(meter=None):
    if meter is not None:meter.charge()
    if len(_CONTEXTS)>=MAX_LIVE_CONTEXTS:raise OverflowError('live insertion contexts')
    context=_Context();_CONTEXTS[context]={'mu':None,'max_n':0,'atoms':{},'alphas':set()};return context


def _cache(context):
    if type(context) is not _Context or context not in _CONTEXTS:raise ValueError('live checker-created insertion context required')
    return _CONTEXTS[context]


def _mu(context,horizon,meter):
    state=_cache(context);old=state['max_n']
    if old>=horizon:meter.charge();return state['mu'],False,old
    indices=horizon+1
    for other,cache in _CONTEXTS.items():
        if other is not context:indices+=cache['max_n']+1
        meter.charge()
    if indices>MAX_MU_INDICES:raise MemoryError('prospective ordinary-mu cache capacity')
    meter.charge(16*(horizon+1))
    mu=VALUES._mobius(horizon,meter)
    if state['mu'] is not None and not np.array_equal(mu[:old+1],state['mu']):raise ArithmeticError('extended ordinary mu changed')
    mu.setflags(write=False);state['mu']=mu;state['max_n']=horizon
    return mu,True,old


def _cofactor_count(t,subsets,meter):
    value=sum(sign*(t//product) for _,product,sign in subsets)
    meter.charge(4*len(subsets))
    if not 0<=value<=t:raise ArithmeticError('exact coprime inclusion-exclusion count')
    return value


def _finite(request,meter,context):
    alpha,primes,R,subsets,q,cs,N,horizon=_parameters(request,meter,True)
    state=_cache(context)
    if request['alpha'] not in state['alphas'] and len(state['alphas'])>=32:raise OverflowError('atom exponent cache capacity')
    existing=sum(len(s['atoms']) for s in _CONTEXTS.values())
    if existing+horizon>MAX_ATOMS:raise MemoryError('prospective shifted atom cache capacity')
    state['alphas'].add(request['alpha'])
    mu,recomputed,old=_mu(context,horizon,meter)
    center=down=up=new_atoms=hits=0
    p1=sum(cs)
    for d in range(1,horizon+1):
        meter.charge(8+len(primes))
        if mu[d]==0 or gcd(d,R)!=1:continue
        signed_count=sum(c*_cofactor_count((q**j*N)//d,subsets,meter) for j,c in enumerate(cs))
        # Removing n=1 is correlated with this very same log(R) atom.
        coefficient=-int(mu[d])*signed_count+(p1 if d==1 else 0)
        index=R*d
        if coefficient==0 or index==1:continue
        key=(request['alpha'],BITS,index)
        if key in state['atoms']:atom=state['atoms'][key];hits+=1;meter.charge()
        else:
            atom,precision=VALUES._atom(index,alpha,BITS,meter)
            if atom>index.bit_length()*(1<<BITS):raise ArithmeticError('shifted atom magnitude capacity')
            state['atoms'][key]=atom;new_atoms+=1
        center+=coefficient*atom
        if coefficient<0:down-=coefficient
        else:up+=coefficient
        if max(abs(center).bit_length(),down.bit_length(),up.bit_length())>8192:raise OverflowError('finite accumulation rational capacity')
    denominator=(1<<BITS)*alpha.numerator
    lo=Q((center-down)*alpha.denominator,denominator)
    hi=Q((center+up)*alpha.denominator,denominator)
    meter.charge(1+abs(center).bit_length()+down.bit_length()+up.bit_length())
    return lo,hi,{'cofactor_horizon':horizon,'maximum_shifted_index':R*horizon,
        'new_shifted_atoms':new_atoms,'reused_new_audit_atoms':hits,'mu_recomputed':recomputed,
        'previous_mu_horizon':old,'unit_correction_combined_before_rounding':True,
        'method':'complete coprime divisor floors with fresh shifted-log atoms and exact signed integer accumulation'}


def verify_filter_interval(request,proposal,meter=None,context=None):
    meter=Meter(cap=200_000_000_000,seconds=7200) if meter is None else meter
    _keys(proposal,('lower','upper'))
    lower=_output_rational(proposal['lower'],meter);upper=_output_rational(proposal['upper'],meter)
    if lower>upper:raise ValueError('ordered producer interval')
    if context is None:context=prepare_context(meter)
    lo,hi,rebuild=_finite(request,meter,context)
    if not lower<=lo<=hi<=upper:raise ValueError('independent shifted interval not contained in producer interval')
    return {'verified':True,'N':request['N'],'request':request,'lower':str(lo),'upper':str(hi),
        'dyadic_bits':BITS,'rebuild':rebuild,'finite_only':True,
        'uniform_bound_proved':False,'RH_proved':False,'RH_refuted':False,
        'archived_source_flags_used_as_authority':False,'producer_imported':False,
        'old_log_atoms_may_overlap_new_shifted_audit':True}


def verify_energy_recovery(request,certificate,meter=None):
    """Price source-free bases and recover target CONDITIONAL on an OPEN leaf."""
    meter=Meter() if meter is None else meter
    _keys(request,('alpha','features','coefficients','lambda','delta','C'))
    alpha=_rational(request['alpha'],meter)
    if not 0<alpha<1:raise ValueError('fractional original target')
    features=request['features'];a=request['coefficients']
    if type(features) is not list or not 1<=len(features)<=32 or features[0]!=[]:raise ValueError('first feature is original empty-set target')
    for primes in features:_parameters({'alpha':request['alpha'],'primes':primes},meter)
    if len({tuple(s) for s in features})!=len(features):raise ValueError('distinct source features')
    if type(a) is not list or len(a)!=len(features) or any(type(c) is not int or abs(c).bit_length()>1024 for c in a):raise ValueError('complete bounded integer auxiliary vector')
    lam=_rational(request['lambda'],meter);delta=_rational(request['delta'],meter);C=_rational(request['C'],meter)
    if min(lam,delta,C)<0:raise ValueError('nonnegative energy and recurrence parameters')
    terms=[]
    for i in range(len(a)):
        for j in range(i,len(a)):
            coefficient=lam*a[i]*a[j]*(1 if i==j else 2)+(1 if i==j==0 else 0)
            if coefficient:terms.append({'i':i,'j':j,'coefficient':str(coefficient)})
            meter.charge(8+abs(coefficient.numerator).bit_length()+coefficient.denominator.bit_length())
    base=Q(108,1)/alpha**2*(1+lam*sum(abs(c) for c in a)**2)
    constant=base+2*C/delta if delta>0 else base
    expected={'schema':'prime-insertion-energy-recovery-v1','request':request,
        'matrix_terms':terms,'base_upper':str(base),
        'recurrence':{'minimum':2,'children':[0,1],
            'formula':'F(2N+r)<=F(N)+C/N^delta','status':'OPEN'},
        'recovery':{'kind':'bounded' if delta>0 else 'logarithmic',
            'constant':str(constant),'log_coefficient':'0' if delta>0 else str(C),'logarithm_base':2},
        'uniform_drift_proved':False,'uniform_target_bound_proved':False,'RH_proved':False}
    _expect(certificate,expected);meter.charge(300+len(repr(expected)))
    return {'verified':True,'request':request,'source_free_base_proved':True,
        'target_domination_proved':True,'conditional_recovery_proved':True,
        'base_upper':str(base),'recovery':expected['recovery'],
        'recurrence_status':'OPEN','uniform_drift_proved':False,
        'uniform_target_bound_proved':False,'RH_proved':False,'RH_refuted':False,
        'scope':'original empty-set normalized q2P[2,-3,1] target; every integer N>=2, conditional on both children'}


def verify_insertion(request,certificate,meter=None):
    """Universal source-dependent identity and pointwise sign, no norm bound."""
    meter=Meter() if meter is None else meter
    alpha,primes,R,subsets=_parameters(request,meter)
    rows=[]
    for subset,product,sign in subsets:
        mask=sum(1<<primes.index(p) for p in subset)
        rows.append((mask,subset,product,sign));meter.charge(1+len(subset))
    rows.sort(key=lambda row:row[0])
    squares={mask:0 for mask,_,_,_ in rows}
    for mask,_,_,sign in rows:
        for other,_,_,other_sign in rows:
            squares[mask|other]+=sign*other_sign;meter.charge(4)
    cancellation=[]
    for mask,subset,product,mu in rows:
        total=sum(sign for upper,_,_,sign in rows if upper&mask==mask)
        cancellation.append({'primes':list(subset),'product':product,'mu':mu,
            'superset_sign_sum':total,'atom_coefficient':mu*total})
        if mu*total!=int(product==R):raise ArithmeticError('complete common atom cancellation')
        if squares[mask]!=mu:raise ArithmeticError('complete Boolean idempotence')
        meter.charge(4*len(rows))
    expected={'schema':'prime-insertion-boolean-certificate-v1','alpha':request['alpha'],
        'primes':primes,'product':R,'domain_minimum':2,
        'subset_terms':[{'primes':list(s),'product':p,'coefficient':sign} for _,s,p,sign in rows],
        'atom_cancellation_rows':cancellation,
        'square_reduction':[{'primes':list(s),'product':p,'coefficient':squares[mask]} for mask,s,p,_ in rows],
        'source_kernel':'K_alpha(n)=-sum_(d|n)mu(d)*(log d)^alpha',
        'source_condition':'actual ordinary-mu common atom function; radical invariance',
        'operator':'D_S=prod_(p in S)(I-E_p), E_p K(n)=K(p*n)',
        'boolean_relations':'E_p^2=E_p; D_p^2=D_p; distinct prime operators commute',
        'shared_prime_zero':'gcd(n,product)>1 implies D_S K(n)=0',
        'coprime_shift_identity':'D_S K(n)=-sum_(d|n)mu(d)*(log(product*d))^alpha',
        'quantized_shift_identity':'D_S K_center(n)=-sum_(d|n)mu(d)*floor(2^bits*(log(product*d))^alpha)',
        'coprime_upward_uncertainty':'K_up(n)',
        'coprime_downward_uncertainty':'K_down(n)+1_(product>1)',
        'prefix_definition':'B_S(X)=sum_(2<=n<=X)D_S K(n)',
        'shifted_prefix_unit_correction':'+(log(product))^alpha; zero for empty set',
        'unit_n1_excluded':True,'empty_set_identity':True,
        'normal_form':'sorted distinct prime set; repeated insertions collapse',
        'source_chain_replayed_here':False,'all_scale_bound_proved':False,'new_atoms_evaluated':0}
    _expect(certificate,expected);meter.charge(len(repr(expected))+100)
    return {'verified':True,'request':request,'source_identity_proved':True,
        'pointwise_nonnegative_proved':True,'pointwise_dominance_by_original_K_proved':True,
        'strict_positive_scope':'n>=2 and gcd(n,product)=1',
        'unit_value':'-(log(product))^alpha; exactly0 for empty set',
        'operator_scope':'ordinary-mu K and radical-invariant states, not arbitrary sequences',
        'uniform_prefix_bound_proved':False,'RH_proved':False,'RH_refuted':False,
        'proof_backend':'independently reviewed exact finite algebra and positive fractional integral'}


def verify_tail_bound(request,certificate,meter=None):
    """Uniform exact-source Laplace tail; small-t signed core remains OPEN."""
    meter=Meter() if meter is None else meter
    _keys(request,('alpha','primes','tau'))
    alpha,primes,R,subsets=_parameters({'alpha':request['alpha'],'primes':request['primes']},meter)
    tau=request['tau']
    if type(tau) is not int or not 2<=tau<=256:raise ValueError('fixed integer Laplace threshold2..256')
    # On each unit interval W is0,1,-1,0 on the four quarter-cells.
    # P(1)=0 removes the excluded unit. W(N)=0 (integerN) removes
    # d=1 only for R=1. Every cofactor divisor remains when R>1.
    upper=Q(18,2**tau) if not primes else Q(12*2**len(primes),R**tau)
    meter.charge(100+len(subsets)+tau*R.bit_length())
    expected={'schema':'prime-insertion-laplace-tail-v1','request':request,
        'product':R,'integer_N_minimum':2,
        'filter':{'q':2,'coefficients':[2,-3,1],'normalization':'divide_by_alpha'},
        'integrand':'R^-t*sum_(d<=4N,gcd(d,R)=1)mu(d)*d^-t*sum_(e|R)mu(e)*W(N/(d*e))',
        'W':'floor(4y)-3floor(2y)+2floor(y)',
        'normalizer':'1/(alpha*I_alpha)',
        'uniform_absolute_upper':str(upper),'unpaid_core':'0<t<tau',
        'tail_bound_proved':True,'complete_target_bound_proved':False,'RH_proved':False}
    _expect(certificate,expected);meter.charge(100+len(repr(expected)))
    return {'verified':True,'request':request,'uniform_absolute_upper':str(upper),
        'tail_bound_proved':True,'domain':'every integer N>=2, t>=tau only',
        'complete_target_bound_proved':False,'RH_proved':False,'RH_refuted':False,
        'unpaid_core':'0<t<tau','full_energy_tail_crosses_must_be_retained':True,
        'source_values_evaluated':False,
        'proof':'exact filtered coprime-divisor integral; quarter-cell W; elementary zeta-tail and normalizer bounds'}

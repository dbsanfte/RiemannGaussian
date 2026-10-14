"""Independent exact signed-mixture, moving-drift and coefficient admission.

No new producer imports, source arrays or whole residual norm evaluations.
"""
from fractions import Fraction as Q
from math import factorial

MAX_RATIONAL_BITS=4096
MAX_POWER_BITS=400000

class Meter:
    def __init__(self,cap=50000000):self.cap=cap;self.operations=0
    def charge(self,n=1):
        if type(n) is not int or n<0 or n>self.cap-self.operations:raise OverflowError('drift checker work cap')
        self.operations+=n

def _meter(m):return Meter() if m is None else m

def rational(s,meter=None):
    meter=_meter(meter)
    if type(s) is not str or not 1<=len(s)<=2500:raise ValueError('canonical rational text')
    try:v=Q(s)
    except (ValueError,ZeroDivisionError):raise ValueError('rational') from None
    if str(v)!=s or max(abs(v.numerator).bit_length(),v.denominator.bit_length())>MAX_RATIONAL_BITS:
        raise ValueError('canonical rational bit cap')
    meter.charge(len(s)+1);return v

def _eq(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(_eq(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(_eq(x,y) for x,y in zip(a,b))
    return a==b

def _power(n,k,m):
    if type(n) is not int or n<0 or type(k) is not int or k<0:raise ValueError('integer power')
    bits=max(1,n.bit_length())*k
    if bits>MAX_POWER_BITS:raise ValueError('exact integer power resource cap')
    m.charge(max(1,bits)*max(1,k.bit_length()));return n**k

def _integer(n,minimum=1):
    if type(n) is not int or n<minimum or n.bit_length()>4096:raise ValueError('bounded positive integer')
    return n

def parse_spec(spec,meter=None):
    m=_meter(meter)
    if type(spec) is not dict or set(spec)!={'kind','a','theta','terms'} or spec['kind']!='drift_mixture':
        raise ValueError('exact drift mixture schema')
    a=rational(spec['a'],m);theta=rational(spec['theta'],m)
    if a<=0 or not 0<theta<1:raise ValueError('positive drift and strict fractional theta')
    rows=spec['terms']
    if type(rows) is not list or not 1<=len(rows)<=8:raise ValueError('one through eight signed terms')
    terms=[];prior=Q(0)
    for row in rows:
        if type(row) is not dict or set(row)!={'rate','weight'}:raise ValueError('mixture term schema')
        rate=rational(row['rate'],m);weight=rational(row['weight'],m)
        if rate<=prior or not weight:raise ValueError('sorted distinct positive rates, nonzero weights')
        terms.append((rate,weight));prior=rate
    if sum((w for _,w in terms),Q(0))!=1:raise ValueError('unit zeroth moment')
    return a,theta,terms

def moments(spec,meter=None):
    m=_meter(meter);a,theta,terms=parse_spec(spec,m)
    values=[]
    for k in range(len(terms)+1):
        value=sum((w*r**k for r,w in terms),Q(0))
        if max(abs(value.numerator).bit_length(),value.denominator.bit_length())>65536:raise ValueError('moment intermediate cap')
        m.charge(100*len(terms)*(k+1));values.append(value)
    order=next((k for k in range(1,len(values)) if values[k]),None)
    if order is None:raise ValueError('impossible positive-rate moment identity')
    return a,theta,terms,values,order

def beta(a_text,theta_text,N,meter=None):
    """Replay ceil by integer inequalities; no float/Arb root decisions."""
    m=_meter(meter);a=rational(a_text,m);theta=rational(theta_text,m)
    _integer(N,2)
    if a<=0 or not 0<theta<1:raise ValueError('finite drift domain')
    L=N.bit_length();u,v=theta.numerator,theta.denominator
    if v*(a.numerator.bit_length()+a.denominator.bit_length())+u*L.bit_length()>MAX_POWER_BITS:
        raise ValueError('ceiling prospective bit cap')
    lhs_factor=_power(a.denominator,v,m)
    rhs=_power(a.numerator,v,m)*_power(L,u,m)
    if rhs.bit_length()>MAX_POWER_BITS:raise ValueError('ceiling comparison cap')
    def ge(z):return _power(z,v,m)*lhs_factor>=rhs
    lo=0;hi=1
    while not ge(hi):lo=hi;hi*=2;m.charge(5)
    while hi-lo>1:
        mid=(lo+hi)//2
        if ge(mid):hi=mid
        else:lo=mid
        m.charge(5)
    return Q(hi,L)

def rounded_twist(n,exponent,p,meter=None):
    m=_meter(meter)
    _integer(n)
    if type(exponent) is not Q or exponent<=0 or type(p) is not int or not 1<=p<=16384:
        raise ValueError('exact finite twist domain')
    u,v=exponent.numerator,exponent.denominator
    if p*v+u*max(1,n.bit_length())>MAX_POWER_BITS:raise ValueError('twist power comparison cap')
    target=1<<(p*v);factor=_power(n,u,m)
    lo=0;hi=(1<<p)+1
    while hi-lo>1:
        mid=(lo+hi)//2
        if _power(mid,v,m)*factor<=target:lo=mid
        else:hi=mid
        m.charge(5)
    return Q(lo,1<<p)

def mixture_value(spec,n,N,meter=None):
    m=_meter(meter);_,_,terms=parse_spec(spec,m);b=beta(spec['a'],spec['theta'],N,m)
    _integer(n)
    p=4*(N-1).bit_length()
    return sum((w*rounded_twist(n,r*b,p,m) for r,w in terms),Q(0))

def mobius(n,meter=None):
    m=_meter(meter)
    if type(n) is not int or not 1<=n<=4096:raise ValueError('exact scalar source index')
    parity=0;p=2
    while p*p<=n:
        m.charge(10)
        if n%p==0:
            n//=p;parity+=1
            if n%p==0:return 0
        p+=1
    if n>1:parity+=1
    return (-1)**parity

def _poly_mul(p,r,m):
    out=[Q(0)]*(len(p)+1)
    for k,c in enumerate(p):out[k]+=c*r;out[k+1]+=c;m.charge(10)
    return out

def survival_identity(terms,meter=None):
    """Exact numerator test for -Laplace(P')=prod r/(s+r)."""
    m=_meter(meter);left=[Q(0)]*len(terms)
    for i,(r,w) in enumerate(terms):
        p=[Q(1)]
        for j,(s,_) in enumerate(terms):
            if i!=j:p=_poly_mul(p,s,m)
        for k,c in enumerate(p):left[k]+=w*r*c;m.charge(10)
    right=[Q(1)]+[Q(0)]*(len(terms)-1)
    for r,_ in terms:right[0]*=r;m.charge(10)
    return left,right,left==right

# Frozen independent primitives: exact cell columns and logarithmic sign gates.
# This does not import any new producer or replay an earlier search.
import check_floor_residual_rates_044 as OLD

def _has_drift(weight,depth=0):
    if type(weight) is not dict or depth>6:raise ValueError('bounded typed weight')
    if weight.get('kind')=='drift_mixture':return True
    if weight.get('kind')=='product':
        if set(weight)!={'kind','left','right'}:raise ValueError('product schema')
        return _has_drift(weight['left'],depth+1) or _has_drift(weight['right'],depth+1)
    return False

def _add_series(a,b):
    if a[0]=='flat':return b
    if b[0]=='flat':return a
    if a[0]=='UNRESOLVED' or b[0]=='UNRESOLVED':
        barrier=min(Q(s[3]) for s in (a,b) if s[0]=='UNRESOLVED')
        leading=[s for s in (a,b) if s[0]=='leading']
        if leading and leading[0][1]<=barrier:return leading[0]
        return ('UNRESOLVED',None,{},str(barrier))
    nu=min(a[1],b[1]);poly={}
    for series in (a,b):
        if series[1]==nu:
            for key,c in series[2].items():poly[key]=poly.get(key,Q(0))+c
    poly={key:c for key,c in poly.items() if c}
    return ('leading',nu,poly,None) if poly else ('UNRESOLVED',None,{},str(nu))

def weight_series(weight,meter=None,depth=0):
    """Independent first correction P-1; product constants stay signed."""
    m=_meter(meter);m.charge(20)
    if type(weight) is not dict or depth>6:raise ValueError('bounded typed weight')
    if weight.get('kind')=='drift_mixture':
        a,theta,_,values,order=moments(weight,m)
        coefficient=Q((-1)**order,factorial(order))*values[order]*a**order
        return ('leading',order*(1-theta),{(Q(order),Q(0)):coefficient},None)
    if weight.get('kind')=='product':
        if set(weight)!={'kind','left','right'}:raise ValueError('product schema')
        return _add_series(weight_series(weight['left'],m,depth+1),weight_series(weight['right'],m,depth+1))
    return OLD.weight_series(weight,m,depth)

def verify_rate_candidate(recipe,index,row,precision=192,meter=None):
    """Admit one source-bound044-compatible obstruction, never an upper bound."""
    m=_meter(meter)
    if type(recipe) is not dict or set(recipe)!={'id','base','auxiliary'} or type(recipe['id']) is not str or not 1<=len(recipe['id'])<=100:
        raise ValueError('recipe schema')
    if not _has_drift(recipe['base']):return OLD.verify_candidate(recipe,index,row,precision,m)
    if recipe['auxiliary'] is not None:raise ValueError('new drift source scope requires null auxiliary')
    if type(index) is not int or not 2<=index<=64 or type(precision) is not int or not 128<=precision<=4096:
        raise ValueError('bounded index/precision')
    series=weight_series(recipe['base'],m);mu=mobius(index,m)
    if not mu:series=('flat',None,{},None)
    elif series[0]=='leading':series=(series[0],series[1],{key:-mu*c for key,c in series[2].items()},series[3])
    if index==2 and series[0]=='leading':
        poly={}
        for (a,b),c in series[2].items():poly[(Q(0),a+b)]=poly.get((Q(0),a+b),Q(0))+c
        poly={key:c for key,c in poly.items() if c}
        series=('leading',series[1],poly,None) if poly else ('UNRESOLVED',None,{},str(series[1]))
    keys={'index','mu','auxiliary_arithmetic','expansion','coefficient_limit_is_compatible','status','nonzero_license','witness','energy_rate','asymptotic_norm_lower'}
    if type(row) is not dict or set(row)!=keys or type(row['index']) is not int or row['index']!=index:
        raise ValueError('source rate candidate schema')
    if type(row['mu']) is not int or row['mu']!=mu or row['auxiliary_arithmetic'] is not None or row['coefficient_limit_is_compatible'] is not True:
        raise ValueError('ordinary Mobius source binding')
    OLD._expansion(series,row['expansion'])
    OLD.verify_witness(row['witness'],m)
    if row['witness']['index']!=index:raise ValueError('witness/source index mismatch')
    licensed=False
    if series[0]=='leading':licensed=OLD._license(series[2],index,row['nonzero_license'],precision,m)
    elif row['nonzero_license'] is not None:raise ValueError('nonzero license on zero or cancelled coefficient')
    status='certified_rate_obstruction' if licensed else 'OPEN' if series[0]=='flat' else 'UNRESOLVED'
    rate=str(2*series[1]) if licensed else None
    lower='liminf L^(2*nu)*norm_squared >= leading_coefficient^2/witness.denominator' if licensed else None
    if row['status']!=status or row['energy_rate']!=rate or row['asymptotic_norm_lower']!=lower:
        raise ValueError('unlicensed obstruction/signed local rate')
    return {'verified':True,'index':index,'energy_rate':rate,'necessary_obstruction_only':True,
      'convergence_proved':False,'uniform_upper_bound_proved':False,'RH_proved':False,'RH_refuted':False}

_COUNT_KEYS={'operations','root_comparisons','ceil_comparisons','rational_operations','root_cache_hits','max_power_bits','total_power_bit_estimates'}
def _counts(row):
    if type(row) is not dict or set(row)!=_COUNT_KEYS or any(type(v) is not int or v<0 for v in row.values()):
        raise ValueError('nonnegative metered counter metadata')

def _admit(proposal,expected):
    if type(proposal) is not dict or set(proposal)!=set(expected)|{'counts'}:
        raise ValueError('exact certificate schema')
    if not _eq({k:proposal[k] for k in expected},expected):raise ValueError('certificate arithmetic or scope differs')
    _counts(proposal['counts'])

def _kernel_expected(terms,m):
    numerator,expected,certified=survival_identity(terms,m)
    denominator=[Q(1)];summands=[]
    for r,_ in terms:denominator=_poly_mul(denominator,r,m)
    for i,(r,w) in enumerate(terms):
        p=[r*w]
        for j,(s,_) in enumerate(terms):
            if i!=j:p=_poly_mul(p,s,m)
        summands.append([str(v) for v in p])
    return {'schema':'floor-drift-exponential-kernel-v1','status':'certified' if certified else 'NOT_CERTIFIED',
      'denominator_polynomial_ascending':[str(v) for v in denominator],
      'numerator_summands_ascending':summands,'numerator_polynomial_ascending':[str(v) for v in numerator],
      'expected_numerator_ascending':[str(v) for v in expected],'rate_product':str(expected[0]),
      'kernel_order':len(terms),'identity':'sum_j w_j*r_j/(s+r_j)=product_j r_j/(s+r_j)',
      'raw_range':['0','1'] if certified else None,
      'raw_simplex_bound':'0<=1-P(u)<=product(r)*u^order/order!' if certified else None,
      'rounded_range_proved':False}

def verify_spec(spec,meter=None):
    m=_meter(meter);a,theta,terms,values,order=moments(spec,m)
    kernel=_kernel_expected(terms,m)
    return {'verified':True,'order':order,'coefficient_rate':str(order*(1-theta)),
      'energy_rate':str(2*order*(1-theta)),'raw_range_proved':kernel['status']=='certified',
      'coefficient_compatibility_proved':True,'rounded_range_proved':False,
      'whole_signed_norm_proved':False,'uniform_forcing_bound_proved':False,
      'norm_convergence_proved':False,'RH_proved':False,'RH_refuted':False}

def verify_certificate(spec,proposal,meter=None):
    m=_meter(meter);a,theta,terms,values,order=moments(spec,m)
    absw=sum((abs(w) for _,w in terms),Q(0));absm=sum((abs(w)*r**order for r,w in terms),Q(0))
    leading=Q((-1)**(order+1),factorial(order))*values[order]*a**order;rate=order*(1-theta)
    expected={'schema':'floor-drift-mixture-certificate-v1','spec':spec,'order':order,
      'moments':[{'k':k,'value':str(v)} for k,v in enumerate(values)],
      'vanishing_orders':list(range(1,order)),'leading_moment':str(values[order]),
      'sum_abs_weights':str(absw),'weighted_abs_order_moment':str(absm),
      'leading_error_coefficient':{'rational':str(leading),'log_n_power':str(order)},
      'coefficient_rate':str(rate),'energy_rate':str(2*rate),
      'local_expansion':'1-P(n,N)=leading_rational*log(n)^order*L^(-coefficient_rate)+o(L^(-coefficient_rate)), fixed n>=2',
      'beta_asymptotic':'beta_N/(a*L^(theta-1))->1; beta_N->0; beta_N*log(N)->infinity',
      'rounding_policy':'p=4*ceil(log2(N)); each n^(-rate*beta) rounded down independently',
      'rounding_error':'abs(P_exact-P_rounded)<=2^(-p)*sum_abs_weights',
      'taylor_bound':'abs(1-P_exact)<=u^order/order!*weighted_abs_order_moment, u=beta_N*log(n)>=0',
      'kernel_certificate':_kernel_expected(terms,m),'coefficient_control_only':True,
      'whole_signed_norm_proved':False,'uniform_forcing_bound_proved':False,'norm_convergence_proved':False,
      'RH_proved':False,'RH_refuted':False,'additional_norms_evaluated':False,'source_arrays_read':False}
    _admit(proposal,expected)
    return {'verified':True,'order':order,'coefficient_rate':str(rate),'energy_rate':str(2*rate),
      'raw_range_proved':expected['kernel_certificate']['status']=='certified','rounded_range_proved':False,
      'whole_signed_norm_proved':False,'uniform_forcing_bound_proved':False,'norm_convergence_proved':False,
      'RH_proved':False,'RH_refuted':False}

def verify_obstruction(spec,proposal,meter=None):
    """Symbolic local order, with actual-source admission in verify_rate_candidate."""
    out=verify_certificate(spec,proposal,meter)
    out['fixed_index_coefficient_order_only']=True
    out['actual_source_obstruction_requires_cell_witness']=True
    return out

def _beta_expected(spec,N,m):
    a,theta,_=parse_spec(spec,m);b=beta(spec['a'],spec['theta'],N,m);L=N.bit_length();z=b*L
    if z.denominator!=1:raise ArithmeticError('integer ceiling')
    hi=(a.numerator*L+a.denominator-1)//a.denominator;u,v=theta.numerator,theta.denominator
    estimate=max(v*max(hi.bit_length(),a.denominator.bit_length())+v*a.denominator.bit_length(),
      v*a.numerator.bit_length()+u*L.bit_length())+4
    if estimate>MAX_POWER_BITS:raise ValueError('producer ceiling resource cap')
    return {'schema':'floor-drift-beta-v1','a':spec['a'],'theta':spec['theta'],'N':N,'L':L,
      'ceiling':str(z.numerator),'beta':str(b),
      'comparison':{'theta_numerator':str(u),'theta_denominator':str(v),
        'a_numerator':str(a.numerator),'a_denominator':str(a.denominator),
        'lower_is_strict':True,'upper_is_nonstrict':True},'power_bit_estimate':estimate},b

def verify_compilation(spec,n,N,proposal,meter=None):
    m=_meter(meter);_,_,terms=parse_spec(spec,m);_integer(n);_integer(N,2)
    bc,b=_beta_expected(spec,N,m);p=4*(N-1).bit_length();rows=[];value=Q(0)
    for r,w in terms:
        exponent=r*b;rounded=rounded_twist(n,exponent,p,m)
        estimate=p*exponent.denominator+exponent.numerator*n.bit_length()+4
        if estimate>MAX_POWER_BITS:raise ValueError('compiler comparison cap')
        rows.append({'rate':str(r),'weight':str(w),'exponent':str(exponent),
          'rounded_value':str(rounded),'power_bit_estimate':estimate});value+=w*rounded
    rounding=sum((abs(w) for _,w in terms),Q(0))/2**p
    if type(proposal) is str:
        if rational(proposal,m)!=value:raise ValueError('wrong exact compiled value')
    else:
        expected={'schema':'floor-drift-compilation-v1','spec':spec,'n':n,'N':N,
          'beta_certificate':bc,'precision_bits':p,'terms':rows,'value':str(value),
          'rounding_error_bound':str(rounding),'signs_retained':True,'exact_rounded_range_claim':None}
        _admit(proposal,expected)
    return {'verified':True,'value':str(value),'beta':str(b),'precision_bits':p,
      'signs_retained':True,'exact_rounded_range_proved':False,'whole_signed_norm_proved':False,'RH_proved':False}

def verify_coefficient_bound(spec,n,N,proposal,meter=None):
    m=_meter(meter);a,theta,terms,values,order=moments(spec,m);_integer(n);_integer(N,2)
    bc,b=_beta_expected(spec,N,m);p=4*(N-1).bit_length();logupper=(n-1).bit_length();u=b*logupper
    absw=sum((abs(w) for _,w in terms),Q(0));absm=sum((abs(w)*r**order for r,w in terms),Q(0))
    taylor=u**order*absm/factorial(order);kernel=_kernel_expected(terms,m)
    simplex=u**order*Q(kernel['rate_product'])/factorial(order) if kernel['status']=='certified' else None
    if simplex is not None and order!=len(terms):raise ArithmeticError('survival moment order')
    raw=min(taylor,simplex,Q(1)) if simplex is not None else taylor
    rounding=absw/2**p if n!=1 else Q(0)
    expected={'schema':'floor-drift-coefficient-bound-v1','spec':spec,'n':n,'N':N,
      'beta_certificate':bc,'precision_bits':p,'order':order,'log_upper_bound':str(logupper),
      'u_upper_bound':str(u),'taylor_error_bound':str(taylor),'simplex_error_bound':None if simplex is None else str(simplex),
      'raw_error_bound':str(raw),'rounding_error_bound':str(rounding),'total_error_bound':str(raw+rounding),
      'bound':'abs(1-P_rounded(n,N))<=total_error_bound','coefficient_control_only':True,
      'whole_signed_norm_proved':False,'uniform_forcing_bound_proved':False,'norm_convergence_proved':False,
      'RH_proved':False,'RH_refuted':False}
    _admit(proposal,expected)
    return {'verified':True,'total_error_bound':str(raw+rounding),'coefficient_control_only':True,
      'whole_signed_norm_proved':False,'norm_convergence_proved':False,'RH_proved':False}

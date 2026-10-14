"""Independent all-integer sign and pointwise-size admission for051 kernels.

Only exact rational syntax and licensed elementary inclusion-exclusion,
calculus and Laplace identities are admitted. No new producer imports,
coefficient observations, analytic continuation or global norm claims.
"""
from fractions import Fraction as Q
import math
import time


class Meter:
    def __init__(self,cap=50000000,seconds=180):
        if type(cap) is not int or cap<0:raise ValueError('nonnegative work cap')
        if type(seconds) not in (int,float) or not math.isfinite(seconds) or seconds<=0:raise ValueError('positive finite deadline')
        self.cap=cap;self.operations=0;self.deadline=time.monotonic()+seconds
    def charge(self,n=1):
        if type(n) is not int or n<0 or n>self.cap-self.operations:raise OverflowError('fractional kernel work cap')
        self.operations+=n
        if time.monotonic()>self.deadline:raise TimeoutError('fractional kernel deadline')


def _meter(m):return Meter() if m is None else m

def _same(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return set(a)==set(b) and all(_same(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(_same(x,y) for x,y in zip(a,b))
    return a==b

def _expect(a,b):
    if not _same(a,b):raise ValueError('fractional kernel theorem, binding or scope mismatch')

def _fields(obj,keys):
    if type(obj) is not dict or set(obj)!=set(keys):raise ValueError('exact fractional kernel schema')

def _rational(text,m):
    if type(text) is not str or not 1<=len(text)<=2500:raise ValueError('canonical rational text')
    try:value=Q(text)
    except (ValueError,ZeroDivisionError):raise ValueError('rational') from None
    if str(value)!=text or max(abs(value.numerator).bit_length(),value.denominator.bit_length())>4096:
        raise ValueError('canonical rational capacity')
    m.charge(len(text)+1);return value

def _request(request,m):
    _fields(request,('a','b','alpha','sign'))
    a,b,alpha=(_rational(request[key],m) for key in ('a','b','alpha'))
    sign=request['sign']
    if a<0 or b<0 or a+b!=1 or a==b or not 0<alpha<=2 or type(sign) is not int or sign not in (-1,1):
        raise ValueError('a,b>=0,a+b=1,a!=b,0<alpha<=2 and strict sign +/-1')
    m.charge(1+a.denominator.bit_length()+b.denominator.bit_length()+alpha.denominator.bit_length())
    return a,b,alpha,sign


def _factor(n,m):
    if type(n) is not int or n<1:raise ValueError('positive integer factorization')
    factors=[];p=2
    while p*p<=n:
        e=0
        while n%p==0:n//=p;e+=1;m.charge(8)
        if e:factors.append((p,e))
        p+=1;m.charge(8)
    if n>1:factors.append((n,1))
    return factors


def _classification(a,b,alpha,sign):
    """Derived solely from finite-difference derivative signs."""
    c=a-b
    if alpha<1 and c>0 and sign==-1:return 'fractional_forward_positive',None
    if alpha==1 and sign*(b-a)>0:return 'linear_positive',None
    if alpha==2 and c<0 and sign==1:return 'quadratic_backward_positive',None
    # At a prime the raw difference has sign -c for every positive alpha.
    if sign*c>0:return 'strict_negative_witness',2
    # The remaining forward alpha>1 case has a positive second difference,
    # reversed by sign-1. Reverse alpha<1 has a negative second difference.
    if c>0 or alpha<1:return 'strict_negative_witness',6
    # Reverse alpha in(1,2) has a negative third difference. Alpha2 reverse
    # sign+ is already admitted above; no unlicensed boundary remains.
    return 'strict_negative_witness',30


def _common(request):
    return {'schema':'fractional-prime-kernel-proof-v1','request':request,
        'formula':'K(n)=sign*sum_{d|n}mu(d)*(a*log(d)+b*log(n/d))^alpha',
        'domain':{'n':'every ordinary integer n>=2','extension_at_one':'K(1)=0',
            'parameters':'fixed exact request; theorem holds for every admitted parameter in its licensed branch',
            'rounding':'none; exact real logarithms and powers;0^alpha=0'},
        'divisor_reduction':{'kind':'squarefree_divisor_boolean_cube',
            'variables':'C=b*log(n), h_p=(a-b)*log(p), for every distinct ordinary prime p|n',
            'identity':'sum_{d|n}mu(d)*f(C+(a-b)*log(d))=sum_{S subset primes(n)}(-1)^|S|*f(C+sum_{p in S}h_p)',
            'prime_powers_retained_in':'C=b*log(n)','all_distinct_prime_factors_retained':True},
        'proof_backend':'reviewed exact calculus and finite divisor identities; no proof-assistant formalization',
        'arithmetic_source':'ordinary Mobius function and actual ordinary prime divisors',
        'source_values_evaluated':False,'numerical_evidence_used':False,
        'prime_distribution_bound_proved':False,'uniform_mobius_partial_sum_bound_proved':False,
        'original_floor_energy_bound_proved':False,'analytic_continuation_proved':False,
        'RH_proved':False,'RH_refuted':False}


def _fractional(a,b,alpha):
    """All differences are negative before orientation; integrand is positive.

    Integration by parts gives I_alpha=Gamma(1-alpha)/alpha. The Boolean
    product vanishes to order omega(n)>alpha at0 and is bounded at infinity.
    Dropping all but one factor pays the increment. The k-fold fundamental
    theorem pays the derivative product only when b>0; AMGM pays the ratio.
    """
    c=a-b
    product=None
    if b>0:
        product={'kind':'mixed_derivative_product','k':'omega(n)',
            'coefficient':'alpha*prod_{j=1}^{k-1}(j-alpha)',
            'formula':'K(n)<=alpha*prod_{j=1}^{k-1}(j-alpha)*c^k*prod_{p|n}log(p)/(b*log(n))^(k-alpha)',
            'factor_count_bound':'K(n)/log(n)^alpha<=alpha*prod_{j=1}^{k-1}(j-alpha)*c^k*b^(alpha-k)/k^k',
            'omega_upper':'K(n)/log(n)^alpha<=2*alpha*b^alpha*(c/(2*b))^k/k',
            'omega_ratio':str(c/(2*b)),'exponential_omega_decay':bool(c<2*b),'b_strictly_positive':True}
    return {'status':'PAID_UNIFORM_POINTWISE_CONTROL','branch':'fractional_forward',
        'nonnegative_for_all_n':True,'strict_positive_scope':'every integer n>=2','exact_zero_scope':'none for n>=2',
        'identity':{'kind':'normalized_positive_laplace_prime_product','c':str(c),
            'normalizer':'I_alpha=integral_0^infinity (1-exp(-u))*u^(-alpha-1) du',
            'normalizer_finite_positive':True,
            'formula':'K(n)=I_alpha^(-1)*integral_0^infinity n^(-b*t)*prod_{p|n}(1-p^(-c*t))*t^(-alpha-1) dt'},
        'upper_bound':{'kind':'minimum_prime_increment','offset_coefficient':str(b),
            'step_coefficient':str(c),'power':str(alpha),
            'formula':'K(n)<=min_{p|n}[(b*log(n)+c*log(p))^alpha-(b*log(n))^alpha]',
            'weaker_bound':'K(n)<=(c*log(p_min))^alpha'},'product_bound':product,
        'proof':{'kind':'concave_power_laplace_and_boolean_product','finite_difference_constant_cancels':True,
            'one_factor_dominance':True,'all_factors_between_zero_and_one':True,
            'upper_bound_includes_all_prime_powers':True},
        'zeta_bridge':{'kind':'fractional_zeta_quotient_integral','numerator_shift':str(b),
            'denominator_shift':str(a),'subtracted_constant':'1',
            'formula':'sum K(n)/n^s=I_alpha^(-1)*integral_0^infinity [zeta(s+b*t)/zeta(s+a*t)-1]*t^(-alpha-1) dt',
            'domain':'Re(s)>1','absolute_convergence_proved':True,
            'justification':'K(n)<=(c*log(n))^alpha; absolute Dirichlet convergence, positive real Tonelli and complex domination'}}


def _linear(a,b):
    c=abs(a-b)
    # The first difference is sign*(b-a)*Lambda. This branch has a positive
    # orientation, so the coefficient equals abs(a-b); mixed differences0.
    return {'status':'PAID_UNIFORM_POINTWISE_CONTROL','branch':'linear_endpoint',
        'nonnegative_for_all_n':True,'strict_positive_scope':'exactly the ordinary prime powers',
        'exact_zero_scope':'integers with at least two distinct prime factors',
        'identity':{'kind':'von_mangoldt','coefficient':str(c),'formula':'K(n)=c*Lambda(n)'},
        'upper_bound':{'kind':'minimum_prime_logarithm','coefficient':str(c),'power':'1'},
        'proof':{'kind':'boolean_difference_of_linear_function','unit_cancellation':True,
            'mixed_differences_order_two_or_more_zero':True},
        'zeta_bridge':{'kind':'logarithmic_derivative','coefficient':str(c),
            'formula':'sum K(n)/n^s=-c*zeta_prime(s)/zeta(s)','domain':'Re(s)>1',
            'absolute_convergence_proved':True}}


def _quadratic(a,b):
    c=b-a
    # Logarithmic differentiation of mu*One=delta gives the exact identity
    # c*Lambda*log +c²(Lambda*Lambda); both terms are nonnegative. The exact
    # prime-power and two-prime cases give the pointwise upper c*log(n)².
    return {'status':'PAID_UNIFORM_POINTWISE_CONTROL','branch':'quadratic_backward',
        'nonnegative_for_all_n':True,'strict_positive_scope':'exactly omega(n)=1 or2',
        'exact_zero_scope':'omega(n)>=3',
        'identity':{'kind':'positive_mangoldt_convolution','c':str(c),
            'formula':'K(n)=c*Lambda(n)*log(n)+c^2*(Lambda*Lambda)(n)',
            'prime_power':'K(p^e)=c*(2*b*e-c)*log(p)^2',
            'two_distinct_primes':'K(p^e*q^f)=2*c^2*log(p)*log(q), e,f>=1'},
        'upper_bound':{'kind':'full_logarithmic_power','coefficient':str(c),'power':'2',
            'formula':'K(n)<=c*log(n)^2'},
        'proof':{'kind':'boolean_difference_of_quadratic_function','cubic_mixed_differences_zero':True,
            'prime_power_coefficient_positive':True,'pair_coefficient_positive':True,'a_plus_b_equals_one':True},
        'zeta_bridge':{'kind':'quadratic_logarithmic_derivative','coefficient':str(c),
            'formula':'sum K(n)/n^s=c*(zeta_prime/zeta)_prime(s)+c^2*(zeta_prime(s)/zeta(s))^2',
            'domain':'Re(s)>1','absolute_convergence_proved':True}}


def _negative(a,b,alpha,sign,n,m):
    # Exact derivative signs license the witness; floating logarithm or gamma
    # values play no role. Endpoints1/2 were already classified separately.
    factors=_factor(n,m)
    if any(e!=1 for _,e in factors):raise ArithmeticError('squarefree witness')
    if n==2:
        if sign*(b-a)>=0:raise ArithmeticError('wrong prime sign witness')
        branch='negative_prime';reason='sign*(b^alpha-a^alpha)<0 since alpha>0'
    elif n==6 and a>b:
        if not alpha>1 or sign!=-1:raise ArithmeticError('wrong second-difference convex witness')
        branch='negative_two_prime_convex';reason='sign=-1 and strictly positive second difference of x^alpha for alpha>1'
    elif n==6:
        if not alpha<1 or sign!=1:raise ArithmeticError('wrong backward concave witness')
        branch='negative_two_prime_concave';reason='sign=+1 and strictly negative backward second difference of x^alpha for0<alpha<1'
    else:
        if n!=30 or not a<b or sign!=1 or not 1<alpha<2:raise ArithmeticError('wrong third-difference witness')
        branch='negative_three_prime';reason='sign=+1 and strictly negative backward third difference of x^alpha for1<alpha<2'
    return {'status':'REFUTED_UNIFORM_NONNEGATIVITY','branch':branch,'nonnegative_for_all_n':False,
        'witness':{'n':n,'primes':[p for p,_ in factors],'conclusion':'K(n)<0','proof':reason,
            'exact_sign_proved':True,'numerical_evaluation_required':False},
        'scope':'refutes nonnegativity of this kernel, not any original RH bound',
        'uniform_pointwise_upper_bound_claimed':False}


def verify_certificate(request,certificate,meter=None):
    """Admit complete symbolic pointwise rules, never a global RH bound."""
    m=_meter(meter);a,b,alpha,sign=_request(request,m)
    classification,witness=_classification(a,b,alpha,sign)
    if classification=='fractional_forward_positive':specific=_fractional(a,b,alpha)
    elif classification=='linear_positive':specific=_linear(a,b)
    elif classification=='quadratic_backward_positive':specific=_quadratic(a,b)
    else:specific=_negative(a,b,alpha,sign,witness,m)
    expected=_common(request);expected.update(specific)
    _expect(certificate,expected);m.charge(100+len(specific)*8)
    return {'verified':True,'status':specific['status'],'branch':specific['branch'],
        'uniform_pointwise_control_proved':specific['status']=='PAID_UNIFORM_POINTWISE_CONTROL',
        'uniform_nonnegativity_refuted':specific['status']=='REFUTED_UNIFORM_NONNEGATIVITY',
        'source_values_evaluated':False,'numerical_evidence_used':False,
        'prime_distribution_bound_proved':False,'uniform_mobius_partial_sum_bound_proved':False,
        'original_floor_energy_bound_proved':False,'analytic_continuation_proved':False,
        'RH_proved':False,'RH_refuted':False}


def verify(request,certificate,meter=None):return verify_certificate(request,certificate,meter)

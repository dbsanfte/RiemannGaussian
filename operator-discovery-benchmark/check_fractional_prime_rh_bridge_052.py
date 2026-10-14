"""Independent conditional ordinary-zero bridge for fractional prime kernels.

The all-epsilon centered arithmetic error is always OPEN here. The admitted
object is its implication to RH, using standard zeta background and the
reviewed full-density/local-zero argument; no producer imports or data.
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
        if type(n) is not int or n<0 or n>self.cap-self.operations:raise OverflowError('fractional RH bridge work cap')
        self.operations+=n
        if time.monotonic()>self.deadline:raise TimeoutError('fractional RH bridge deadline')


def _meter(m):return Meter() if m is None else m

def _same(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return set(a)==set(b) and all(_same(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(_same(x,y) for x,y in zip(a,b))
    return a==b

def _expect(a,b):
    if not _same(a,b):raise ValueError('conditional bridge rule, source or scope mismatch')

def _fields(obj,keys):
    if type(obj) is not dict or set(obj)!=set(keys):raise ValueError('exact conditional bridge schema')

def _rational(text,m):
    if type(text) is not str or not 1<=len(text)<=2500:raise ValueError('canonical rational text')
    try:value=Q(text)
    except (ValueError,ZeroDivisionError):raise ValueError('rational') from None
    if str(value)!=text or max(abs(value.numerator).bit_length(),value.denominator.bit_length())>4096:
        raise ValueError('canonical rational capacity')
    m.charge(len(text)+1);return value


def _request(request,m):
    _fields(request,('kernel','error_bound','centering'))
    kernel=request['kernel'];_fields(kernel,('a','b','alpha','sign'))
    a,b,alpha=(_rational(kernel[k],m) for k in ('a','b','alpha'))
    if a<0 or b<0 or a+b!=1 or a<=b or not 0<alpha<1 or type(kernel['sign']) is not int or kernel['sign']!=-1:
        raise ValueError('licensed forward concave ordinary-mu kernel only')
    _expect(request['error_bound'],{'kind':'all_epsilon_square_root','minimum':2,'uniform_x':True,
        'constants':'depend_on_epsilon_and_fixed_kernel_only'})
    _expect(request['centering'],{'kind':'full_positive_density_integral'})
    m.charge(1+a.denominator.bit_length()+b.denominator.bit_length()+alpha.denominator.bit_length())
    return a,b,alpha


def _rules(request,a,b,alpha):
    """Typed rule instance; parameter gates are derived before this replay."""
    return {
        'schema':'fractional-prime-conditional-rh-bridge-v1','request':request,
        'status':'PAID_CONDITIONAL_IMPLICATION_WITH_OPEN_PREMISE',
        'pointwise_dependency':{
            'schema':'fractional-prime-kernel-proof-v1','request':request['kernel'],
            'branch':'fractional_forward',
            'purpose':'arithmetic identity and initial Dirichlet convergence only',
            'pays_centered_error':False},
        'parameters':{'a':str(a),'b':str(b),'alpha':str(alpha),'c':str(a-b),
            'scope':'one fixed admitted kernel; no uniformity across kernels assumed'},
        'normalizer':'I_alpha=integral_0^infinity (1-exp(-u))*u^(-alpha-1) du',
        'arithmetic_sum':'A(x)=sum_{2<=n<=x} K(n), for every real x>=1',
        'center':{
            'density':'m(x)=I_alpha^(-1)*integral_0^infinity x^(-b*t)/zeta(1+c*t)*t^(-alpha-1) dt',
            'primitive':'M(x)=integral_1^x m(u) du',
            'domain':'every real x>=1',
            'origin_integrability':'1/zeta(1+c*t)=c*t+O(t^2); t^(-alpha) integrable since alpha<1',
            'tail_integrability':'0<1/zeta(1+c*t)<=1 and x^(-b*t)<=1; alpha>0',
            'growth':'0<m(x)<=m(1)<infinity; M(1)=0 and M(x)=O(x)',
            'fitted_or_asymptotic_center_allowed':False},
        'open_premise':{
            'id':'centered_fractional_prime_error','status':'OPEN',
            'expression':'|A(x)-M(x)|<=C_(epsilon,a,b,alpha)*x^(1/2+epsilon)',
            'quantifiers':'for every epsilon>0 there exists finite C_(epsilon,a,b,alpha), for all real x>=2',
            'source':'ordinary Mobius coefficients and every ordinary integer in A(x)',
            'finite_samples_can_pay':False,'pointwise_kernel_bound_can_pay':False,
            'error_bound_proved':False},
        'mellin_bridge':{
            'F_initial':'F(s)=sum_{n>=2} K(n)/n^s=I_alpha^(-1)*integral_0^infinity [zeta(s+b*t)/zeta(s+a*t)-1]*t^(-alpha-1) dt',
            'H_initial':'H(s)=integral_1^infinity m(x)*x^(-s) dx=I_alpha^(-1)*integral_0^infinity t^(-alpha-1)/(zeta(1+c*t)*(s+b*t-1)) dt',
            'initial_domain':'Re(s)>1',
            'H_continuation_domain':'C minus the real cut (-infinity,1]; at b=0, H(s)=m(1)/(s-1)',
            'centered_identity':'F(s)-H(s)=s*integral_1^infinity (A(x)-M(x))*x^(-s-1) dx',
            'conditional_holomorphy':'the OPEN premise implies F-H holomorphic on Re(s)>1/2',
            'epsilon_choice':'on each compact subset choose 0<epsilon<minimum_Re(s)-1/2'},
        'zero_obstruction':{
            'hypothesis':'a nontrivial zero rho=beta+i*gamma with beta>1/2',
            'real_zero_exclusion':'the alternating eta series is positive for real 0<s<1; zeta(s)=eta(s)/(1-2^(1-s))<0',
            'choice':'choose a rightmost zero at this fixed nonzero height gamma; never a globally rightmost zero',
            'multiplicity':'every integer m>=1 via zeta(rho+z)=z^m*G(z), G holomorphic and nonzero nearby',
            'continuation_path':'horizontal s=sigma+i*gamma, sigma>beta; denominator has no zeros on any shifted ray',
            'asymptotic':'F(rho+delta)=C_m*delta^(-alpha)+O(1), delta positive real tending to0',
            'coefficient':'C_m=I_alpha^(-1)*integral_0^infinity [((1+b*u)/(1+a*u))^m-1]*u^(-alpha-1) du',
            'coefficient_sign':'finite and strictly negative for every m>=1, including b=0',
            'local_error':'G(delta+b*t)/G(delta+a*t)=1+O(t); integrated remainder is O(1) since alpha<1',
            'contradiction':'H is holomorphic near nonreal rho, so F-H cannot have the premise-implied holomorphy',
            'reflection':'the zeta functional equation reflects any off-line nontrivial zero to Re(s)>1/2'},
        'conclusion':'the exact OPEN centered-error premise implies RH',
        'conditional_RH_implication_proved':True,'converse_proved':False,
        'centered_error_proved':False,'unconditional_continuation_to_half_plane_proved':False,
        'original_floor_energy_bound_proved':False,'RH_proved':False,'RH_refuted':False,
        'numerical_evidence_used':False,
        'proof_backend':'independently reviewed exact analytic argument; no proof-assistant formalization',
        'background_sources':['https://dlmf.nist.gov/25.2','https://dlmf.nist.gov/25.4','https://dlmf.nist.gov/25.10']}


def verify_certificate(request,certificate,meter=None):
    """Admit only the reviewed implication, with its missing estimate OPEN.

    This verifies a finite typed analytic rule instance, not an arbitrary
    complex-analysis proof or a proof-assistant derivation of zeta background.
    """
    meter=_meter(meter)
    a,b,alpha=_request(request,meter)
    expected=_rules(request,a,b,alpha)
    _expect(certificate,expected)
    # Charge the complete finite replay, including all source/scope strings.
    meter.charge(len(repr(expected))+200)
    return {'verified':True,
        'conditional_RH_implication_proved':True,'centered_error_proved':False,
        'error_status':'OPEN','RH_proved':False,'RH_refuted':False,
        'converse_proved':False,'numerical_evidence_used':False,
        'source_scope':'one fixed ordinary-Mobius fractional kernel',
        'proof_scope':'reviewed typed analytic argument, not proof-assistant formalization',
        'all_zero_multiplicities':True,'full_density_center_required':True}


verify=verify_certificate

"""Conditional RH bridge for the051 forward fractional arithmetic kernels.

This creates an exact missing-bound request. It never proves its error premise.
The argument is human-readable calculus/complex analysis, independently reviewed;
it is not a proof-assistant formalization or a numerical zero computation.
"""
from copy import deepcopy
import fractional_prime_kernel_051 as KERNEL

SCHEMA = 'fractional-prime-conditional-rh-bridge-v1'
ERROR = {'kind': 'all_epsilon_square_root', 'minimum': 2, 'uniform_x': True,
         'constants': 'depend_on_epsilon_and_fixed_kernel_only'}
CENTER = {'kind': 'full_positive_density_integral'}


def make_request(kernel):
    return {'kernel': deepcopy(kernel), 'error_bound': deepcopy(ERROR),
            'centering': deepcopy(CENTER)}


def _equal(left, right):
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return set(left) == set(right) and all(_equal(left[k], right[k]) for k in left)
    return left == right


def build_certificate(request, meter=None):
    meter = meter or KERNEL.Meter()
    if type(request) is not dict or set(request) != {'kernel', 'error_bound', 'centering'}:
        raise ValueError('exact conditional bridge request')
    if not _equal(request['error_bound'], ERROR) or not _equal(request['centering'], CENTER):
        raise ValueError('full exact center and all-real all-epsilon error scope required')
    a, b, alpha, sign = KERNEL.parse(request['kernel'], meter)
    if not a > b >= 0 or not 0 < alpha < 1 or sign != -1:
        raise ValueError('forward concave kernel required')
    c = a-b
    meter.charge(200)
    return {
        'schema': SCHEMA, 'request': deepcopy(request),
        'status': 'PAID_CONDITIONAL_IMPLICATION_WITH_OPEN_PREMISE',
        'pointwise_dependency': {
            'schema': KERNEL.SCHEMA, 'request': deepcopy(request['kernel']),
            'branch': 'fractional_forward',
            'purpose': 'arithmetic identity and initial Dirichlet convergence only',
            'pays_centered_error': False},
        'parameters': {'a': str(a), 'b': str(b), 'alpha': str(alpha), 'c': str(c),
                       'scope': 'one fixed admitted kernel; no uniformity across kernels assumed'},
        'normalizer': 'I_alpha=integral_0^infinity (1-exp(-u))*u^(-alpha-1) du',
        'arithmetic_sum': 'A(x)=sum_{2<=n<=x} K(n), for every real x>=1',
        'center': {
            'density': 'm(x)=I_alpha^(-1)*integral_0^infinity x^(-b*t)/zeta(1+c*t)*t^(-alpha-1) dt',
            'primitive': 'M(x)=integral_1^x m(u) du',
            'domain': 'every real x>=1',
            'origin_integrability': '1/zeta(1+c*t)=c*t+O(t^2); t^(-alpha) integrable since alpha<1',
            'tail_integrability': '0<1/zeta(1+c*t)<=1 and x^(-b*t)<=1; alpha>0',
            'growth': '0<m(x)<=m(1)<infinity; M(1)=0 and M(x)=O(x)',
            'fitted_or_asymptotic_center_allowed': False},
        'open_premise': {
            'id': 'centered_fractional_prime_error', 'status': 'OPEN',
            'expression': '|A(x)-M(x)|<=C_(epsilon,a,b,alpha)*x^(1/2+epsilon)',
            'quantifiers': 'for every epsilon>0 there exists finite C_(epsilon,a,b,alpha), for all real x>=2',
            'source': 'ordinary Mobius coefficients and every ordinary integer in A(x)',
            'finite_samples_can_pay': False, 'pointwise_kernel_bound_can_pay': False,
            'error_bound_proved': False},
        'mellin_bridge': {
            'F_initial': 'F(s)=sum_{n>=2} K(n)/n^s=I_alpha^(-1)*integral_0^infinity [zeta(s+b*t)/zeta(s+a*t)-1]*t^(-alpha-1) dt',
            'H_initial': 'H(s)=integral_1^infinity m(x)*x^(-s) dx=I_alpha^(-1)*integral_0^infinity t^(-alpha-1)/(zeta(1+c*t)*(s+b*t-1)) dt',
            'initial_domain': 'Re(s)>1',
            'H_continuation_domain': 'C minus the real cut (-infinity,1]; at b=0, H(s)=m(1)/(s-1)',
            'centered_identity': 'F(s)-H(s)=s*integral_1^infinity (A(x)-M(x))*x^(-s-1) dx',
            'conditional_holomorphy': 'the OPEN premise implies F-H holomorphic on Re(s)>1/2',
            'epsilon_choice': 'on each compact subset choose 0<epsilon<minimum_Re(s)-1/2'},
        'zero_obstruction': {
            'hypothesis': 'a nontrivial zero rho=beta+i*gamma with beta>1/2',
            'real_zero_exclusion': 'the alternating eta series is positive for real 0<s<1; zeta(s)=eta(s)/(1-2^(1-s))<0',
            'choice': 'choose a rightmost zero at this fixed nonzero height gamma; never a globally rightmost zero',
            'multiplicity': 'every integer m>=1 via zeta(rho+z)=z^m*G(z), G holomorphic and nonzero nearby',
            'continuation_path': 'horizontal s=sigma+i*gamma, sigma>beta; denominator has no zeros on any shifted ray',
            'asymptotic': 'F(rho+delta)=C_m*delta^(-alpha)+O(1), delta positive real tending to0',
            'coefficient': 'C_m=I_alpha^(-1)*integral_0^infinity [((1+b*u)/(1+a*u))^m-1]*u^(-alpha-1) du',
            'coefficient_sign': 'finite and strictly negative for every m>=1, including b=0',
            'local_error': 'G(delta+b*t)/G(delta+a*t)=1+O(t); integrated remainder is O(1) since alpha<1',
            'contradiction': 'H is holomorphic near nonreal rho, so F-H cannot have the premise-implied holomorphy',
            'reflection': 'the zeta functional equation reflects any off-line nontrivial zero to Re(s)>1/2'},
        'conclusion': 'the exact OPEN centered-error premise implies RH',
        'conditional_RH_implication_proved': True,
        'converse_proved': False, 'centered_error_proved': False,
        'unconditional_continuation_to_half_plane_proved': False,
        'original_floor_energy_bound_proved': False,
        'RH_proved': False, 'RH_refuted': False,
        'numerical_evidence_used': False,
        'proof_backend': 'independently reviewed exact analytic argument; no proof-assistant formalization',
        'background_sources': ['https://dlmf.nist.gov/25.2', 'https://dlmf.nist.gov/25.4',
                               'https://dlmf.nist.gov/25.10']}

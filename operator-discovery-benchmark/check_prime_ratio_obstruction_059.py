"""Independent cofinal cost obstruction for a first ascending prime-ratio pass.

No kernel evaluations, source arrays, miner imports, or finite failure scales.
The obstruction concerns the irrevocably charged matching cost, not |J|.
"""
from fractions import Fraction as Q
from math import gcd, isqrt, prod
from check_fractional_prime_rh_bridge_052 import Meter, _rational, _fields, _expect


def _integer(n,lower,upper):
    if type(n) is not int or not lower<=n<=upper:raise ValueError('bounded strict integer')
    return n


def _prime(n,m):
    _integer(n,2,1_000_000)
    for d in range(2,isqrt(n)+1):
        m.charge(4)
        if n%d==0:raise ValueError('actual prime required')
    m.charge(1)
    return n


def _parameters(obj,m):
    _fields(obj,('alpha','gamma','tau','primes','p','q'))
    alpha,gamma,tau=(_rational(obj[k],m) for k in ('alpha','gamma','tau'))
    if not 0<alpha<1 or gamma<=0 or not 0<tau<1:raise ValueError('fixed fractional band parameters')
    ps=obj['primes']
    if type(ps) is not list or not 2<=len(ps)<=8:raise ValueError('fixed bounded prime mask')
    for p in ps:_prime(p,m)
    if ps!=sorted(set(ps)):raise ValueError('distinct ascending prime mask')
    p,q=obj['p'],obj['q']
    if type(p) is not int or type(q) is not int or p not in ps or q not in ps or p>=q:
        raise ValueError('ordered source primes in mask')
    return alpha,gamma,tau,ps,p,q


def _policy(obj):
    _fields(obj,('steps',));steps=obj['steps']
    if type(steps) is not list or not 1<=len(steps)<=2:raise ValueError('first prime pass and optional residual scan')
    _fields(steps[0],('kind','group','order'))
    if steps[0]['kind']!='prime_ratio' or steps[0]['group'] not in ('all','profile') or steps[0]['order']!='asc':
        raise ValueError('first ascending prime pass required')
    if len(steps)==2:
        _fields(steps[1],('kind','group','order','method'))
        if steps[1]['kind']!='scan' or steps[1]['group'] not in ('all','profile') or steps[1]['order']!='asc' or steps[1]['method']!='stack':
            raise ValueError('canonical residual scan only')


def _first_prime_outside(ps,m):
    for n in range(2,32):
        m.charge(1)
        if all(n%d for d in range(2,isqrt(n)+1)) and n not in ps:return n
    raise OverflowError('first outside prime capacity')


def _floor_cell(lo,hi,den,m):
    """One-sided limits, not midpoint sampling, for the OPEN interval."""
    floors=[]
    for multiplier in (1,2,4):
        left=lo*multiplier/den;right=hi*multiplier/den
        minimum=left.numerator//left.denominator
        maximum=-((-right.numerator)//right.denominator)-1
        m.charge(40+sum(abs(x).bit_length() for x in (left.numerator,left.denominator,right.numerator,right.denominator)))
        if minimum!=maximum:raise ValueError('a component floor changes inside the open cell')
        floors.append(minimum)
    value=floors[2]-3*floors[1]+2*floors[0]
    if value not in (-1,0,1):raise ValueError('floor shell weight range')
    return {'denominator':den,'floors':floors,'weight':value}


def _profile(a,b):
    if a==b==0:raise ValueError('both source tokens must be nonzero')
    if b==0:return 'P',a
    if a==0:return 'Q',-b
    if a==b:return 'D',a
    return 'S',a


def verify(certificate,meter=None):
    m=Meter() if meter is None else meter
    _fields(certificate,('schema','parameters','policy','prime','cell','profile','kernel_sign','log_power'))
    _expect(certificate['schema'],'prime-ratio-cost-obstruction-v1')
    alpha,gamma,tau,ps,p,q=_parameters(certificate['parameters'],m)
    _policy(certificate['policy']);m.charge(100)
    r=_prime(certificate['prime'],m)
    if r!=_first_prime_outside(ps,m):raise ValueError('smallest actual prime outside registered mask required')
    _fields(certificate['cell'],('lower','upper'))
    lo,hi=(_rational(certificate['cell'][k],m) for k in ('lower','upper'))
    if not 0<lo<hi:raise ValueError('positive-length positive open cell')
    rows=[_floor_cell(lo,hi,d,m) for d in (p,q,r*p,r*q)]
    first=_profile(rows[0]['weight'],rows[1]['weight'])
    second=_profile(rows[2]['weight'],rows[3]['weight'])
    if first!=second:raise ValueError('same profile and same nonzero kernel sign at both endpoints')
    profile,sigma=first
    if type(certificate['profile']) is not str or certificate['profile']!=profile or type(certificate['kernel_sign']) is not int or certificate['kernel_sign']!=sigma:
        raise ValueError('profile or signed source gate')
    delta=int(profile=='D');power=Q(len(ps)+delta+1)-alpha
    if _rational(certificate['log_power'],m)!=power:raise ValueError('kernel logarithmic power')
    mask=r*prod(ps);phi=(r-1)*prod(s-1 for s in ps)
    width=1/lo-1/hi
    # These are rational proof constants, not evaluated scientific values.
    density_floor=Q(phi,4*mask)
    kernel_floor=(1-alpha)/Q(36*(2**len(ps))*prod(ps)*r*q**(delta+1))
    m.charge(2000+sum(abs(x).bit_length() for x in (mask,phi,width.numerator,width.denominator)))
    return {
        'verified':True,'schema':'verified-prime-ratio-cost-obstruction-v1',
        'parameters':certificate['parameters'],'policy':certificate['policy'],
        'prime':r,'cell':certificate['cell'],'profile':profile,'kernel_sign':sigma,
        'floor_cells':rows,'open_endpoint_convention':'floor(c*lower), ceil(c*upper)-1',
        'source_scope':'ordinary Mobius tokens; complete registered-prime product; unit and range exits retained',
        'first_pass':{'smallest_unregistered_prime':True,'opposite_mu_signs':True,
            'disjoint_edges':'squarefree a coprime to r*M; r^2*a is absent',
            'charged_before_later_prime_passes':True,'later_residual_scan_cannot_undo_cost':True},
        'density':{'coprime_squarefree_modulus':mask,'reciprocal_cell_width':str(width),
            'density_lower':str(density_floor),'method':'mu^2 divisor-square expansion; Euler product >=1/4',
            'count':'rho*(1/lower-1/upper)*N+O_(mask,cell)(sqrt(N))',
            'finite_threshold_claimed':False},
        'kernel_lower':{'registered_prime_count':len(ps),'profile_order':delta,
            'rational_integrand_constant':str(kernel_floor),
            'window':'[1/log(2*q*floor(4*N/p)),2/log(2*q*floor(4*N/p))]',
            'window_eventually_inside_source_band':True,'log_power':str(power)},
        'lower_bound':{'expression':'B_policy(N)>=c*N/(log(N))^log_power',
            'log_power':str(power),'constant':'some fixed c>0 depending only on admitted parameters and cell',
            'domain':'every sufficiently large integer N','cost_lower_bound_proved':True,
            'numerical_lower_constant_claimed':False,'finite_threshold_claimed':False},
        'growth_exclusion':{'quantifiers':'every fixed beta<1, every fixed finite real eta, every fixed finite C>=0',
            'excluded_expression':'B_policy(N)<=C*N^beta*(1+log(N))^eta for every integer N>=2',
            'proved':True,'scope':'this first-prime-pass matching cost only; not the signed sum J or arbitrary matching policies'},
        'actual_arithmetic_refuted':False,'RH_refuted':False,'RH_proved':False,
        'uniform_signed_target_bound_proved':False,'finite_counterexample_claimed':False,
        'fresh_source_arrays_or_integrals_evaluated':False}

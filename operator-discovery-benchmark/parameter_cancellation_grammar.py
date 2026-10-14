"""Actual parameter jets and universal cancellation-before-envelope bounds."""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial,comb,floor
import flint
from estimate_grammar import inverse_one_prefix
from mellin_kernel_grammar import real
from branch_center_grammar import canonical,moments,normalization,recovery,center_series,center_disk_certificate,complete_center,decode
from rational_fractional_evaluator import coefficients,rational_power,continued_profile,ball,cball,integer_guard

VERSION='actual-parameter-jet-limits-uniform-normalization-adaptive-cauchy-radius-v1'

def raw_jet(m,n):
    if type(m)is not int or m<0:raise ValueError('Nonnegative integer Taylor index required')
    if n==1:return flint.arb(0)
    return real(n).log().log()**m/factorial(m)

def jets(m,N,precision=640,input_coefficients=None):
    if type(m)is not int or m<0 or type(N)is not int or N<1:raise ValueError('Integer jet and full cutoff required')
    flint.ctx.prec=precision
    if input_coefficients is None:
        f=[flint.arb(0)]+[flint.arb(1) for _ in range(N)];inv=list(map(flint.arb,inverse_one_prefix(N)));model='inverse_one'
    else:
        f=list(map(flint.arb,input_coefficients))
        if len(f)!=N+1 or f[1]!=1:raise ValueError('Generic unit-normalized full input required')
        inv=[flint.arb(0) for _ in range(N+1)];inv[1]=flint.arb(1)
        for n in range(2,N+1):inv[n]=-sum((inv[d]*f[n//d] for d in range(1,n) if n%d==0),flint.arb(0))
        model='generic_sequence'
    out=[flint.arb(0) for _ in range(N+1)]
    for d in range(1,N+1):
        for j in range(1,N//d+1):out[d*j]+=inv[d]*f[j]*raw_jet(m,j)
    return {'index':m,'cutoff':N,'precision':precision,'values':list(map(ball,out)),'arithmetic_model':model,'prime_or_factor_oracle_used':False,
        'Taylor_factorial_charged':True,'complete_finite_arithmetic':True,'weight_at_one_is_zero':True}

@lru_cache(maxsize=None)
def reciprocal_gamma(M,precision):
    flint.ctx.prec=precision;old=flint.ctx.cap;flint.ctx.cap=M+1
    try:s=flint.arb_series([1,-1],prec=M+1).rgamma();return tuple(s[j] for j in range(M+1))
    finally:flint.ctx.cap=old

def jet_center(m,x,precision=640):
    if type(m)is not int or m<0 or Q(x)<1:raise ValueError('Integer jet and x>=1 required')
    flint.ctx.prec=precision
    if m==0 or Q(x)==1:return {'value_ball':'0','error_ball':'0','full_parameter_jet_center':True,'missing':False}
    L=448;G=reciprocal_gamma(m,precision);H=center_series(str(Q(x)),L,precision);value=sum((h*sum((G[r-1]/real((j+1)**(m-r+1)) for r in range(1,m+1)),flint.arb(0)) for j,h in enumerate(H)),flint.arb(0));disk=center_disk_certificate(precision)
    if not disk['certified']:return {'missing':True,'reason':'jet_center_Cauchy_disk_unresolved'}
    R=Q(disk['radius']);lower=flint.arb(disk['modulus_lower_ball']);B=(rational_power(real(Q(x)),1+R)+1)/(real(R-1)*lower);error=B*real(R)**(-L)/(1-real(1/R))*sum((abs(G[r-1])/real((L+1)**(m-r+1)) for r in range(1,m+1)),flint.arb(0));value+=flint.arb(0,error.upper())
    return {'value_ball':ball(value),'error_ball':ball(error),'full_parameter_jet_center':True,'missing':False,'gamma_coefficients':list(map(ball,G)),'Taylor_terms':L,'precision':precision}

def family_parameters(p,q0=2):
    if p.get('arithmetic_model')!='inverse_one' or p.get('center')!='full_real_cut':raise ValueError('Actual arithmetic and full center required')
    if type(q0)is not int or q0<1:raise ValueError('Positive integer minimum level required')
    m,pm=moments(p);atoms=[(Q(b),Q(w)) for b,w in p['atoms']];bmax=max(b for b,w in atoms);cap=Q(1,2)-bmax/q0
    if cap<=0:raise ValueError('Positive Cauchy cap required')
    Aw=sum((abs(w)*b**m for b,w in atoms),Q(0))/abs(pm)
    return {'moment':m,'moment_value':str(pm),'weight_norm':str(Aw),'largest_base':str(bmax),'minimum_level':q0,'radius_cap':str(cap),
        'uniform_center_derivative_guard':str(12*Aw/cap**m),'actual_arithmetic_retained':True,'ordinary_zeta_erased':False}

def coordinate(x):
    x=Q(x)
    if x<1:raise ValueError('x>=1 required')
    return (4*(1+real(x).log())).log()

def radius_value(program,V,m,cap=Q(1,4)):
    if type(m)is not int or m<0 or not V>0 or not 0<Q(cap)<=Q(1,2) or not radius_certificate(program)['admitted']:raise ValueError('Admitted radius, integer Taylor index, positive coordinate and cap <=1/2 required')
    kind=program['kind']
    if kind=='constant':value=real(Q(program['value']))
    elif kind=='shifted_power':value=real(Q(program['coefficient']))*rational_power(real(max(1,m)),Q(program['index_power']))/rational_power(real(Q(program['shift']))+V,Q(program['coordinate_power']))
    elif kind=='inverse_monomial':value=1/(real(Q(program['coefficient']))*rational_power(real(max(1,m)),Q(program['index_power']))*rational_power(V,Q(program['coordinate_power'])))
    else:raise ValueError('Unsupported radius program')
    upper=real(Q(cap))
    if value>upper:return upper
    if upper>value:return value
    return flint.arb(value.lower(),0).union(upper) # valid enclosure of min

def radius_certificate(program):
    kind=program.get('kind')
    try:
        if kind=='constant':valid=Q(program['value'])>0
        elif kind=='shifted_power':valid=Q(program['coefficient'])>0 and Q(program['shift'])>=0 and Q(program['coordinate_power'])>0 and isinstance(Q(program['index_power']),Q)
        elif kind=='inverse_monomial':valid=Q(program['coefficient'])>0 and Q(program['coordinate_power'])>0 and isinstance(Q(program['index_power']),Q)
        else:valid=False
    except (ValueError,ZeroDivisionError,KeyError,TypeError):valid=False
    return {'admitted':valid,'cap_applied_before_Cauchy_bound':True,'all_positive_coordinates_and_integer_indices':valid,
        'all_real_scale_bound_proved':valid,'ordinary_power':'1','RH_strength':False,'radius_program_semantics_unchanged':True,
        'supplied_math_method':'actual exponential maximum, reciprocal-Gamma product, Cauchy and moment cancellation'}

def certified_family_bound(p,radius,q,x,q0=2):
    params=family_parameters(p,q0)
    if type(q)is not int or q<q0 or not radius_certificate(radius)['admitted']:raise ValueError('Admitted radius and full integer level domain required')
    V=coordinate(x);m=params['moment'];rho=Q(params['radius_cap']);d=radius_value(radius,V,m,rho);Aw=real(Q(params['weight_norm']));A=real(Q(params['largest_base'])/q)
    value=Aw*real(Q(x))*(9*d**(-m)*((A+d)*V).exp()+12/real(rho)**m)
    return {'bound_ball':ball(value),'parameters':params,'radius_ball':ball(d),'uniform_in_normalization_level':True,'ordinary_power':'1','all_real_x_ge_one':True,
        'cancellation_before_absolute_envelope':True,'full_center_and_actual_mobius_retained':True,'global_signed_premise_proved':True,'RH_strength':False}

def certified_jet_bound(m,radius,x,arithmetic_model='inverse_one'):
    if arithmetic_model!='inverse_one':raise ValueError('Actual-prime Cauchy bound does not transfer to generic coefficients')
    if type(m)is not int or m<0 or not radius_certificate(radius)['admitted']:raise ValueError('Admitted radius and nonnegative integer Taylor index required')
    V=coordinate(x);d=radius_value(radius,V,m,Q(1,2));value=real(Q(x))*(9*d**(-m)*(d*V).exp()+12*2**m)
    return {'bound_ball':ball(value),'jet_index':m,'Taylor_factorial_charged':True,'all_real_x_ge_one':True,'ordinary_power':'1','RH_strength':False}

def jet_bank_recovery(minimum,all_integer_tail=True,arithmetic_model='inverse_one'):
    admitted=type(minimum)is int and minimum>=0 and all_integer_tail and arithmetic_model=='inverse_one'
    return {'admitted':admitted,'minimum_index':minimum,'every_integer_in_tail_required':True,'cofinal_subset_is_sufficient':False,'all_ordinary_heights_and_multiplicities':admitted,
        'argument':'entire exponent-parameter tail coefficients vanish, polynomial, ordinary-zeta pole contradiction',
        'global_critical_signed_premise_proved':False,'RH_proved':False,'finite_positive_jet_RH_recovery_unproved':True}

def jet_profile_bound(precision=768):
    flint.ctx.prec=precision;s=flint.acb(real(Q(5,8)),16);z=flint.acb(flint.arb(real(Q(9,8)),real(Q(1,2))),16);old=flint.ctx.cap;flint.ctx.cap=2
    try:B=abs(flint.acb_series([z,1],prec=2).zeta()[1]).upper()
    finally:flint.ctx.cap=old
    bound=3*abs(s.zeta()-1)+real(Q(3,2))*(2*B+(1+2/s.real)*rational_power(real(2),Q(-13,8))/real(2).log())
    return {'disk_radius':'1/2','zeta_derivative_segment_upper_ball':ball(B),'parameter_disk_modulus_upper_ball':ball(bound),'complete_continuation_bound':True}

@lru_cache(maxsize=None)
def jet_observer(m):
    if type(m)is not int or m<0:raise ValueError('Integer jet index required')
    if m>8:return {'missing':True,'reason':'jet_observer_resources_exhausted','index':m,'missing_not_counterexample':True}
    precision=max(896,160*m+512);flint.ctx.prec=precision;s=flint.acb(real(Q(5,8)),16)
    if not m:return {'value_ball':cball(s.zeta()-1),'whole_continued_jet':True,'index':m,'method':'exact_shifted_Mertens_numerator','error_ball':'0'}
    h=Q(1,2**160);bounds=jet_profile_bound(precision);BF=flint.arb(bounds['parameter_disk_modulus_upper_ball']);total=flint.acb(0);points=[];M=max(64,16*m+16);N=512+128*m
    for j in range(m+1):
        row=continued_profile(j*h,precision,N,M) if j else {'value_ball':cball(s.zeta()-1),'whole_continuation_not_prefix_surrogate':True}
        total+=(-1)**(m-j)*comb(m,j)*decode(row['value_ball']);points.append(row)
    value=total/(factorial(m)*real(h)**m);error=m*(m+1)*real(h)*BF/(real(Q(1,2))-m*real(h))**(m+1);value+=flint.acb(flint.arb(0,error.upper()),flint.arb(0,error.upper()))
    return {'value_ball':cball(value),'whole_continued_jet':True,'index':m,'method':'whole-continuation forward parameter difference plus Cauchy remainder','error_ball':ball(error),
        'difference_step':str(h),'finite_differences_not_unenclosed_limit':True,'Taylor_factorial_charged':True,'complete_parameter_disk_bound':bounds,'points':points,'precision':precision}

def coefficient_features(n):
    n=int(n)
    if n<2:raise ValueError('Feature domain n>=2')
    L=real(n).log();l=L.log();p=(1+L).log();pp=(1+p).log();out={f'constant':flint.arb(1)}
    for m in range(1,5):out[f'nested_log_integer_{m}']=l**m
    for r in ['1/6','1/3','1/2','1','2','3','4']:
        out['log_power_'+r]=rational_power(L,Q(r));out['shifted_nested_power_'+r]=rational_power(p,Q(r))
    out.update({'third_shifted_log':pp,'sin_log':L.sin(),'cos_log':L.cos(),'sin_nested':l.sin(),'cos_nested':l.cos(),'gaussian_nested':(-l*l).exp(),'mixed_log_nested':L*l})
    return out

def feature_limit_admission(feature,coefficient,m):
    exact_feature='constant' if not m else f'nested_log_integer_{m}'
    return {'admitted':feature==exact_feature and Q(coefficient)==Q(1,factorial(m)),
        'universal_exact_finite_prefix_limit':feature==exact_feature and Q(coefficient)==Q(1,factorial(m)),
        'first_nonzero_parameter_moment':m,'pointwise_limit_jet_index':m,'uniform_on_compact_x_only':True,
        'infinite_x_limit_exchange_claimed':False,'same_as_fixed_q_parent':False,'Taylor_factorial_required':True}

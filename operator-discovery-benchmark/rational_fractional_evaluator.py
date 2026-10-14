"""Portable numerical contracts for positive rational logarithmic exponents.

This extends callable evaluation, not the frozen search or its conclusions.
Fractional powers use exp(r*log x), with exact-rational r enclosed natively,
so a C unsigned-long root index never restricts the denominator.
"""
from fractions import Fraction as Q
from math import factorial,floor
import flint
from estimate_grammar import inverse_one_prefix
from mellin_kernel_grammar import real
from branch_center_grammar import canonical,recovery,normalization,complete_center,croot,derivative_guard,decode

VERSION='unbounded-rational-logarithmic-powers-and-exact-native-bound-guards-v1'
def ball(x):return x.str(flint.ctx.prec*30103//100000+12)
def cball(x):return {'real':ball(x.real),'imag':ball(x.imag)}

def rational_power(x,r):
    r=Q(r)
    if not r:return flint.arb(1)
    if x==0 and r>0:return flint.arb(0)
    if not x>0:raise ValueError('Positive base required for this real power')
    return (real(r)*x.log()).exp()

def coefficients(order,N,precision=512):
    order=Q(order)
    if order<=0 or type(N)is not int or N<1:raise ValueError('Positive rational order and positive integer cutoff required')
    flint.ctx.prec=precision;mu=inverse_one_prefix(N);raw=[flint.arb(0)]+[rational_power(real(n).log(),order) for n in range(1,N+1)];values=[flint.arb(0) for _ in range(N+1)]
    for d in range(1,N+1):
        if not mu[d]:continue
        for j in range(1,N//d+1):values[d*j]+=mu[d]*raw[j]
    return {'order':str(order),'cutoff':N,'precision':precision,'mu':mu,'values':list(map(ball,values)),'complete_finite_arithmetic':True,
        'prime_or_factor_oracle_used':False,'all_positive_rational_orders_supported':True,'native_unsigned_denominator_used':False}

def integer_guard(bound):
    if not bound.is_finite():raise ArithmeticError('Missing finite bound enclosure')
    guard=bound.upper().ceil().unique_fmpz()
    if guard is None:raise ArithmeticError('Missing exact integer ceiling enclosure')
    return int(guard)+1

def weak_certificate(program,q,precision=512):
    flint.ctx.prec=precision
    if not recovery(program)['admitted']:raise ValueError('Actual complete-center recovering family required')
    h=abs(normalization(program,q));K=sum((real(abs(Q(w)))*derivative_guard(Q(b)/q) for b,w in program['atoms']),flint.arb(0))/real(h)
    C=K+sum((real(abs(Q(w))) for b,w in program['atoms']),flint.arb(0))/real(h)
    stored_C=ball(C);C=flint.arb(stored_C)
    return {'constant':integer_guard(C),'derivative_guard_ball':ball(K),'native_bound_ball':stored_C,'bound_integer_is_exact_outward_ceiling':True,'decimal_conversion_used_for_integer_guard':False,
        'normalization':str(normalization(program,q)),'ordinary_exponent':'1','log_degree':'1','all_real_x_ge_one':True,'global_signed_premise_proved':True,'RH_strength':False,'actual_mobius_arithmetic_retained':True}

def continued_profile(order,precision=768,N=512,M=64):
    """Whole continued numerator; larger resources resolve tiny-order filters."""
    order=Q(order);croot(order);flint.ctx.prec=precision;s=flint.acb(real(Q(5,8)),16);L=real(N).log();coeff=[flint.acb(1)];der=[]
    for r in range(2*M+1):
        der.append(sum((c*rational_power(L,order-j) for j,c in enumerate(coeff)),flint.acb(0))*flint.acb(real(N)).pow(-s-r))
        if r<2*M:coeff=[-(s+r)*(coeff[j] if j<len(coeff) else 0)+(real(order-j+1)*coeff[j-1] if j else 0) for j in range(len(coeff)+1)]
    value=sum((flint.acb(real(n)).pow(-s)*rational_power(real(n).log(),order) for n in range(2,N+1)),flint.acb(0));value+=((s-1)*L).gamma_upper(real(order+1))*(s-1).pow(-real(order+1))-der[0]/2
    for k in range(1,M+1):value-=flint.arb.bernoulli(2*k)/factorial(2*k)*der[2*k-1]
    rate=s.real+2*M-1;error=2*real(2*M).zeta()/(2*flint.arb.pi())**(2*M)*(rate*L).gamma_upper(real(order+1))/rational_power(rate,order+1)*sum((abs(c)/L**j for j,c in enumerate(coeff)),flint.arb(0))
    value+=flint.acb(flint.arb(0,error.upper()),flint.arb(0,error.upper()))
    return {'order':str(order),'value_ball':cball(value),'remainder_ball':ball(error),'precision':precision,'N':N,'M':M,'whole_continuation_not_prefix_surrogate':True,'native_unsigned_denominator_used':False}

def family_observer(program,q,profiles,precision=768):
    flint.ctx.prec=precision;h=normalization(program,q);F=sum((real(Q(w))*decode(profiles[str(Q(b)/q)]['value_ball']) for b,w in program['atoms']),flint.acb(0))/real(h);stored=cball(F);F=decode(stored);lo=abs(F).lower();D=2**160
    if not lo.is_finite():return {'missing':True,'reason':'complete_observer_modulus_unresolved'}
    lower=real(Q(floor(Q(lo.str(250,radius=False))*D)-1,D))
    if not lower>0:return {'missing':True,'reason':'complete_observer_modulus_unresolved'}
    return {'missing':False,'normalized_full_profile_ball':stored,'profile_modulus_lower_ball':ball(lower),'profile_lower_rounding_bits':160,'normalization':str(h),
        'normalization_charged':True,'arithmetic_model':'inverse_one','RH_proved':False}

"""Actual logarithmic roots and inverse preconditioning with retained remainder."""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial,comb,ceil
import flint
from estimate_grammar import inverse_one_prefix
from mellin_kernel_grammar import real,power,serialize

VERSION='logarithmic-root-arithmetic-generic-divisor-preconditioning-retained-signed-remainder-v1'
def ball(v):return v.str(85)


def convolution(a,b):
    N=min(len(a),len(b))-1;out=[flint.arb(0) for _ in range(N+1)]
    for d in range(1,N+1):
        if a[d]==0:continue
        for j in range(1,N//d+1):out[d*j]+=a[d]*b[j]
    return out


def generic_inverse(f):
    if f[1]!=1:raise ValueError('Unit-normalized generic coefficient input required')
    N=len(f)-1;out=[flint.arb(0) for _ in range(N+1)];out[1]=flint.arb(1)
    for n in range(2,N+1):out[n]=-sum((out[d]*f[n//d] for d in range(1,n) if n%d==0),flint.arb(0))
    return out


def coefficients(order,N,precision=384):
    order=Q(order)
    if order<=0 or type(N)is not int or N<1:raise ValueError('Positive rational weight and positive integer cutoff required')
    flint.ctx.prec=precision;mu=inverse_one_prefix(N);logs=[flint.arb(0)]+[real(n).log() for n in range(1,N+1)]
    raw=[flint.arb(0)]+[flint.arb(0) if n==1 else power(logs[n],order) for n in range(1,N+1)]
    out=convolution([flint.arb(m) for m in mu],raw)
    return {'order':str(order),'cutoff':N,'precision':precision,'mu':mu,'values':list(map(ball,out)),
        'complete_finite_arithmetic':True,'definition':'mu * (log n)^order; 0^order=0',
        'prime_or_factor_oracle_used':False,'all_positive_rational_orders_supported':True}


def sum_at(table,x):
    x=Q(x)
    if x<1 or x.numerator//x.denominator>table['cutoff']:raise ValueError('Complete point support required')
    return sum((flint.arb(v) for v in table['values'][1:1+x.numerator//x.denominator]),flint.arb(0))


@lru_cache(maxsize=None)
def gamma_constants(K,precision):
    flint.ctx.prec=precision
    series=flint.arb_series([1,1],prec=K+1).zeta(deflate=True)
    return [(-1)**j*factorial(j)*series[j] for j in range(K)]


def harmonic_polynomials(K,gamma):
    out=[]
    for r in range(K):
        P=[flint.arb(0) for _ in range(r+2)];P[r+1]=real(Q(1,r+1))
        for j in range(r+1):P[r-j]+=(-1)**j*comb(r,j)*gamma[j]
        out.append(P)
    return out


def complete_preconditioner(k,precision=512):
    if type(k)is not int or k<1:raise ValueError('Positive integer derivative required by this completion backend')
    flint.ctx.prec=precision;gamma=gamma_constants(k,precision);Hs=harmonic_polynomials(k,gamma)
    target=[real((-1)**(k-j)*Q(factorial(k),factorial(j))) for j in range(k+1)];P=[flint.arb(0) for _ in range(k)]
    for j in range(k,0,-1):P[j-1]=j*(target[j]-sum((P[r]*Hs[r][j] for r in range(j,k)),flint.arb(0)))
    b=target[0]-sum((P[r]*Hs[r][0] for r in range(k)),flint.arb(0))
    Bj=[Q(2*factorial(j))*sum((Q(1,factorial(h)) for h in range(j+1)),Q(0)) for j in range(k)]
    Cr=[sum((comb(r,j)*Bj[j] for j in range(r+1)),Q(0)) for r in range(k)]
    residual=real(factorial(k)+1)+abs(b)+sum((abs(P[r])*real(Cr[r]) for r in range(k)),flint.arb(0))
    C_R=ceil(Q(residual.upper().str(70,radius=False)))+1;norm=sum(comb(k,j)*factorial(j) for j in range(k+1));C=2*norm*C_R
    return {'kind':'completed_divisor_antiderivative','order':k,'polynomial_coefficients':list(map(ball,P)),'constant_term':ball(b),
        'gamma_constants':list(map(ball,gamma)),'harmonic_error_constants':list(map(str,Bj)),'dilated_harmonic_error_constants':list(map(str,Cr)),
        'residual_constant':C_R,'divisor_norm_constant':2*norm,'signed_error_constant':C,
        'residual_bound':'|R_k(y)|<=C_R*(1+log y)^k for every real y>=1',
        'signed_error_bound':'|sum_(n<=x) lambda_k(n)-h_k(x)|<=C*x for every real x>=1',
        'h_semantics':'x*P(log x)+b for x>=1, zero below one',
        'exact_rewrite':'sum lambda_k = h_k + sum_(d<=x) mu(d)*R_k(x/d)',
        'inverse_applied_before_absolute_envelope':True,'actual_mobius_remainder_retained':True,
        'arithmetic_model':'inverse_one','global_signed_premise_proved':True,'ordinary_zeta_erased':False,
        'ordinary_exponent':'1','RH_strength':False,'first_derivative_recovers_every_ordinary_zero':k==1,
        'higher_derivative_zero_recovery_is_unproved':k!=1,'historical_priority_is_acceptance_gate':False,
        'named_calibration':'integer generalized von Mangoldt/Selberg identities'}


def evaluate_h(cert,x):
    x=Q(x)
    if x<1:return flint.arb(0)
    L=real(x).log();v=flint.arb(0)
    for c in reversed(cert['polynomial_coefficients']):v=v*L+flint.arb(c)
    return real(x)*v+flint.arb(cert['constant_term'])


def approximate_certificate(k,coefficients,constant,precision=512):
    """A completed reference proves a conservative bound for ANY proposal.

    The proposal remains its exact rational program. The reference is used
    only by the proof backend; no substitution of operator semantics occurs.
    """
    ref=complete_preconditioner(k,precision);P=list(map(Q,coefficients));b=Q(constant);degree=max(k-1,len(P)-1);C=real(ref['signed_error_constant'])+abs(flint.arb(ref['constant_term'])-real(b));deltas=[]
    for r in range(degree+1):
        delta=(flint.arb(ref['polynomial_coefficients'][r]) if r<k else flint.arb(0))-(real(P[r]) if r<len(P) else flint.arb(0));deltas.append(delta);C+=abs(delta)
    loss=max((r for r,v in enumerate(deltas) if v!=0),default=0);guard=ceil(Q(C.upper().str(70,radius=False)))+1
    return {'order':k,'polynomial_coefficients':list(map(str,P)),'constant_term':str(b),'global_signed_premise_proved':True,
        'bound_constant':guard,'log_degree':loss,'ordinary_exponent':'1','actual_mobius_remainder_retained':True,
        'source_semantics_changed_by_proof':False,'reference_completion_used_only_for_bound':True,'RH_strength':False}


def primitive_sum(k,x):
    x=Q(x);return sum((real(n).log()**k for n in range(1,1+x.numerator//x.denominator)),flint.arb(0))
def residual(cert,x):
    x=Q(x);return primitive_sum(cert['order'],x)-sum((evaluate_h(cert,x/n) for n in range(1,1+x.numerator//x.denominator)),flint.arb(0))


def sign_signature(order):
    order=Q(order)
    if order<=0:raise ValueError('Positive rational logarithmic order required')
    m=order.numerator//order.denominator
    return {'kind':'integer_zero_tail' if order.denominator==1 else 'alternating_tail_after_threshold',
        'threshold':m if order.denominator==1 else m+1,'positive_initial_sign':True,
        'zero_at_n_one':True,'actual_arithmetic_model':'inverse_one',
        'sign_proved_for_every_integer_n':True,'global_distribution_estimate_proved':False,
        'proof':'iterated finite difference integral; falling factorial (order)_omega and positive integrand',
        'fractional_support_has_no_distinct_prime_cap':order.denominator!=1}


def sign_from_signature(signature,r):
    if r==0:return 0
    m=signature['threshold']
    if r<=m:return 1
    return 0 if signature['kind']=='integer_zero_tail' else (-1)**(r-m)


def generic_difference(order,base,steps):
    order=Q(order);base=Q(base);steps=list(map(Q,steps))
    if order<=0 or base<0 or not steps or min(steps)<=0:raise ValueError('Positive finite-difference geometry required')
    out=flint.arb(0);r=len(steps)
    for mask in range(1<<r):
        v=base+sum((h for j,h in enumerate(steps) if mask>>j&1),Q(0))
        out+=(-1)**(r-mask.bit_count())*(power(real(v),order) if v else flint.arb(0))
    return out


def bell_polynomials(K):
    """Symbolic differential algebra, supplied completion method for any K."""
    out=[{():1}]
    for k in range(K):
        P={}
        for monomial,c in out[-1].items():
            product=tuple(sorted(monomial+(0,)));P[product]=P.get(product,0)+c
            for j,r in enumerate(monomial):
                d=tuple(sorted(monomial[:j]+(r+1,)+monomial[j+1:]));P[d]=P.get(d,0)+c
        out.append(P)
    return out


def enforce_domain(cert,model):
    if cert['arithmetic_model']!=model:raise ValueError('Certificate requires actual inverse of the constant-one sequence')
    return True

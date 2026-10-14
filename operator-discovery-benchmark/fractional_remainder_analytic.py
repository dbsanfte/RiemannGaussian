"""Native enclosures of the entire pole-subtracted fractional numerator.

Uses a difference integral, a Cauchy-certified Taylor piece, and explicit
infinite tails. The independent checker uses the derivative representation.
"""
from fractions import Fraction as Q
import flint
from prime_error_grammar import real, serialize


def entire_jet(s, length):
    old = flint.ctx.cap
    flint.ctx.cap = max(old, length+1)
    try:
        return flint.acb_series([s,1],prec=length).zeta(deflate=True)
    finally:
        flint.ctx.cap=old


def entire(s):
    return entire_jet(s,1)[0]-1


def numerator(alpha, sigma, height, K=80, U=64, terms=16):
    """N_alpha(s)=sum(log n)^alpha/n^s-Gamma(alpha+1)/(s-1)^(alpha+1).

    The expression on the right initially requires Re(s)>1. The enclosure
    uses its entire continuation in s for real 0<=alpha<=1.
    """
    alpha,sigma,height=map(Q,(alpha,sigma,height))
    if not 0<=alpha<=1 or K<8 or terms<2 or U<=1:
        raise ValueError("Unsupported numerator enclosure parameters")
    s=flint.acb(real(sigma),real(height)); A=entire(s)
    if alpha==0:
        return A,{"method":"native deflated zeta minus one","alpha":"0","query":[str(sigma),str(height)]}
    if alpha==1:
        return -entire_jet(s,2)[1],{"method":"native negative derivative of deflated zeta","alpha":"1","query":[str(sigma),str(height)]}
    d=Q(1,64);r=2*d
    z=flint.acb(flint.arb(0,real(r)),flint.arb(0,real(r)))
    M=entire(s+z).abs_upper()
    if not M.is_finite():raise ArithmeticError("Nonfinite local Cauchy numerator bound")
    jet=entire_jet(s,K+1)
    small=-sum((jet[k]*real(d)**real(k-alpha)/real(k-alpha) for k in range(1,K+1)),flint.acb(0))
    small_error=M*real(d)**real(-alpha)*real(d/r)**(K+1)/real((K+1-alpha)*(1-d/r))
    def integrand(v, analytic):
        return (A-entire(s+v.exp()))*(-real(alpha)*v).exp()
    middle=flint.acb.integral(integrand,real(d).log(),real(U).log(),
        rel_tol=real(Q(1,2**100)),abs_tol=real(Q(1,2**100)),eval_limit=200000,depth_limit=50)
    if not middle.is_finite():raise ArithmeticError("Native difference integral unresolved")
    q=-(s-1)/U; qr=q.abs_upper()
    if not qr<1:raise ValueError("Tail start must exceed |s-1|")
    rational=real(U)**real(-alpha-1)*sum((q**k/real(alpha+k+1) for k in range(K+1)),flint.acb(0))
    rational_error=real(U)**real(-alpha-1)*qr**(K+1)/(real(alpha+K+2)*(1-qr))
    zeta_tail=sum(((-s*real(n).log()).exp()*real(n).log()**real(alpha)*
        (real(U)*real(n).log()).gamma_upper(-real(alpha)) for n in range(2,terms+1)),flint.acb(0))
    p=sigma+U
    if p<=1:raise ValueError("Tail Dirichlet majorant needs real part greater than one")
    zeta_error=real(U)**real(-alpha-1)/real(terms+1).log()*real(terms)**real(1-p)/real(p-1)
    tail=A*real(U)**real(-alpha)/real(alpha)+rational-zeta_tail
    pref=real(alpha)*(1-real(alpha)).rgamma()
    total=small+middle+tail
    error=(small_error+rational_error+zeta_error)*pref
    result=total*pref+flint.acb(flint.arb(0,error.upper()),flint.arb(0,error.upper()))
    if not result.is_finite():raise ArithmeticError("Nonfinite entire numerator enclosure")
    return result,{"method":"difference integral with local Cauchy and explicit infinite tails",
        "alpha":str(alpha),"query":[str(sigma),str(height)],"Taylor_order":K,"tail_start":U,"explicit_tail_terms":terms,
        "local_Cauchy_radius":str(r),"local_Cauchy_bound_ball":serialize(M),
        "small_remainder_ball":serialize(small_error),"rational_tail_remainder_ball":serialize(rational_error),
        "Dirichlet_tail_remainder_ball":serialize(zeta_error),"numerator_ball":{"real":serialize(result.real),"imag":serialize(result.imag)},
        "deflated_zeta_crosses_one_analytically":True,"scope":"finite native query, not uniform in height"}

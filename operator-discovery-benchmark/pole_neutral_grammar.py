"""Signed coefficient roots and shifted fractional logarithmic integrals.

For a>0, b>=0 and real kappa, this has the initial Mellin transform
zeta(s)^(-a)*(s-kappa)^(-b)/s. The pointwise root of a cumulative sum is
a different production. Universal signed growth premises are not asserted.
"""
from fractions import Fraction as Q
import flint
from exact_arithmetic import normalized_power
from estimate_grammar import inverse_one_prefix

VERSION="coefficient-roots-and-fractional-log-kernels-v1"
def real(x):
    x=Q(x);return flint.arb(x.numerator)/x.denominator


def coefficients(a,N):
    a=Q(a)
    if not 0<a<=1:raise ValueError("This pilot's coefficient bound uses 0<a<=1")
    return normalized_power(list(map(Q,inverse_one_prefix(N))),a)


def kernel(b,kappa,u):
    b,kappa=Q(b),Q(kappa)
    if not 0<=b<=1:raise ValueError("This pilot uses 0<=b<=1")
    if u==0:return flint.arb(1) if b==0 else flint.arb(0)
    if not u>0:raise ValueError("The real logarithmic kernel requires u>=0")
    if b==0:return flint.arb(1)
    # K_b,kappa(u)=integral_0^u exp(kappa*v)*v^(b-1)/Gamma(b) dv.
    value=u.root(b.denominator)**b.numerator*(real(b)+1).rgamma()*(real(kappa)*u).hypgeom_1f1(real(b),real(b+1))
    if not value.is_finite():raise ArithmeticError("Fractional logarithmic kernel was not finite")
    return value


def values(coefficients_by_a,b,kappa,points):
    """Complete arithmetic sums at each point, sharing kernels across roots."""
    b,kappa=Q(b),Q(kappa)
    converted={a:[real(v) for v in f] for a,f in coefficients_by_a.items()}
    out={a:{} for a in converted}
    for x in points:
        if type(x)is not int or x<1:raise ValueError("An integer point is required")
        if any(x>=len(f) for f in converted.values()):raise ValueError("Point exceeds complete coefficient prefix")
        totals={a:flint.arb(0) for a in converted}
        for n in range(1,x+1):
            weight=kernel(b,kappa,(real(x)/n).log())
            for a,f in converted.items():totals[a]+=f[n]*weight
        for a in converted:out[a][x]=totals[a]
    return out


def point_value(f,b,kappa,x):
    return values({Q(1):f},b,kappa,[x])[Q(1)][x]


def serialize(x):
    return (x+flint.arb(0,real(Q(1,2**180))*(1+abs(x)))).str(45)


def transfer(a,b,kappa,theta,C,offset):
    a,b,kappa,theta,C,offset=map(Q,(a,b,kappa,theta,C,offset))
    if not 0<a<=1 or not 0<=b<=1 or theta<0 or C<=0:raise ValueError("Invalid fractional coefficient or growth parameters")
    increment_exponent=max(kappa-1,Q(0)) if b else Q(0)
    eta=max(theta,increment_exponent)
    E=real(0) if b==0 else real(4+4/b)*real(b).rgamma()*real(2)**real(increment_exponent)
    one_order=a-b if b and kappa==1 else a
    obstructions=[]
    if eta<1 and (one_order.denominator!=1 or one_order<0):
        obstructions.append({"location":"1","kind":"uncancelled_zeta_pole_branch_or_pole","local_order":str(one_order)})
    if b and kappa!=1 and kappa>eta:
        obstructions.append({"location":str(kappa),"kind":"introduced_kernel_branch_or_pole","local_order":str(-b)})
    return {"a":str(a),"b":str(b),"kappa":str(kappa),"theta":str(theta),"constant":str(C),"offset":str(offset),
        "mellin_exponent":str(eta),"increment_exponent":str(increment_exponent),"increment_constant_ball":E.str(45),
        "integer_premise":"For every integer n>=1, |G(n)-offset|<=C*n^theta",
        "real_extension":"|G(t)-offset|<=C*t^theta+E*t^lambda*(1+log t) for every real t>=1",
        "root_identity":"zeta(s)^(a*m)*(s-kappa)^(b*m)*(s*Mellin(G-offset)+offset)^m=1, for m clearing both denominators",
        "zero_multiplicities_preserved":True,"local_divisor_obstructions":obstructions,
        "RH_sufficient_if_uniform":bool(eta<=Q(1,2) and not obstructions),
        "uniform_integer_signed_bound_proved":False,"RH_proved":False}


def reciprocal_cost(cert,sigma,height):
    a,b,kappa,theta,C,offset=map(Q,(cert[k] for k in ("a","b","kappa","theta","constant","offset")))
    sigma,height=Q(sigma),Q(height);lam=Q(cert["increment_exponent"])
    if sigma<=max(theta,lam,0):raise ValueError("Cost line lies outside the conditional domain")
    E=flint.arb(cert["increment_constant_ball"])
    B=real(C)/real(sigma-theta)+E*(1/real(sigma-lam)+1/real(sigma-lam)**2)
    s=flint.acb(real(sigma),real(height))
    return (abs(s)*B+real(abs(offset)))**real(1/a)*abs(s-real(kappa))**real(b/a)

"""Fractional arithmetic logarithms with continuous quadrature subtraction.

This is a supplied grammar/proof backend, not an autonomous proof generator.
Its recovery theorem requires infinitely many orders; finite probes never
establish that premise. Rational orders have no semantic denominator cap.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial

import flint
from fractional_prime_grammar import forward
from prime_error_grammar import real, serialize

VERSION = "fractional-discrete-continuous-remainders-and-parameter-pole-recovery-v1"


def complex_ball(z):
    return {"real":serialize(z.real),"imag":serialize(z.imag)}


def power(x, exponent):
    exponent = Q(exponent)
    if exponent == 0:
        return flint.arb(1)
    if x == 0 and exponent > 0:
        return flint.arb(0)
    return x.root(exponent.denominator) ** exponent.numerator


def canonical(c, b=None):
    c = list(map(Q, c)); b = c.copy() if b is None else list(map(Q, b))
    if not c or len(c) != len(b) or not any(c+b):
        raise ValueError("Equal nonempty, nonzero rational coefficient vectors required")
    while len(c) > 1 and not c[-1] and not b[-1]:
        c.pop(); b.pop()
    divisor = next(v for v in c+b if v)
    c = [v/divisor for v in c]; b = [v/divisor for v in b]
    D = len(c)-1
    paired = all(c[j] == b[j] for j in range(1, D+1))
    rate = None
    moments = []
    if paired:
        if b[0] != c[0]:
            rate = 0
        else:
            for k in range(D+1):
                moment = sum((v*j**k for j, v in enumerate(c)), Q(0))
                moments.append(str(moment))
                if moment:
                    rate = k
                    break
    return {"coefficients":list(map(str, c)), "normalizers":list(map(str, b)),
            "degree":D, "positive_orders_compensated":paired,
            "parameter_vanishing_order":rate, "parameter_moments_through_first_nonzero":moments,
            "order_schedule":"a_q=1/(max(1,D)*q), every integer q>=2",
            "zero_order_convention":"D_0(1)=0; D_0(n)=1 for n>=2; T_0=delta_1-mu",
            "domain":"x>=1; 0<=a<=1/max(1,D); order j*a<=1"}


def order(p, q, j):
    if not isinstance(q, int) or q < 2:
        raise ValueError("The infinite order schedule requires integer q>=2")
    return Q(j, max(1, p["degree"])*q)


def normalizer(alpha, x):
    alpha, x = Q(alpha), Q(x)
    if not 0 <= alpha <= 1 or x < 1:
        raise ValueError("Normalizer domain: 0<=alpha<=1, x>=1")
    if x == 1:
        return flint.arb(0)
    u = real(x).log()
    if alpha == 0:
        return real(x-1)
    if alpha == 1:
        return real(x)*u-real(x)+1
    return power(u, alpha+1)/real(alpha+1)*u.hypgeom_1f1(real(alpha+1), real(alpha+2))


def primitive_tables(mu, alphas, points):
    """Every divisor and every Mobius term is used; no sample quadrature."""
    points = list(map(Q, points)); N = len(mu)-1
    if not mu[0] == 0 or not mu[1] == 1 or max(points, default=Q(1)) >= N+1:
        raise ValueError("Complete constant-one inverse prefix required")
    convolution=[0]*(N+1)
    for d in range(1,N+1):
        for n in range(d,N+1,d):convolution[n]+=mu[d]
    if convolution[1:]!=[1]+[0]*(N-1):
        raise ValueError("The supplied coefficients are not the constant-one Dirichlet inverse")
    ones = [flint.arb(0)]+[flint.arb(1)]*N
    out = {}
    for alpha in sorted(set(map(Q, alphas))):
        if not 0 <= alpha <= 1:
            raise ValueError("Fractional primitive orders must be in [0,1]")
        T, _ = forward(ones, alpha)
        S = [flint.arb(0)]*(N+1)
        for n in range(1, N+1):
            S[n] = S[n-1]+T[n]
        rows = {}
        for x in points:
            top = x.numerator//x.denominator
            G = sum((real(mu[d])*normalizer(alpha, x/d) for d in range(1, top+1) if mu[d]), flint.arb(0))
            rows[str(x)] = {"discrete":serialize(S[top]), "continuous":serialize(G),
                            "remainder":serialize(S[top]-G)}
        out[str(alpha)] = rows
    return out


def response(p, tables, qs, points):
    rows = {}
    for q in qs:
        for x in map(Q, points):
            value = flint.arb(0)
            for j, (c, b) in enumerate(zip(p["coefficients"], p["normalizers"])):
                if not Q(c) and not Q(b):
                    continue
                cell = tables[str(order(p, q, j))][str(x)]
                value += real(c)*flint.arb(cell["discrete"])-real(b)*flint.arb(cell["continuous"])
            rows[f"{q}:{x}"] = serialize(value)
    return rows


@lru_cache(maxsize=None)
def cauchy_boxes(rho, mesh, precision):
    """A finite cover of the full Cauchy rectangle, with native upper bounds."""
    rho = Q(rho)
    if not 0 < rho < 1 or mesh < 1:
        raise ValueError("0<rho<1 and positive mesh required")
    if flint.ctx.prec != precision:
        raise ValueError("Explicit native precision must match the certificate cache")
    rows = []; maxima = [Q(0)]*3
    nx = (Q(1)+2*rho)*mesh
    ny = 2*rho*mesh
    nx = (nx.numerator+nx.denominator-1)//nx.denominator
    ny = (ny.numerator+ny.denominator-1)//ny.denominator
    for i in range(nx):
        for j in range(ny):
            lo = -rho+(1+2*rho)*Q(i,nx); hi = -rho+(1+2*rho)*Q(i+1,nx)
            bottom = -rho+2*rho*Q(j,ny); top = -rho+2*rho*Q(j+1,ny)
            z = flint.acb(flint.arb(real((lo+hi)/2), real((hi-lo)/2)),
                          flint.arb(real((bottom+top)/2), real((top-bottom)/2)))
            vals = [(z*(1-z).rgamma()).abs_upper(), (z*(2-z).rgamma()).abs_upper(),
                    (1-z).rgamma().abs_upper()]
            if not all(v.is_finite() for v in vals):
                raise ArithmeticError("Unresolved reciprocal-gamma cover")
            for k, v in enumerate(vals):
                upper = Q(int((v.upper()*2**80).ceil().fmpz()),2**80)
                maxima[k] = max(maxima[k],upper)
            rows.append({"rectangle":list(map(str,(lo,hi,bottom,top))), "upper_balls":list(map(serialize,vals))})
    M1, M2, M3 = map(real,maxima)
    C0 = M1/real(2*(1-rho))+M1/(2*real(2).log()**2)+M2+M3
    return {"rho":str(rho), "mesh":mesh, "precision":precision,
            "boxes":rows, "maxima_rational_upper":list(map(str,maxima)), "C0_ball":serialize(C0),
            "domain":"every n>=2; every real beta in [0,1]; all derivative orders r>=0",
            "coefficient_derivative_bound":"|d_beta^r T_beta(n)|<=r!*rho^(-r)*C0*log(e+n)^2",
            "uses_exact_prime_factor_sign_structure":True, "uses_prime_distribution_estimate":False}


def global_certificate(p, covers):
    """Automatic weak all-scale theorems and parameter-sensitive increments."""
    c,b=list(map(Q,p["coefficients"])),list(map(Q,p["normalizers"]))
    Sc,Sb=sum(map(abs,c),Q(0)),sum(map(abs,b),Q(0))
    r=p["parameter_vanishing_order"]
    if r is None or r == 0:
        W=real(Sc+Q(3,2)*Sb); I=real(Sc+6*Sb); r=0; ell=2; rho=None; Sr=None
    else:
        Sr=sum((abs(v)*j**r for j,v in enumerate(c)),Q(0))
        cover=min(covers,key=lambda z:float((flint.arb(z["C0_ball"])*real(Q(z["rho"]))**(-r)).upper()))
        rho=cover["rho"]; cost=flint.arb(cover["C0_ball"])*real(Q(rho))**(-r)
        W=real(Sr)*(cost+1+real(Q(1,(r+2)*factorial(r))))
        I=real(Sr)*(cost+real(Q(2,factorial(r)))+4); ell=r+2
    return {"status":"proved_weak_all_scale_signed_family_and_unit_increment_bounds",
            "parameter_power":r, "growth_power":"1", "log_power":ell,
            "constant_ball":serialize(W), "unit_increment_constant_ball":serialize(I),
            "selected_Cauchy_radius":rho, "absolute_parameter_moment":str(Sr) if Sr is not None else None,
            "weak_bound":"|V_a(x)|<=W*a^r*x*log(e+x)^ell",
            "increment_bound":"|V_a(t)-V_a(N)|<=I*a^r*log(e+N+1)^ell, N<=t<=N+1",
            "domain":"every real x>=1; every real 0<=a<=1/max(1,D)",
            "uses_signed_parameter_cancellation":r>0,
            "ordinary_zeta_exponent":"1", "RH_sufficient":False, "RH_proved":False}


def transfer(p, theta, kappa, ell, C):
    theta,kappa,ell,C=map(Q,(theta,kappa,ell,C))
    if ell<0 or C<=0:
        raise ValueError("Nonnegative log loss and positive constant required")
    eta=max(theta,Q(0)); D=p["degree"]; r=p["parameter_vanishing_order"]
    bad=[j for j,(c,b) in enumerate(zip(p["coefficients"],p["normalizers"])) if j>0 and Q(c)!=Q(b)]
    if bad and eta<1: status="ruled_out_by_uncompensated_fractional_pole_at_one"
    elif bad: status="unsupported_family_zero_bridge_for_uncompensated_positive_orders"
    elif kappa>r: status="ruled_out_by_exact_parameter_vanishing_order"
    elif eta<Q(1,2): status="ruled_out_by_actual_critical_zero_and_infinite_parameter_family"
    elif eta<=Q(1,2): status="RH_sufficient_infinite_family_obligation_missing_uniform_proof"
    else: status="infinite_family_signed_obligation_above_RH_threshold"
    pole_index=max((j for j,c in enumerate(p["coefficients"]) if Q(c)),default=0)
    return {"theta":str(theta),"parameter_power":str(kappa),"log_power":str(ell),"constant":str(C),
            "ordinary_zeta_exponent":str(eta),"analytic_status":status,
            "exact_parameter_vanishing_order":r,"positive_order_mismatches":bad,
            "numerator_parameter_pole_location":str(Q(-1,pole_index)) if pole_index else None,
            "numerator_parameter_pole_residue":str(-Q(p["coefficients"][pole_index])/pole_index) if pole_index else None,
            "zero_recovery":"parameter identity theorem and nonzero pole residue" if D else "real rational numerator nonzero at every nonreal ordinary zeta zero",
            "required_uniform_scope":"every integer n>=1 AND every integer q>=2",
            "finite_parameter_grid_suffices":False if D else True,
            "uniform_constant_in_q_required_for_parameter_rate_claim":True,
            "all_height_scalar_multiplier_nonvanishing_required":False,
            "RH_sufficient_if_uniform":not bad and kappa<=r and eta==Q(1,2),
            "uniform_signed_premise_proved":False,"RH_proved":False}


def mellin_majorant(exponent, log_power, constant, sigma):
    exponent,log_power,sigma=map(Q,(exponent,log_power,sigma))
    if sigma<=exponent:
        raise ValueError("Mellin majorant needs a positive real gap")
    m=(log_power.numerator+log_power.denominator-1)//log_power.denominator
    l=(flint.arb.const_e()+1).log()
    return constant*sum((real(comb(m,j)*factorial(j))*l**(m-j)/real(sigma-exponent)**(j+1)
                         for j in range(m+1)),flint.arb(0))


def recovery_cost(p,tr,cert,numerators,sigma,height,qs):
    """Finite native observations charge the denominator, order and increments.

    This conditional cost is scoped to each query. It is not a bound uniform
    in height, and a failed finite denominator probe does not disprove a lead.
    """
    sigma,height=map(Q,(sigma,height));s=flint.acb(real(sigma),real(height));costs=[];unresolved=[]
    for q in qs:
        a=Q(1,max(1,p["degree"])*q)
        A=numerators["0"]
        Qs=real(p["coefficients"][0])*(A+1/(s-1))-real(p["normalizers"][0])/(s-1)
        for j,c in enumerate(p["coefficients"][1:],1):
            if Q(c): Qs+=real(c)*numerators[str(j*a)]
        lower=Q(int((Qs.abs_lower().lower()*2**80).floor().fmpz()),2**80)
        if not lower>0:
            unresolved.append(q);continue
        # Integer-to-real conversion: n^theta <= 2^max(0,-theta) x^theta;
        # log(e+n)<=log(e+x). The unit correction has real exponent zero.
        H=mellin_majorant(Q(tr["theta"]),Q(tr["log_power"]),
            real(tr["constant"])*power(real(a),Q(tr["parameter_power"]))*power(real(2),max(Q(0),-Q(tr["theta"]))),sigma)
        H+=mellin_majorant(Q(0),Q(cert["log_power"]),flint.arb(cert["unit_increment_constant_ball"])*
            power(real(a),cert["parameter_power"])*real(2)**cert["log_power"],sigma)
        cost=s.abs_upper()*H/real(lower)
        costs.append({"q":q,"order":str(a),"numerator_ball":complex_ball(Qs),"numerator_lower_rational":str(lower),"numerator_lower_ball":serialize(real(lower)),
                      "conditional_reciprocal_zeta_bound_ball":serialize(cost)})
    return {"query":[str(sigma),str(height)],"parameter_observers":costs,"unresolved_denominator_orders":unresolved,
            "best_conditional_reciprocal_zeta_bound_ball":min((v["conditional_reciprocal_zeta_bound_ball"] for v in costs),
                key=lambda v:float(flint.arb(v).upper())) if costs else None,
            "charges_parameter_normalization_and_unit_increment":True,"scope":"one native complex query; conditioned on the full infinite-family bound",
            "height_uniform":False,"uniform_signed_premise_proved":False}

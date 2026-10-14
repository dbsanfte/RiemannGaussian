"""Conditional signed-energy recurrence certificates, including log losses."""
from fractions import Fraction as Q
import flint


def real(x): x=Q(x); return flint.arb(x.numerator)/x.denominator


def certificate(q,rho,gamma,B,initial_energy):
    if type(q) is not int or q<2 or q%2: raise ValueError("An even q>=2 is required")
    rho,gamma,B,A1=map(Q,(rho,gamma,B,initial_energy))
    if B<0 or A1<0: raise ValueError("The defect cost and initial energy must be nonnegative")
    critical=Q(q,2)+1; scale=2**int(critical)
    sufficient=rho<=scale and gamma<=critical
    impossible_if_zero_nonzero=max(rho,Q(0))<scale and gamma<critical
    return {"q":q,"rho":str(rho),"gamma":str(gamma),"B":str(B),"A_1":str(A1),
            "premise":"For every dyadic X>=1, A_q(2X)-rho*A_q(X)<=B*X^gamma",
            "critical_energy_exponent":str(critical),"critical_recurrence_multiplier":scale,
            "RH_sufficient_with_global_zero_bridge":sufficient,
            "strictly_subcritical_recurrence_ruled_out_if_critical_zero_multiplier_nonzero":impossible_if_zero_nonzero,
            "conclusion":"If the recurrence premise holds and rho<=2^(q/2+1), gamma<=q/2+1, then A_q(2^j)<=(2^j)^(q/2+1)*(A_1+B*j/2^(q/2+1)), and the direct Mellin transform is holomorphic on Re(s)>1/2",
            "uniform_signed_recurrence_premise_proved":False,"RH_proved":False}


def dyadic_majorant(cert,j):
    if type(j) is not int or j<0 or not cert["RH_sufficient_with_global_zero_bridge"]:
        raise ValueError("A nonnegative dyadic index and certified conditional regime are required")
    scale=cert["critical_recurrence_multiplier"]
    return Q(scale**j)*(Q(cert["A_1"])+Q(cert["B"])*j/scale)


def mellin_majorant(cert,sigma):
    sigma=Q(sigma)
    if sigma<=Q(1,2) or not cert["RH_sufficient_with_global_zero_bridge"]:
        raise ValueError("A line sigma>1/2 in the conditional regime is required")
    scale=cert["critical_recurrence_multiplier"]
    norm=(real(Q(cert["A_1"])+Q(cert["B"])/scale))**real(Q(1,cert["q"]))
    ratio=real(2)**real(Q(1,2)-sigma)
    return norm/(1-ratio)**2

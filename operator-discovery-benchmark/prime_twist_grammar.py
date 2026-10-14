"""Fractional arithmetic twists, independent normalizers, and zeta recovery."""
from fractions import Fraction as Q
from math import ceil,comb,factorial
import hashlib
import json
import flint
from prime_error_grammar import real,serialize

VERSION="fractional-prime-twists-and-right-shift-zero-recovery-v1"


def semantics_digest(p):
    names=("channel","delta","coefficients","normalizers","leading_index","leading_shift","increment_shift","normalizer_exponents")
    return hashlib.sha256(json.dumps({k:p[k] for k in names},sort_keys=True,separators=(",",":"),allow_nan=False).encode()).hexdigest()


def canonical(delta,c,b,channel="weighted"):
    delta=Q(delta);c=list(map(Q,c));b=list(map(Q,b))
    if channel not in ("weighted","log") or delta<=0 or len(c)!=len(b) or not c or not any(c):raise ValueError("Typed positive rational shift and equal nonzero coefficient vectors required")
    while len(c)>1 and c[-1]==0 and b[-1]==0:c.pop();b.pop()
    leading=next(j for j,v in enumerate(c) if v)
    divisor=c[leading]
    c=[v/divisor for v in c];b=[v/divisor for v in b]
    if len(c)==1:delta=Q(1)
    active=next(j for j,(v,w) in enumerate(zip(c,b)) if v or w)
    return {"channel":channel,"delta":str(delta),"coefficients":list(map(str,c)),"normalizers":list(map(str,b)),"leading_index":leading,
        "increment_shift":str(active*delta),
        "leading_shift":str(leading*delta),"normalizer_exponents":[str(1-j*delta) for j in range(len(c))]}


def twist(n,exponent):
    exponent=Q(exponent)
    if n<1:raise ValueError("A positive index is required for a real fractional twist")
    return real(n).root(exponent.denominator)**(-exponent.numerator)


def polynomial_range(coefficients):
    """Exact Bernstein certificates on [0,1]; failure is not negativity."""
    c=list(map(Q,coefficients));degree=len(c)-1
    for m in range(degree,max(degree,1)+5):
        bs=[sum((c[j]*Q(comb(k,j),comb(m,j)) for j in range(min(k,degree)+1)),Q(0)) for k in range(m+1)]
        if min(bs)>=0 and max(bs)<=1:
            return {"status":"proved_between_zero_and_one","degree":m,"bernstein_coefficients":list(map(str,bs)),
                "domain":"every real z in [0,1]","strictly_positive_in_open_interval":any(bs)}
    return {"status":"unresolved_by_declared_Bernstein_budget","domain":"[0,1]"}


def normalizer(alpha,x,channel="weighted"):
    alpha,x=Q(alpha),Q(x)
    if x<2:return real(0)
    u,u0=real(x).log(),real(2).log()
    if channel=="log":return u-u0 if not alpha else ((real(alpha)*u).exp()-(real(alpha)*u0).exp())/real(alpha)
    if not alpha:return u.log()-u0.log()
    return (real(alpha)*u).ei()-(real(alpha)*u0).ei()


def tables(f,ps,points):
    if len(f)<2 or f[0]!=0 or f[1]!=0:raise ValueError("A complete logarithmic coefficient prefix with f(0)=f(1)=0 is required")
    shifts=sorted({Q(p["delta"])*j for p in ps for j in range(len(p["coefficients"]))})
    N=len(f)-1
    prefixes={}
    for channel,shift in sorted({(p["channel"],j*Q(p["delta"])) for p in ps for j in range(len(p["coefficients"]))}):
        row=[real(0)]*(N+1)
        for n in range(1,N+1):row[n]=row[n-1]+real(f[n])*twist(n,shift)*(real(n).log() if channel=="log" else 1) if f[n] else row[n-1]
        prefixes[channel,shift]=row
    kernels={(channel,alpha):{str(x):normalizer(alpha,x,channel) for x in points}
        for channel,alpha in {(p["channel"],Q(v)) for p in ps for v in p["normalizer_exponents"]}}
    return prefixes,kernels


def observe(ps,f,points):
    prefixes,kernels=tables(f,ps,points);out={}
    for p in ps:
        delta=Q(p["delta"]);rows={}
        for n in points:
            value=sum((real(v)*kernels[p["channel"],Q(alpha)][str(n)] for v,alpha in zip(p["normalizers"],p["normalizer_exponents"])),real(0))
            value-=sum((real(v)*prefixes[p["channel"],j*delta][n-1] for j,v in enumerate(p["coefficients"])),real(0))
            rows[str(n)]=serialize(value)
        out[p["id"]]=rows
    return out


def weak_uniform_bound(p,Cp):
    """A proved norm bound; its original-zeta exponent is at least one."""
    nu=Q(p["leading_shift"]);r=p["leading_index"]
    if any(Q(v) for v in p["normalizers"][:r]):return {"status":"unsupported_normalizers_precede_leading_twist"}
    Sc=sum(map(abs,map(Q,p["coefficients"])),Q(0));Sb=sum(map(abs,map(Q,p["normalizers"])),Q(0));Cp=Q(Cp)
    divisor=real(2).log() if p["channel"]=="weighted" else real(1)
    if nu<1:
        theta,ell=1-nu,Q(0);bound=real(Sc*Cp+Sb)/real(1-nu)/divisor
    elif nu==1:
        theta,ell=Q(0),Q(1);bound=2*real(Sc*Cp+Sb)/divisor
    else:
        theta,ell=Q(0),Q(0);bound=real(Sc*Cp*nu+Sb)/real(nu-1)/divisor
    C=Q(int((bound.upper()*1024).ceil().fmpz()),1024)
    return {"status":"proved_all_scale_signed_output_bound_by_absolute_majorants","theta":str(theta),"log_power":str(ell),
        "constant":str(C),"unrounded_constant_ball":serialize(bound),"domain":"every real x>=1",
        "ordinary_zeta_exponent_after_shift_recovery":str(theta+nu),"uses_signed_cancellation":False,
        "RH_sufficient":theta+nu<=Q(1,2),"RH_proved":False}


def offset_value(A):
    return real(A["value"]) if A["kind"]=="rational" else flint.arb(A["value_ball"])


def finite_part_center(p):
    """Required centering at s=0, derived from the Mellin expression."""
    result=real(0);delta=Q(p["delta"])
    for j,(c,b) in enumerate(zip(p["coefficients"],p["normalizers"])):
        c,b=Q(c),Q(b);shift=j*delta;kappa=1-shift
        if p["channel"]=="log":
            if not kappa:
                if c!=b:return None
                result+=real(c)*flint.arb.const_euler()-real(b)*real(2).log()
            else:
                if b:result-=real(b)*real(2)**real(kappa)/real(kappa)
                if c:
                    value=real(shift)
                    result+=real(c)*flint.arb_series([value,1],prec=2).zeta()[1]/value.zeta()
        else:
            if kappa>=0 and c!=b:return None
            B=(-flint.arb.const_euler()-real(2).log().log() if not kappa else
                -(real(kappa)*real(2).log()).ei()+abs(real(kappa)).log())
            result+=real(b)*B
            if c!=b:result+=real(c-b)*real(-kappa).log()
            if c:
                F=real(1) if shift==1 else real(shift-1)*real(shift).zeta()
                assert F>0
                result-=real(c)*F.log()
    return {"kind":"Mellin_finite_part_at_zero","value_ball":serialize(result),
        "semantic_digest":semantics_digest(p),
        "semantics":"exact real expression determined by the compiled Mellin finite part; the ball is an enclosure"}


def transfer(p,theta,ell,C,A=None):
    theta,ell,C=map(Q,(theta,ell,C));A=A or {"kind":"rational","value":"0"}
    if ell<0 or C<=0:raise ValueError("A nonnegative log exponent and positive bound constant required; growth exponents may be negative")
    delta=Q(p["delta"]);nu=Q(p["leading_shift"]);r=p["leading_index"]
    incnu=Q(p["increment_shift"]);output_eta=max(theta,-incnu);eta=output_eta+nu
    poles=[{"location":str(1-j*delta),"residue":str(Q(c)-Q(b))} for j,(c,b) in enumerate(zip(p["coefficients"],p["normalizers"])) if 1-j*delta>output_eta and Q(c)!=Q(b)]
    centre=finite_part_center(p) if output_eta<0 else None
    bad_centre=output_eta<0 and (centre is None or A["kind"]!="Mellin_finite_part_at_zero" or A.get("semantic_digest")!=semantics_digest(p))
    if poles:status="uniform_claim_ruled_out_by_shifted_pole_logarithm"
    elif bad_centre:status="negative_growth_obligation_missing_exact_Mellin_center_certificate"
    elif eta<Q(1,2):status="uniform_claim_ruled_out_by_actual_critical_zero_and_right_shift_recovery"
    elif eta<=Q(1,2):status="RH_sufficient_prime_twist_obligation_missing_uniform_signed_proof"
    else:status="signed_prime_twist_obligation_above_RH_threshold"
    Sc=sum(map(abs,map(Q,p["coefficients"])),Q(0));Sb=sum(map(abs,map(Q,p["normalizers"])),Q(0))
    increment=real(Sc+Sb) if p["channel"]=="log" else real(Sc)+real(Sb)/real(2).log()
    return {"theta":str(theta),"log_power":str(ell),"constant":str(C),"offset":A,
        "output_mellin_exponent":str(output_eta),"leading_shift_recovery_cost":str(nu),"ordinary_zeta_exponent":str(eta),
        "integer_to_real_bound_factor_ball":serialize(real(2)**real(max(Q(0),-theta))),
        "increment_shift":str(incnu),"increment_log_power":1 if p["channel"]=="log" else 0,
        "uncancelled_pole_residues_in_output_half_plane":poles,"increment_cost_ball":serialize(increment),
        "ordinary_zero_recovery":"finite right-shift multiplicity chain; arbitrary isolated shifted-zero coincidences allowed",
        "leading_coefficient":p["coefficients"][r],"all_height_nonvanishing_required":False,
        "RH_sufficient_if_uniform":not poles and not bad_centre and eta<=Q(1,2),"analytic_status":status,
        "uniform_signed_premise_proved":False,"RH_proved":False}


def recovery_cost(p,tr,sigma,height,terminal_sigma=Q(9,8)):
    """Finite DAG recovery, including terminal Euler bounds and all paths."""
    sigma,height,terminal_sigma=map(Q,(sigma,height,terminal_sigma))
    theta=Q(tr["theta"]);ell=Q(tr["log_power"]);C=Q(tr["constant"]);A=offset_value(tr["offset"])
    nu=Q(p["leading_shift"]);delta=Q(p["delta"]);r=p["leading_index"]
    if sigma<=Q(tr["ordinary_zeta_exponent"]) or terminal_sigma<=1:raise ValueError("Recovery line must exceed the recovered Mellin exponent, with terminal real part>1")
    m=ceil(ell);l=(flint.arb.const_e()+1).log();increment=flint.arb(tr["increment_cost_ball"])
    incnu=Q(tr["increment_shift"]);spread=max(Q(0),terminal_sigma-sigma) if p["channel"]=="log" else Q(0)
    cache={};nodes=[]
    def bound(k):
        if k in cache:return cache[k]
        real_part=sigma+k*delta;z=flint.acb(real(real_part),real(height))
        if real_part>=terminal_sigma:
            if p["channel"]=="weighted":result=abs((z-1).log())+real(real_part).zeta().log()
            else:result=1/abs(z-1)-flint.arb_series([real(real_part),1],prec=2).zeta()[1]/real(real_part).zeta()
            kind="terminal_Euler_half_plane"
        else:
            s=z-real(nu);gap=real_part-nu-theta
            H=real(C)*flint.arb(tr["integer_to_real_bound_factor_ball"])*sum((real(comb(m,j)*factorial(j))*l**(m-j)/real(gap)**(j+1) for j in range(m+1)),real(0))
            hgap=real(real_part-nu+incnu)
            H+=increment*real(2)**real(incnu)*(l/hgap+1/hgap**2 if tr["increment_log_power"] else 1/hgap)
            result=(abs(s)+real(spread))*H+abs(A)
            for j,(c,b) in enumerate(zip(p["coefficients"],p["normalizers"])):
                kappa=1-j*delta;distance=s-real(kappa)
                # E1((s-kappa)log2)+log(s-kappa) is entire.
                base_cost=real(2).log()*max(real(1),real(2)**real(kappa-(real_part-nu)))
                entire_cost=(flint.arb.const_euler()+abs(real(2).log().log())+abs(distance)*base_cost if p["channel"]=="weighted" else base_cost)
                result+=real(abs(Q(b)))*entire_cost
                mismatch=Q(c)-Q(b)
                if mismatch:
                    if real_part-nu<=kappa:return None
                    result+=real(abs(mismatch))*(abs(distance.log()) if p["channel"]=="weighted" else 1/abs(distance))
            for j in range(r+1,len(p["coefficients"])):
                if Q(p["coefficients"][j]):
                    child=bound(k+j-r)
                    if child is None:return None
                    result+=real(abs(Q(p["coefficients"][j])))*child
            kind="charged_shift_recurrence"
        cache[k]=result
        nodes.append({"shift_index":k,"real_part":str(real_part),"kind":kind,
            "transform":"log_F" if p["channel"]=="weighted" else "logarithmic_derivative_F",
            "conditional_transform_bound_ball":serialize(result)})
        return result
    root=bound(0)
    if root is None:return None
    z=flint.acb(real(sigma),real(height))
    if p["channel"]=="log":
        end=z+real(spread)
        root=abs((end-1).log())+real(sigma+spread).zeta().log()+real(spread)*root
    cost=abs(z-1).log()+root
    return {"log_reciprocal_zeta_bound_ball":serialize(cost),"recurrence_nodes":sorted(nodes,key=lambda r:r["shift_index"]),
        "terminal_sigma":str(terminal_sigma),"full_shift_path_cost_charged":True,"horizontal_integration_width":str(spread),
        "scope":"conditional fixed-point reciprocal reconstruction bound, not a proved signed premise"}

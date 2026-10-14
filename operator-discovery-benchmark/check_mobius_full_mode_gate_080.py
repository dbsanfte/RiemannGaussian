"""Independent exact full rough-channel leading-mode obstruction080.

Analytic premise is the separately reviewed signed rough-Mobius theorem from
least-prime recursion+PNT and quantitative Mertens decay. No producer imports.
"""
from fractions import Fraction
import check_mobius_symbolic_cover_080 as C
import check_mobius_prime_mass_gate_078 as K
from check_mobius_prime_storage_073 import AdmissionError,ResourceLimit,_rational,_add,_mul,_divide
class Meter(C.Meter):pass
MERTENS_REFERENCE='https://arxiv.org/abs/2208.06141v5'

def _finish(out,m,error=None):
    out=C._done(out,m,error)
    out.update(arithmetic_residual_refuted=False,residual_lower_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False,finite_u_threshold_supplied=False)
    return out

def _log_bounds(r,m):
    z=_divide(_add(r,Fraction(-1),m),_add(r,Fraction(1),m),m);t=abs(z);square=_mul(t,t,m);term=t;lo=Fraction(0)
    for j in range(32):
        lo=_add(lo,_divide(_mul(Fraction(2),term,m),Fraction(2*j+1),m),m);term=_mul(term,square,m)
    hi=_add(lo,_divide(_mul(Fraction(2),term,m),_mul(Fraction(65),_add(Fraction(1),-square,m),m),m),m)
    return (-hi,-lo) if z<0 else (lo,hi)

def _floor_dyadic(v):return Fraction((v.numerator*2**40)//v.denominator,2**40)
def _ceil_dyadic(v):return Fraction(-((-v.numerator*2**40)//v.denominator),2**40)

def _rho(raw,m):
    keys={'mesh','bits','log_terms','lower_log_three','upper_riemann_summands','rho_three_upper'}
    if type(raw) is not dict or set(raw)!=keys:raise AdmissionError('exact rho certificate schema required')
    for key,v in [('mesh',64),('bits',40),('log_terms',32)]:
        if type(raw[key]) is not int or raw[key]!=v:raise AdmissionError('rho certificate constants mismatch')
    if type(raw['upper_riemann_summands']) is not list or len(raw['upper_riemann_summands'])!=64:raise AdmissionError('complete64 endpoint summands required')
    m.reserve(65536+sum(8*len(v) for v in raw['upper_riemann_summands'] if type(v) is str))
    lower=_floor_dyadic(_log_bounds(Fraction(3),m)[0]);summands=[]
    for i in range(1,65):
        v=Fraction(64+i,64);logupper=_log_bounds(v,m)[1];summands.append(_ceil_dyadic(_divide(logupper,_mul(Fraction(64),_add(v,Fraction(1),m),m),m)))
    upper=Fraction(1)-lower
    for v in summands:upper=_add(upper,v,m)
    if _rational(raw['lower_log_three'],'lower log3',m)!=lower or [_rational(v,'upper sum term',m) for v in raw['upper_riemann_summands']]!=summands or _rational(raw['rho_three_upper'],'rho3 upper',m)!=upper:raise AdmissionError('independent rho envelope mismatch')
    if not 0<upper<Fraction(1,16):raise AdmissionError('rho3 envelope insufficient')
    return upper

def verify_rho(rho_cert,meter=None):
    m=meter or Meter();out={}
    try:
        upper=_rho(rho_cert,m);out.update(status='VERIFIED_DICKMAN_ENVELOPE',rho_three_upper=str(upper),envelope='0<=rho(s)<=rho_three_upper for s>=3',analytic_premises=['Dickman differential-delay equation and positivity','rho decreasing','rho(3)=1-log3+integral1..2 log(v)/(v+1)dv','integrand increasing on[1,2]'],uniform_signed_control_proved=False)
    except (ValueError,TypeError,KeyError,OverflowError) as e:return _finish(out,m,e)
    return _finish(out,m)
verify_rho_envelope=verify_rho

def verify_full_mode(kernel,P,gamma,ray,logspec,rho_cert,certificate,meter=None):
    m=meter or Meter();out={'uniform_covariance_leaf_obstructed':False}
    try:
        rhoupper=_rho(rho_cert,m);r,lo,hi=C._log(logspec,m);g=_rational(gamma,'gamma',m);a=C._ray(ray,m);normalized=K._kernel(kernel,m);primes=C.F.F._primes(P,m)
        if type(P) is not list or list(primes)!=sorted(primes):raise AdmissionError('sorted excluded primes required')
        if not Fraction(1,2)<g<=Fraction(2,3):
            out.update(status='UNSUPPORTED',reason='full-mode domain1/2<gamma<=2/3 unpaid outside');return _finish(out,m)
        if any(any(v) for i,v in enumerate(a) if i not in (1,7,8,9)):
            out.update(status='UNSUPPORTED',reason='unproved additional channels');return _finish(out,m)
        expected=_divide(_add(Fraction(3),-_mul(Fraction(2),g,m),m),_mul(Fraction(2),g,m),m)
        if r!=expected:raise AdmissionError('log argument must bind gamma')
        if type(certificate) is not dict or set(certificate)!={'mass','delta','leading_lower','leading_upper'}:raise AdmissionError('exact full-mode certificate required')
        supplied={k:_rational(v,k,m) for k,v in certificate.items()};mass=Fraction(0);delta=Fraction(1)
        for d,w in normalized.items():mass=_add(mass,_divide(w,Fraction(d),m),m)
        for p in primes:delta=_mul(delta,Fraction(p-1,p),m)
        scale=_divide(_mul(mass,delta,m),Fraction(2),m)
        # -a1+a8+(a9-a8)L+(a7-a8)r0, all ai affine in SAME L.
        constant=C._sum(C._scale(a[1],Fraction(-1),m),a[8],m)
        logpart=C._sum(a[9],C._scale(a[8],Fraction(-1),m),m)
        rhopart=C._sum(a[7],C._scale(a[8],Fraction(-1),m),m)
        corners=[];endpoint_polys=[]
        for rho in (Fraction(0),rhoupper):
            c=C._sum(constant,C._scale(rhopart,rho,m),m)
            poly=C._scale((c[0],_add(c[1],logpart[0],m),logpart[1]),scale,m);endpoint_polys.append(poly);corners.append(C._range(poly,lo,hi,m))
        leadinglo=min(v[0] for v in corners);leadinghi=max(v[1] for v in corners)
        if supplied!={'mass':mass,'delta':delta,'leading_lower':leadinglo,'leading_upper':leadinghi}:raise AdmissionError('full-mode enclosure/mass/delta mismatch')
        out.update(mass=str(mass),delta=str(delta),rho_three_upper=str(rhoupper),rho_endpoint_polynomials=[[str(v) for v in poly] for poly in endpoint_polys],leading_lower=str(leadinglo),leading_upper=str(leadinghi))
        basepoly=(constant[0],_add(constant[1],logpart[0],m),logpart[1])
        rholower,rhohigher=C._range(rhopart,lo,hi,m)
        positive_rho_only=bool(mass) and not any(basepoly) and not rholower<=0<=rhohigher
        if leadinglo<=0<=leadinghi and not positive_rho_only:out.update(status='UNPAID',reason='full leading coefficient enclosure contains zero')
        elif positive_rho_only:
            out.update(status='VERIFIED_FULL_MODE_OBSTRUCTION',uniform_covariance_leaf_obstructed=True,strict_positive_rho_reason=True,numerical_nonzero_lower_bound_supplied=False,rho_multiplier_lower=str(rholower),rho_multiplier_upper=str(rhohigher),q_scope='every1<=q<2 and every fixed finite kappa',conclusion='Nonzero fixed leading coefficient from rho(s)>0, although closed enclosure touches0; total signed residual unrefuted',source_kernel_binding_still_required=True,coefficient_norm_admission_still_required=True,imported_theorems=[{'name':'Classical Prime Number Theorem','url':K.PNT_REFERENCE},{'name':'Quantitative Mertens decay','url':MERTENS_REFERENCE}],formal_theorem_prover_checked=False)
        else:
            minimum=min(abs(leadinglo),abs(leadinghi));square=_divide(_mul(minimum,minimum,m),Fraction(4),m)
            out.update(status='VERIFIED_FULL_MODE_OBSTRUCTION',uniform_covariance_leaf_obstructed=True,eventual_square_lower_coefficient=str(square),q_scope='every1<=q<2 and every fixed finite kappa',conclusion='Full fixed-log covariance leaf impossible on all integers; signed residual unrefuted',source_kernel_binding_still_required=True,coefficient_norm_admission_still_required=True,imported_theorems=[{'name':'Classical Prime Number Theorem','url':K.PNT_REFERENCE},{'name':'Quantitative Mertens decay','url':MERTENS_REFERENCE}],reviewed_analytic_derivation='A(x,x^(1/U))~-rho(U-1)*x/logx; fixedP coprime total=o(x/logx); signature[-1,r0,1-L-r0,L] on[1,7,8,9], r0=rho(3/gamma-1)',formal_theorem_prover_checked=False)
    except (ValueError,TypeError,KeyError,OverflowError) as e:return _finish(out,m,e)
    return _finish(out,m)

def verify_second_mode(kernel,P,gamma,ray,logspec,certificate,meter=None):
    """Pure1/9 exact first-mode annihilation leaves a second-log obstruction."""
    m=meter or Meter();out={'uniform_covariance_leaf_obstructed':False}
    try:
        r,_,_=C._log(logspec,m);g=_rational(gamma,'gamma',m);a=C._ray(ray,m);normalized=K._kernel(kernel,m);primes=C.F.F._primes(P,m)
        if type(P) is not list or list(primes)!=sorted(primes):raise AdmissionError('sorted primes required')
        if not Fraction(1,2)<g<Fraction(3,4):
            out.update(status='UNSUPPORTED',reason='second-mode gamma domain unpaid');return _finish(out,m)
        if any(any(v) for i,v in enumerate(a) if i not in (1,9)):
            out.update(status='UNSUPPORTED',reason='second-mode requires pure1/9 support');return _finish(out,m)
        expected=_divide(_add(Fraction(3),-_mul(Fraction(2),g,m),m),_mul(Fraction(2),g,m),m)
        if r!=expected:raise AdmissionError('log argument not bound gamma')
        c=a[9][0]
        if not c or a[9][1] or a[1]!=(Fraction(0),c):raise AdmissionError('exact first-mode identity a1=cL,a9=c required')
        keys={'mass','delta','moment_lower','moment_upper','leading_lower','leading_upper'}
        if type(certificate) is not dict or set(certificate)!=keys:raise AdmissionError('exact second-mode certificate required')
        supplied={k:_rational(v,k,m) for k,v in certificate.items()};mass=Fraction(0);delta=Fraction(1);tlo=thi=alo=ahi=Fraction(0)
        for d,w in normalized.items():
            argument=Fraction(d,4)
            if not Fraction(1,16)<=argument<=16:raise AdmissionError('kernel logarithm argument outside[1/16,16]')
            l,h=_log_bounds(argument,m);factor=_divide(w,Fraction(d),m);mass=_add(mass,factor,m);l=_add(Fraction(1),l,m);h=_add(Fraction(1),h,m)
            if factor<0:l,h=h,l
            tlo=_add(tlo,_mul(factor,l,m),m);thi=_add(thi,_mul(factor,h,m),m)
        for p in primes:
            if p>16:raise AdmissionError('prime logarithm argument outside[1/16,16]')
            l,h=_log_bounds(Fraction(p),m);alo=_add(alo,_divide(l,Fraction(p-1),m),m);ahi=_add(ahi,_divide(h,Fraction(p-1),m),m);delta=_mul(delta,Fraction(p-1,p),m)
        # Tfold=delta*(Tfixed-mass*A), preserving signed multiplication.
        correctionlo,correctionhi=(_mul(mass,alo,m),_mul(mass,ahi,m)) if mass>=0 else (_mul(mass,ahi,m),_mul(mass,alo,m))
        momentlo=_mul(delta,_add(tlo,-correctionhi,m),m);momenthi=_mul(delta,_add(thi,-correctionlo,m),m)
        scale=_divide(-c,_mul(Fraction(2),_add(Fraction(1),-_divide(_mul(Fraction(2),g,m),Fraction(3),m),m),m),m)
        leadinglo,leadinghi=(_mul(scale,momentlo,m),_mul(scale,momenthi,m)) if scale>=0 else (_mul(scale,momenthi,m),_mul(scale,momentlo,m))
        if supplied!={'mass':mass,'delta':delta,'moment_lower':momentlo,'moment_upper':momenthi,'leading_lower':leadinglo,'leading_upper':leadinghi}:raise AdmissionError('second-mode moment/leading enclosure mismatch')
        out.update(mass=str(mass),delta=str(delta),moment_lower=str(momentlo),moment_upper=str(momenthi),leading_lower=str(leadinglo),leading_upper=str(leadinghi))
        if leadinglo<=0<=leadinghi:out.update(status='UNPAID',reason='second-log coefficient interval contains0')
        else:out.update(status='VERIFIED_SECOND_MODE_OBSTRUCTION',uniform_covariance_leaf_obstructed=True,q_scope='every1<=q<2 and every fixed finite kappa',asymptotic='a.D~leading*u/(logu)^2',source_kernel_binding_still_required=True,coefficient_norm_admission_still_required=True,quantitative_prime_number_theorem_required=True,imported_theorem={'name':'Quantitative prime counting error (Trudgian, Theorem2)','url':'https://arxiv.org/html/1401.2689v2'},formal_theorem_prover_checked=False,conclusion='Exact first-mode annihilation leaves nonzero second-log mode; signed residual unrefuted')
    except (ValueError,TypeError,KeyError,OverflowError) as e:return _finish(out,m,e)
    return _finish(out,m)

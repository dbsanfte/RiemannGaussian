"""Independent fixed-kernel all-scale proper covariance-leaf obstruction079.

Imports classical PNT explicitly; no producer, mu query or scientific outcome.
Finite rational log enclosures prove only a nonzero asymptotic mode, never a
finite failure threshold or a signed residual lower bound.
"""
from fractions import Fraction
import check_mobius_residual_fold_077 as F
import check_mobius_prime_mass_gate_078 as K
from check_mobius_prime_storage_073 import AdmissionError,ResourceLimit,_rational,_add,_mul,_divide
LOG_TERMS=32
class Meter(F.Meter):pass

def _log_bounds(alpha,m):
    """Exact atanh enclosure of log((1-alpha)/alpha), no floating logs."""
    z=_add(Fraction(1),-_mul(Fraction(2),alpha,m),m)
    if not 0<z<Fraction(1,3):raise AdmissionError('log ratio outside proved semiprime domain')
    z2=_mul(z,z,m);term=z;lower=Fraction(0)
    for j in range(LOG_TERMS):
        lower=_add(lower,_divide(_mul(Fraction(2),term,m),Fraction(2*j+1),m),m);term=_mul(term,z2,m)
    tail=_divide(_mul(Fraction(2),term,m),_mul(Fraction(2*LOG_TERMS+1),_add(Fraction(1),-z2,m),m),m)
    return lower,_add(lower,tail,m)

def _scale_interval(scale,lo,hi,m):
    return (_mul(scale,lo,m),_mul(scale,hi,m)) if scale>=0 else (_mul(scale,hi,m),_mul(scale,lo,m))
def _finish(out,m,error=None):
    if error is not None:
        out.update(status='INVALID',reason=str(error))
        if isinstance(error,ResourceLimit):out['resource_limit']=True
    out.update(ops=m.ops,peak_bytes=m.peak_bytes,uniform_source_bound_proved=False,uniform_bound_proved=False,RH_proved=False,arithmetic_residual_refuted=False,residual_lower_bound_proved=False,finite_u_threshold_supplied=False)
    return out

def verify_flux_mass_gate(kernel,P,gamma,q,ray,certificate,meter=None):
    """Verify an eventual obstruction to S²<=kappa*u^(q-1)*Q_a for fixed kappa.

    Kernel is the UNFOLDED fixed rational prefix kernel; excluded-prime folds
    multiply its first moment by delta. Source/norm/row binding is separate.
    """
    m=meter or Meter();out={'status':'INVALID','uniform_covariance_leaf_obstructed':False}
    try:
        normalized=K._kernel(kernel,m);primes=F._primes(P,m)
        if type(P) is not list or list(primes)!=sorted(primes):raise AdmissionError('sorted distinct excluded primes required')
        g=_rational(gamma,'gamma',m);exponent=_rational(q,'q',m)
        if not 1<=exponent<2:raise AdmissionError('q outside [1,2)')
        if type(ray) is not list or len(ray)!=10:raise AdmissionError('ten rational ray coefficients required')
        a=[_rational(x,'ray coefficient',m) for x in ray]
        keys={'mass','delta','leading_lower','leading_upper','sigma','log_terms'}
        if type(certificate) is not dict or set(certificate)!=keys:raise AdmissionError('invalid exact flux-mass certificate schema')
        supplied={key:_rational(certificate[key],key,m) for key in keys-{'log_terms'}}
        if type(certificate['log_terms']) is not int:raise AdmissionError('log_terms must be integer')
        if any(value for i,value in enumerate(a) if i not in (1,9)) or not (a[1] or a[9]):
            out.update(status='UNSUPPORTED',reason='ray outside prime/last-bin obstruction grammar')
            return _finish(out,m)
        mode='pure_prime' if not a[9] else 'prime_last_bin'
        if mode=='pure_prime':
            if not 0<g<1:
                out.update(status='UNSUPPORTED',reason='pure-prime gamma domain0<gamma<1 unpaid')
                return _finish(out,m)
            if certificate['log_terms']!=0:raise AdmissionError('pure-prime log_terms must be0')
            loglo=loghi=Fraction(0)
        else:
            if not Fraction(1,2)<g<Fraction(3,4):
                out.update(status='UNSUPPORTED',reason='distinct-semiprime last-bin domain1/2<gamma<3/4 unpaid')
                return _finish(out,m)
            if certificate['log_terms']!=LOG_TERMS:raise AdmissionError('coupled log_terms must be32')
            alpha=_divide(_mul(Fraction(2),g,m),Fraction(3),m);loglo,loghi=_log_bounds(alpha,m)
        mass=Fraction(0)
        for d,weight in normalized.items():mass=_add(mass,_divide(weight,Fraction(d),m),m)
        delta=Fraction(1)
        for p in primes:delta=_mul(delta,Fraction(p-1,p),m)
        sigma=_add(Fraction(2),-exponent,m)
        if supplied['mass']!=mass or supplied['delta']!=delta or supplied['sigma']!=sigma:raise AdmissionError('mass/delta/sigma certificate mismatch')
        folded_mass=_mul(mass,delta,m)
        lo,hi=_scale_interval(a[9],loglo,loghi,m);lo=_add(lo,-a[1],m);hi=_add(hi,-a[1],m)
        leadinglo,leadinghi=_scale_interval(_divide(folded_mass,Fraction(2),m),lo,hi,m)
        if supplied['leading_lower']!=leadinglo or supplied['leading_upper']!=leadinghi:raise AdmissionError('signed leading coefficient enclosure mismatch')
        if not mass:
            out.update(status='UNPAID',reason='zero fixed-kernel first moment; no nonzero leading mode admitted')
            return _finish(out,m)
        if leadinglo<=0<=leadinghi:
            out.update(status='UNPAID',reason='leading coefficient interval does not exclude zero',leading_lower=str(leadinglo),leading_upper=str(leadinghi))
            return _finish(out,m)
        minimum=min(abs(leadinglo),abs(leadinghi));square_constant=_divide(_mul(minimum,minimum,m),Fraction(4),m)
        out.update(status='VERIFIED_FLUX_MASS_OBSTRUCTION',uniform_covariance_leaf_obstructed=True,mode=mode,mass=str(mass),delta=str(delta),folded_mass=str(folded_mass),leading_lower=str(leadinglo),leading_upper=str(leadinghi),sigma=str(sigma),log_terms=certificate['log_terms'],log_lower=str(loglo),log_upper=str(loghi),eventual_square_lower_coefficient=str(square_constant),normalized_kernel=K._saved(normalized),imported_theorem={'name':'Classical Prime Number Theorem','statement':'pi(x)~x/log(x)','url':K.PNT_REFERENCE},kernel_is_before_excluded_prime_folds=True,source_kernel_binding_still_required=True,coefficient_norm_admission_still_required=True,scope='fixed prime/last-bin proper covariance leaf impossible for every finite constant kappa and q<2; signed residual unrefuted',eventual_statement='|a.D|^2 >= eventual_square_lower_coefficient*u^2/(log u)^2 for all sufficiently large integer u; Q_a=O(u)',contradicted_leaf='(a.D)^2<=kappa*u^(q-1)*Q_a with fixed finite kappa')
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _finish(out,m,error)
    return _finish(out,m)

verify_gate=verify_flux_mass_gate

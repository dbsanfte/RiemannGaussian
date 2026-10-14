"""Independent exact shared-log affine cover and finite covariance admission080.
No producer imports. Uniform arithmetic leaves and source admissions stay unpaid.
"""
from fractions import Fraction
import math
import check_mobius_scale_flux_079 as F
import check_mobius_prime_mass_gate_078 as M
from check_mobius_prime_storage_073 import AdmissionError,ResourceLimit,_rational,_add,_mul,_divide,power_enclosure
class Meter(F.Meter):pass

def _done(out,m,error=None):
    if error is not None:
        out.update(status='INVALID',reason=str(error))
        if isinstance(error,ResourceLimit):out['resource_limit']=True
    out.update(ops=m.ops,peak_bytes=m.peak_bytes,uniform_correlation_proved=False,uniform_source_bound_proved=False,uniform_bound_proved=False,RH_proved=False,source_admission_still_required=True,arithmetic_residual_refuted=False,residual_lower_bound_proved=False,finite_u_threshold_supplied=False)
    return out

def _log(raw,m):
    if type(raw) is not dict or set(raw)!={'argument','terms','lower','upper'} or type(raw['terms']) is not int or raw['terms']!=32:raise AdmissionError('exact32-term log certificate required')
    r=_rational(raw['argument'],'log argument',m)
    if not Fraction(1,16)<=r<=16:raise AdmissionError('log argument outside [1/16,16]')
    z=_divide(_add(r,Fraction(-1),m),_add(r,Fraction(1),m),m);t=abs(z);t2=_mul(t,t,m);term=t;lo=Fraction(0)
    for k in range(32):
        lo=_add(lo,_divide(_mul(Fraction(2),term,m),Fraction(2*k+1),m),m);term=_mul(term,t2,m)
    hi=_add(lo,_divide(_mul(Fraction(2),term,m),_mul(Fraction(65),_add(Fraction(1),-t2,m),m),m),m)
    if z<0:lo,hi=-hi,-lo
    if _rational(raw['lower'],'log lower',m)!=lo or _rational(raw['upper'],'log upper',m)!=hi:raise AdmissionError('exact log enclosure mismatch')
    return r,lo,hi

def verify_log(logspec,meter=None):
    m=meter or Meter();out={}
    try:
        r,lo,hi=_log(logspec,m);out.update(status='VERIFIED_LOG_ENCLOSURE',argument=str(r),lower=str(lo),upper=str(hi),terms=32)
    except (ValueError,TypeError,KeyError,OverflowError) as e:return _done(out,m,e)
    return _done(out,m)

def _ray(raw,m,proper=True):
    if type(raw) is not list or len(raw)!=10:raise AdmissionError('ten affine coefficients required')
    a=[]
    for pair in raw:
        if type(pair) is not list or len(pair)!=2:raise AdmissionError('affine coefficient [constant,L coefficient] required')
        a.append(tuple(_rational(v,'affine coefficient',m) for v in pair))
    if proper and (not any(any(v) for v in a) or all(v==a[0] for v in a)):raise AdmissionError('zero or affine total-flux ray prohibited')
    return a

def _sum(a,b,m):return tuple(_add(x,y,m) for x,y in zip(a,b))
def _scale(a,c,m):return tuple(_mul(x,c,m) for x in a)
def _product(a,b,m):
    return (_mul(a[0],b[0],m),_add(_mul(a[0],b[1],m),_mul(a[1],b[0],m),m),_mul(a[1],b[1],m))
def _evaluate(p,x,m):
    value=Fraction(0)
    for c in reversed(p):value=_add(_mul(value,x,m),c,m)
    return value

def _range(p,lo,hi,m):
    values=[_evaluate(p,lo,m),_evaluate(p,hi,m)]
    if len(p)>2 and p[2]:
        vertex=_divide(-p[1],_mul(Fraction(2),p[2],m),m)
        if lo<=vertex<=hi:values.append(_evaluate(p,vertex,m))
    return min(values),max(values)

def _unit(poly,m):
    parsed=F.F._poly(poly,m)
    if any(t!='1' for t in parsed):raise AdmissionError('fixed-kernel pilot permits only literal1 tokens')
    return parsed.get('1',Fraction(0))

def _row(raw,m):
    u,D,B,ranges=F._row(raw,m)
    if ranges!={'1':(Fraction(1),Fraction(1))}:raise AdmissionError('exact unit token interval required')
    values=[]
    for poly in D:
        if any(t!='1' for t in poly):raise AdmissionError('only literal1 feature tokens permitted')
        values.append(poly.get('1',Fraction(0)))
    gram={}
    for pair,poly in B.items():
        if any(tokens!=('1','1') for tokens in poly):raise AdmissionError('only literal1 Gram tokens permitted')
        gram[pair]=poly.get(('1','1'),Fraction(0))
    return u,values,gram

def verify_leaf(row,ray,kappa,q,logspec,meter=None,precision=24):
    m=meter or Meter();out={}
    try:
        _,lo,hi=_log(logspec,m);a=_ray(ray,m);u,D,B=_row(row,m)
        k=_rational(kappa,'kappa',m);qv=_rational(q,'q',m)
        if k<0 or not 1<=qv<2:raise AdmissionError('kappa/q domain')
        precision=F.F._integer(precision,'precision',8,24)
        S=(Fraction(0),Fraction(0));Q=(Fraction(0),)*3
        for av,d in zip(a,D):S=_sum(S,_scale(av,d,m),m)
        for (i,j),value in B.items():Q=_sum(Q,_scale(_product(a[i],a[j],m),value*(1 if i==j else 2),m),m)
        SS=_product(S,S,m);slo,shi=_range(SS,lo,hi,m);qlo,qhi=_range(Q,lo,hi,m)
        if qlo<0:raise AdmissionError('Gram ray polynomial not certified nonnegative')
        plo,phi=(Fraction(1),Fraction(1)) if qv==1 else power_enclosure(u,qv-1,precision,m)
        # Compute the difference polynomial first, retaining the SAME log throughout.
        lower_poly=_sum(SS,_scale(Q,-_mul(k,phi,m),m),m)
        upper_poly=_sum(SS,_scale(Q,-_mul(k,plo,m),m),m)
        lower=_range(lower_poly,lo,hi,m)[0];upper=_range(upper_poly,lo,hi,m)[1]
        status='CERTIFIED_FINITE' if upper<=0 else ('REFUTED_FINITE' if lower>0 else 'UNRESOLVED_INTERVAL')
        out.update(status=status,u=u,S_polynomial=[str(v) for v in S],Q_polynomial=[str(v) for v in Q],S_squared_lower=str(slo),S_squared_upper=str(shi),Q_lower=str(qlo),Q_upper=str(qhi),difference_lower=str(lower),difference_upper=str(upper),cell_admission_still_required=True,noncircularity_still_required=True)
    except (ValueError,TypeError,KeyError,OverflowError) as e:return _done(out,m,e)
    return _done(out,m)

def verify_noncircularity(payload,ray,logspec,witnessfirst_cell,witnesssecond_cell,meter=None):
    m=meter or Meter();out={}
    try:
        _,lo,hi=_log(logspec,m);a=_ray(ray,m)
        if type(payload) is not dict or type(payload.get('bands')) is not list or type(payload.get('cells')) is not list:raise AdmissionError('cell payload required')
        cells=payload['cells'];bands=payload['bands']
        indices=[F.F._integer(v,'witness cell',0,len(cells)-1) for v in (witnessfirst_cell,witnesssecond_cell)]
        if indices[0]==indices[1]:raise AdmissionError('distinct positive cells required')
        forms=[]
        for ix in indices:
            cell=cells[ix]
            if type(cell) is not dict or type(cell.get('count')) is not int or cell['count']<=0:raise AdmissionError('positive actual cell count required')
            bi=F.F._integer(cell.get('band'),'band',0,len(bands)-1);pc=F.F._integer(cell.get('parent_category'),'parent category',0,10);hc=F.F._integer(cell.get('child_category'),'child category',0,10)
            band=bands[bi];pw=_unit(band['parent_weight'],m);cw=_unit(band['child_weight'],m)
            proper=(Fraction(0),Fraction(0));total=Fraction(0)
            if pc<10:proper=_sum(proper,_scale(a[pc],pw,m),m);total+=pw
            if hc<10:proper=_sum(proper,_scale(a[hc],-cw,m),m);total-=cw
            forms.append((proper,total))
        det=_sum(_scale(forms[0][0],forms[1][1],m),_scale(forms[1][0],-forms[0][1],m),m);dl,du=_range(det,lo,hi,m)
        proved=not dl<=0<=du
        out.update(status='VERIFIED_NONCIRCULARITY' if proved else 'UNRESOLVED_INTERVAL',determinant_polynomial=[str(v) for v in det],determinant_lower=str(dl),determinant_upper=str(du),noncircularity_proved=proved,cell_admission_still_required=True)
    except (ValueError,TypeError,KeyError,OverflowError) as e:return _done(out,m,e)
    return _done(out,m)

def _sqrt_upper(value,m):
    m.charge(value.numerator.bit_length()+value.denominator.bit_length());scaled=value*2**48
    root=math.isqrt(scaled.numerator//scaled.denominator)
    return Fraction(root if root*root==scaled else root+1,2**24)

def verify_cover(target,rays,kappas,K,logspec,certificate,meter=None):
    m=meter or Meter();out={}
    try:
        _,lo,hi=_log(logspec,m)
        if type(target) is not list or len(target)!=10 or any(type(v) is not int or v not in (0,1) for v in target) or not any(target):raise AdmissionError('nonzero binary target required')
        if type(rays) is not list or len(rays)!=2 or type(kappas) is not list or len(kappas)!=2:raise AdmissionError('two complement rays/kappas required')
        aa=[_ray(a,m) for a in rays];ks=[_rational(v,'kappa',m) for v in kappas];Kv=_rational(K,'K',m)
        if min(ks+[Kv])<0:raise AdmissionError('nonnegative kappa/K required')
        if any(_sum(aa[0][i],aa[1][i],m)!=(Fraction(target[i]),Fraction(0)) for i in range(10)):raise AdmissionError('affine complement identity mismatch')
        weights=[];maxima=[]
        for a,k in zip(aa,ks):
            maximum=max(max(abs(_evaluate(v,lo,m)),abs(_evaluate(v,hi,m))) for v in a);maxima.append(maximum)
            weights.append(_sqrt_upper(_mul(Fraction(3),_mul(Kv,_mul(k,_mul(maximum,maximum,m),m),m),m),m))
        price=_mul(_add(weights[0],weights[1],m),_add(weights[0],weights[1],m),m)
        if type(certificate) is not dict or set(certificate)!={'price'} or _rational(certificate['price'],'price',m)!=price:raise AdmissionError('conditional price mismatch')
        out.update(status='VERIFIED_CONDITIONAL_COVER',price=str(price),weights=[str(v) for v in weights],maxima=[str(v) for v in maxima],exact_affine_cover_verified=True,uniform_leaves_still_required=True,coefficient_norm_admission_still_required=True,inactive_coordinate_admission_still_required=True,noncircularity_still_required=True)
    except (ValueError,TypeError,KeyError,OverflowError) as e:return _done(out,m,e)
    return _done(out,m)

def verify_mode_annihilator(gamma,ray,logspec,meter=None):
    m=meter or Meter();out={}
    try:
        r,_,_=_log(logspec,m);g=_rational(gamma,'gamma',m);a=_ray(ray,m)
        if not Fraction(1,2)<g<Fraction(3,4):raise AdmissionError('semiprime mode gamma domain')
        expected=_divide(_add(Fraction(3),-_mul(Fraction(2),g,m),m),_mul(Fraction(2),g,m),m)
        if r!=expected:raise AdmissionError('log argument not bound to gamma')
        # Only the 1,9 subexpression is checked: other coordinates remain unpaid.
        poly=(-a[1][0],_add(-a[1][1],a[9][0],m),a[9][1])
        if any(poly):
            out.update(status='UNPAID',leading_mode_annihilated=False,mode_polynomial=[str(v) for v in poly])
        else:out.update(status='VERIFIED_LEADING_MODE_ANNIHILATION',leading_mode_annihilated=True,whole_ray_mode_annihilated=not any(any(v) for i,v in enumerate(a) if i not in (1,9)),conclusion='prime/last-bin subexpression is o(u/log u); lower logarithmic remainders and other channels unpaid',imported_theorem={'name':'Classical Prime Number Theorem','url':M.PNT_REFERENCE},fixed_kernel_binding_still_required=True)
    except (ValueError,TypeError,KeyError,OverflowError) as e:return _done(out,m,e)
    return _done(out,m)

def verify_source_pair(unfoldedfixedkernel,P,u,parentintervals,childintervals,payload,meter=None):
    """Fresh tiny/domain-gated arithmetic recombination; cell roster admission external."""
    m=meter or Meter();out={}
    try:
        kernel=M._kernel(unfoldedfixedkernel,m);primes=F.F._primes(P,m)
        if type(P) is not list or list(primes)!=sorted(primes):raise AdmissionError('sorted P required')
        u=F.F._integer(u,'u',2,F.F.MAX_PARENT);h=u//2
        if type(payload) is not dict or payload.get('u')!=u or payload.get('child_u')!=h or type(payload.get('bands')) is not list or type(payload.get('cells')) is not list:raise AdmissionError('source cell payload scale mismatch')
        divisors=[(1,1)]
        for p in primes:divisors += [(d*p,-s) for d,s in divisors]
        if len(kernel)*len(divisors)>100000:raise ResourceLimit('folded source term gate')
        m.reserve(F._resident()+8192*(1+len(kernel)*len(divisors)));folded={}
        for d,w in kernel.items():
            for mult,sign in divisors:
                key=d*mult;folded[key]=_add(folded.get(key,Fraction(0)),w*sign,m)
        saved=M._saved(folded)
        for v,intervals in ((u,parentintervals),(h,childintervals)):
            result=F.verify_kernel_row(saved,v,intervals,m)
            if result['status']!='VERIFIED_KERNEL_ROW':raise AdmissionError('source coefficient row mismatch')
        horizon=max((u//d for d in kernel),default=0)
        source=F.A.ensure_horizon(horizon,m);m.reserve(F._resident()+16*(horizon+1)+4096);m.charge(horizon+1)
        prefix=source['mu'].astype('int64').cumsum()
        expected=[sum((w*int(prefix[v//d]) for d,w in kernel.items()),Fraction(0)) for v in (u,h)]
        sums=[Fraction(0),Fraction(0)]
        if len(payload['cells'])>100000:raise ResourceLimit('cell gate')
        for cell in payload['cells']:
            if type(cell) is not dict:raise AdmissionError('invalid source cell')
            bi=F.F._integer(cell.get('band'),'band',0,len(payload['bands'])-1);count=F.F._integer(cell.get('count'),'count',1,4000000);signed=F.F._integer(cell.get('signed_count'),'signed count',-count,count)
            band=payload['bands'][bi]
            for i,key in enumerate(('parent_weight','child_weight')):sums[i]=_add(sums[i],_mul(_unit(band[key],m),Fraction(signed),m),m)
        if sums!=expected:raise AdmissionError('parent/half arithmetic source recombination mismatch')
        out.update(status='VERIFIED_SOURCE_PAIR',u=u,child_u=h,parent_residual=str(expected[0]),child_residual=str(expected[1]),cell_admission_still_required=True,fixed_source_program_binding_still_required=True)
    except (ValueError,TypeError,KeyError,OverflowError) as e:return _done(out,m,e)
    return _done(out,m)

def verify_mode_obstruction(kernel,P,gamma,ray,logspec,certificate,meter=None):
    """Symbolic fixed-kernel covariance obstruction for every1<=q<2.

    Log-defined ray coefficients are fixed real constants, not moving tokens.
    """
    m=meter or Meter();out={'uniform_covariance_leaf_obstructed':False}
    try:
        r,lo,hi=_log(logspec,m);g=_rational(gamma,'gamma',m);a=_ray(ray,m)
        normalized=M._kernel(kernel,m);primes=F.F._primes(P,m)
        if type(P) is not list or list(primes)!=sorted(primes):raise AdmissionError('sorted P required')
        if type(certificate) is not dict or set(certificate)!={'leading_lower','leading_upper','mass','delta'}:raise AdmissionError('exact symbolic mode certificate required')
        supplied={key:_rational(v,key,m) for key,v in certificate.items()}
        if any(any(v) for i,v in enumerate(a) if i not in (1,9)):
            out.update(status='UNSUPPORTED',reason='other channels lack fixed-kernel leading theorem')
            return _done(out,m)
        coupled=any(a[9])
        if coupled:
            if not Fraction(1,2)<g<Fraction(3,4):
                out.update(status='UNSUPPORTED',reason='semiprime domain unpaid');return _done(out,m)
            expected=_divide(_add(Fraction(3),-_mul(Fraction(2),g,m),m),_mul(Fraction(2),g,m),m)
            if r!=expected:raise AdmissionError('log argument not bound to gamma')
        elif not 0<g<1:
            out.update(status='UNSUPPORTED',reason='pure-prime gamma domain unpaid');return _done(out,m)
        mass=Fraction(0);delta=Fraction(1)
        for d,w in normalized.items():mass=_add(mass,_divide(w,Fraction(d),m),m)
        for p in primes:delta=_mul(delta,Fraction(p-1,p),m)
        scale=_divide(_mul(mass,delta,m),Fraction(2),m)
        polynomial=_scale((-a[1][0],_add(-a[1][1],a[9][0],m),a[9][1]),scale,m)
        leadinglo,leadinghi=_range(polynomial,lo,hi,m)
        if supplied!={'mass':mass,'delta':delta,'leading_lower':leadinglo,'leading_upper':leadinghi}:raise AdmissionError('symbolic leading certificate mismatch')
        if leadinglo<=0<=leadinghi:
            out.update(status='UNPAID',leading_lower=str(leadinglo),leading_upper=str(leadinghi),leading_polynomial=[str(v) for v in polynomial],reason='leading interval does not exclude zero')
        else:
            minimum=min(abs(leadinglo),abs(leadinghi));square=_divide(_mul(minimum,minimum,m),Fraction(4),m)
            out.update(status='VERIFIED_SYMBOLIC_MODE_OBSTRUCTION',uniform_covariance_leaf_obstructed=True,mass=str(mass),delta=str(delta),leading_lower=str(leadinglo),leading_upper=str(leadinghi),leading_polynomial=[str(v) for v in polynomial],eventual_square_lower_coefficient=str(square),q_scope='every1<=q<2 and every finite fixed kappa',source_kernel_binding_still_required=True,coefficient_norm_admission_still_required=True,finite_u_threshold_supplied=False,arithmetic_residual_refuted=False,residual_lower_bound_proved=False,imported_theorem={'name':'Classical Prime Number Theorem','url':M.PNT_REFERENCE},conclusion='This fixed-log prime/last-bin covariance leaf cannot hold on all integers; total signed residual unrefuted')
    except (ValueError,TypeError,KeyError,OverflowError) as e:return _done(out,m,e)
    return _done(out,m)

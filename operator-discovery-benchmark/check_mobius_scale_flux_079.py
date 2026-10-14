"""Independent079 shared-index arithmetic cells, flux Gram and leaf admission.
No producer import. Frozen independent077 rational/interval and078 factor cache
are reused; cell queries use sorted joint-category positions and signed prefixes.
"""
from fractions import Fraction
import numpy as np
import check_mobius_residual_fold_077 as F
import check_mobius_rough_energy_078 as A
from check_mobius_prime_storage_073 import (AdmissionError,ResourceLimit,_rational,_add,_mul,_divide,power_enclosure)
MEMORY_BUDGET=4*1024**3
MAX_TERMS=100000
class Meter(F.Meter):pass
_JOINT_CACHE={}
_JOINT_BYTES=0

def _saved(poly):return {t:str(v) for t,v in poly.items() if v}
def _resident():return A._resident()+_JOINT_BYTES

def _cutoffs(H,g,m):
    cuts=(A.ceil_power(H,g,m),A.ceil_power(H,g/3,m),A.ceil_power(H,2*g/3,m))
    from check_mobius_prime_storage_073 import _power_compare
    if H and _power_compare(cuts[0],7,H,m)<0:raise AdmissionError('terminal degree gate unpaid')
    return cuts

def _category(H,cuts,n,source):
    y,s1,s2=cuts
    result=np.full(len(n),10,dtype=np.int8)
    if not H:return result
    inside=(n>=1)&(n<=H);least=source['least'];omega=source['omega']
    rough=inside&(least>min(y,H));result[rough]=omega[rough]
    for index,(lo,hi) in enumerate(((0,s1),(s1,s2),(s2,y)),7):
        mask=inside&(least>min(lo,H))&(least<=min(hi,H));result[mask]=index
    result[1]=0
    return result

def _joint_queries(Hp,Hc,g,P,m):
    global _JOINT_BYTES
    pc=_cutoffs(Hp,g,m);hc=_cutoffs(Hc,g,m);key=(Hp,Hc,pc,hc,tuple(P));m.charge()
    if key in _JOINT_CACHE:return _JOINT_CACHE[key]
    H=max(Hp,Hc)
    m.reserve(_resident()+160*(H+1)+4096)
    source=A.ensure_horizon(H,m);n=np.arange(H+1,dtype=np.int32);allowed=source['mu']!=0;allowed[0]=False
    for p in P:m.charge(H+1);allowed &= n%p!=0
    parent=_category(Hp,pc,n,source);child=_category(Hc,hc,n,source)
    positions=np.flatnonzero(allowed).astype(np.int32);joint=(11*parent[positions]+child[positions]).astype(np.int16)
    # Stable category sort retains ascending positions within each group.
    order=np.argsort(joint,kind='stable');positions=positions[order];joint=joint[order];m.charge(12*(H+1))
    queries={};size=4096
    for pcat in range(11):
        for ccat in range(11):
            code=11*pcat+ccat;lo=int(np.searchsorted(joint,code,'left'));hi=int(np.searchsorted(joint,code,'right'))
            if hi>lo:
                pos=positions[lo:hi].copy();prefix=np.empty(len(pos)+1,dtype=np.int32);prefix[0]=0
                np.cumsum(source['mu'][pos],dtype=np.int32,out=prefix[1:]);pos.flags.writeable=False;prefix.flags.writeable=False
                queries[(pcat,ccat)]=(pos,prefix);size+=pos.nbytes+prefix.nbytes+256
    if _JOINT_BYTES+size>256*1024**2:_JOINT_CACHE.clear();_JOINT_BYTES=0
    m.reserve(_resident()+160*(H+1)+size+4096);_JOINT_CACHE[key]=queries;_JOINT_BYTES+=size
    return queries

def _bands(parent,child,m):
    pe=F._function_events(parent,m);ce=F._function_events(child,m);points=sorted(set(pe)|set(ce));pw={};cw={};result=[];terms=0;live_cost=4096
    for i,left in enumerate(points[:-1]):
        F._join(pw,pe.get(left,{}),1,m);F._join(cw,ce.get(left,{}),1,m);right=points[i+1]
        if pw or cw:
            terms+=len(pw)+len(cw)
            if terms>MAX_TERMS or len(result)>=100000:raise ResourceLimit('prospective band expansion term gate')
            live_cost+=1024+sum(1024+8*len(t)+2*(a.numerator.bit_length()+a.denominator.bit_length()) for poly in (pw,cw) for t,a in poly.items())
            m.reserve(_resident()+32*live_cost)
            result.append({'left':left,'right':right,'parent_weight':_saved(pw),'child_weight':_saved(cw)})
    return result

def _cell_deltas(band,pc,hc,m):
    parent=F._poly(band['parent_weight'],m);child=F._poly(band['child_weight'],m);deltas=[{} for _ in range(10)]
    if pc<10:F._join(deltas[pc],parent,1,m)
    if hc<10:F._join(deltas[hc],child,-1,m)
    return deltas

def _quad_add(target,left,right,scale,m):
    if not scale:return
    for lt,la in left.items():
        for rt,ra in right.items():
            pair=tuple(sorted((lt,rt)));v=_mul(scale,_mul(la,ra,m),m);new=_add(target.get(pair,Fraction(0)),v,m)
            if new:target[pair]=new
            else:target.pop(pair,None)

def _saved_gram(gram):
    return [{'i':i,'j':j,'terms':[{'left_token':a,'right_token':b,'coefficient':str(v)} for (a,b),v in sorted(gram[(i,j)].items())]} for i in range(10) for j in range(i,10)]

def _parse_gram(raw,m):
    if type(raw) is not list or len(raw)!=55:raise AdmissionError('complete55-entry Gram required')
    pre_cost=4096;pre_terms=0
    for row in raw:
        if type(row) is not dict or type(row.get('terms')) is not list:raise AdmissionError('invalid Gram entries')
        pre_terms+=len(row['terms'])
        if pre_terms>MAX_TERMS:raise ResourceLimit('Gram term gate')
        for term in row['terms']:
            if type(term) is not dict:raise AdmissionError('invalid quadratic term')
            pre_cost+=2048+sum(4*len(value) for value in term.values() if type(value) is str)
    m.reserve(_resident()+16*pre_cost)
    expected=[(i,j) for i in range(10) for j in range(i,10)];result={};terms=0;cost=4096
    for pair,row in zip(expected,raw):
        if type(row) is not dict or set(row)!={'i','j','terms'} or type(row['i']) is not int or type(row['j']) is not int or (row['i'],row['j'])!=pair or type(row['terms']) is not list:raise AdmissionError('invalid Gram entry')
        terms+=len(row['terms'])
        if terms>MAX_TERMS:raise ResourceLimit('Gram term gate')
        poly={};previous=None
        for term in row['terms']:
            if type(term) is not dict or set(term)!={'left_token','right_token','coefficient'}:raise AdmissionError('invalid quadratic term')
            a,b=term['left_token'],term['right_token']
            if type(a) is not str or type(b) is not str or not a or not b or max(len(a),len(b))>256 or a>b:raise AdmissionError('invalid canonical token pair')
            key=(a,b)
            if previous is not None and key<=previous:raise AdmissionError('quadratic terms must be sorted unique')
            previous=key;v=_rational(term['coefficient'],'quadratic coefficient',m)
            if not v:raise AdmissionError('omit zero quadratic coefficients')
            poly[key]=v;cost+=2048+8*(len(a)+len(b))+4*len(term['coefficient'])
        result[pair]=poly
    m.reserve(_resident()+16*cost)
    return result

def _done(out,m,error=None):
    out=F._finish(out,m,error);out.update(uniform_correlation_proved=False,uniform_source_bound_proved=False,source_admission_still_required=True,token_root_binding_still_required=True)
    return out

def verify_cells(parent_intervals,child_intervals,P,gamma,payload,meter=None):
    m=meter or Meter();out={'status':'INVALID'}
    try:
        parent,pcost=F._intervals(parent_intervals,m);child,ccost=F._intervals(child_intervals,m);primes=F._primes(P,m)
        if type(P) is not list or list(primes)!=sorted(primes):raise AdmissionError('sorted excluded prime list required')
        g=_rational(gamma,'gamma',m)
        if g<0:raise AdmissionError('negative gamma')
        keys={'schema','u','child_u','bands','cells','flux_features','gram_upper'}
        if type(payload) is not dict or set(payload)!=keys or payload['schema']!='scale-flux-cells-v1':raise AdmissionError('invalid cell payload schema')
        u=F._integer(payload['u'],'u',2,F.MAX_PARENT)
        if type(payload['child_u']) is not int or payload['child_u']!=u//2:raise AdmissionError('child scale mismatch')
        m.reserve(_resident()+32*(pcost+ccost));bands=_bands(parent,child,m)
        if len(bands)>100000:raise ResourceLimit('band count gate')
        if type(payload['bands']) is not list or len(payload['bands'])!=len(bands):raise AdmissionError('invalid bands')
        m.reserve(_resident()+32*sum(F._raw_cost(band.get('parent_weight',{}))+F._raw_cost(band.get('child_weight',{})) for band in payload['bands'] if type(band) is dict and type(band.get('parent_weight')) is dict and type(band.get('child_weight')) is dict))
        for band in payload['bands']:
            if type(band) is not dict or set(band)!={'left','right','parent_weight','child_weight'} or type(band['left']) is not int or type(band['right']) is not int:raise AdmissionError('invalid band schema')
            F._poly(band['parent_weight'],m);F._poly(band['child_weight'],m)
        if payload['bands']!=bands:raise AdmissionError('complete coefficient band union mismatch')
        Hp=max((r for l,r,p in parent),default=0);Hc=max((r for l,r,p in child),default=0)
        queries=_joint_queries(Hp,Hc,g,primes,m);actual_cells=payload['cells']
        if type(actual_cells) is not list or len(actual_cells)>121*max(1,len(bands)):raise AdmissionError('invalid cell list')
        m.reserve(_resident()+64*(pcost+ccost)+1024*min(max(Hp,Hc),len(bands)*len(queries)))
        expected=[]
        for bi,band in enumerate(bands):
            for (pc,hc),(positions,prefix) in sorted(queries.items()):
                l=int(np.searchsorted(positions,band['left'],'right'));r=int(np.searchsorted(positions,band['right'],'right'));count=r-l;m.charge(2*max(1,len(positions).bit_length()))
                if count:expected.append({'band':bi,'parent_category':pc,'child_category':hc,'count':count,'signed_count':int(prefix[r])-int(prefix[l])})
        for cell in actual_cells:
            if type(cell) is not dict or set(cell)!={'band','parent_category','child_category','count','signed_count'} or any(type(value) is not int for value in cell.values()):raise AdmissionError('invalid cell schema/integer')
        if actual_cells!=expected:raise AdmissionError('complete arithmetic cell/count mismatch')
        D=[{} for _ in range(10)];gram={(i,j):{} for i in range(10) for j in range(i,10)}
        # Quadratic expansion reserve follows actual admitted token dimensions.
        work=sum((len(band['parent_weight'])+len(band['child_weight']))**2 for band in bands)
        if work*121>10**8:raise ResourceLimit('prospective quadratic expansion work gate')
        m.reserve(_resident()+64*(pcost+ccost)+4096*work+1024*len(expected))
        for cell in expected:
            deltas=_cell_deltas(bands[cell['band']],cell['parent_category'],cell['child_category'],m)
            for i,poly in enumerate(deltas):
                for token,a in poly.items():
                    new=_add(D[i].get(token,Fraction(0)),_mul(Fraction(cell['signed_count']),a,m),m)
                    if new:D[i][token]=new
                    else:D[i].pop(token,None)
                for j in range(i,10):_quad_add(gram[(i,j)],poly,deltas[j],Fraction(cell['count']),m)
        suppliedD=A._polys(payload['flux_features'],m);suppliedGram=_parse_gram(payload['gram_upper'],m)
        if suppliedD!=D:raise AdmissionError('signed flux feature mismatch')
        if suppliedGram!=gram:raise AdmissionError('diagonal shared-index Gram mismatch')
        out.update(status='VERIFIED_CELLS',u=u,child_u=u//2,bands_checked=len(bands),cells_checked=len(expected),flux_features=[_saved(poly) for poly in D],gram_upper=_saved_gram(gram),pointwise_flux_identity_verified=True)
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _done(out,m,error)
    return _done(out,m)

def _ray(raw,m):
    if type(raw) is not list or len(raw)!=10:raise AdmissionError('ten ray coefficients required')
    a=[_rational(x,'ray',m) for x in raw]
    if not 1<=sum(bool(x) for x in a)<=2:raise AdmissionError('proper ray requires support1or2')
    return a

def _ranges(raw,m):
    if type(raw) is not dict or len(raw)>MAX_TERMS:raise AdmissionError('invalid token ranges')
    ranges={}
    for token,pair in raw.items():
        if type(token) is not str or not token or len(token)>256 or type(pair) not in (tuple,list) or len(pair)!=2:raise AdmissionError('invalid token enclosure')
        lo,hi=(_rational(v,'token endpoint',m) for v in pair)
        if lo>hi:raise AdmissionError('inverted token enclosure')
        ranges[token]=(lo,hi)
    return ranges

def _quad_interval(poly,ranges,m):
    lo=hi=Fraction(0)
    for (a,b),c in poly.items():
        if a not in ranges or b not in ranges:raise AdmissionError('missing quadratic token enclosure')
        x,y=ranges[a];z,w=ranges[b]
        if a==b:left,right=A._square(x,y,m)
        else:
            values=[_mul(x,z,m),_mul(x,w,m),_mul(y,z,m),_mul(y,w,m)];left,right=min(values),max(values)
        if c<0:left,right=right,left
        lo=_add(lo,_mul(c,left,m),m);hi=_add(hi,_mul(c,right,m),m)
    return lo,hi

def _row(raw,m):
    if type(raw) is not dict or set(raw)!={'u','flux_features','gram_upper','token_intervals'}:raise AdmissionError('invalid local leaf row')
    u=F._integer(raw['u'],'u',2,F.MAX_PARENT);D=A._polys(raw['flux_features'],m);B=_parse_gram(raw['gram_upper'],m);ranges=_ranges(raw['token_intervals'],m)
    return u,D,B,ranges

def _ray_forms(D,B,a,m):
    S=A._linear(D,a,m);Q={}
    for (i,j),poly in B.items():
        scale=_mul(a[i],a[j],m)
        if i!=j:scale=_mul(Fraction(2),scale,m)
        if scale:
            for pair,value in poly.items():
                new=_add(Q.get(pair,Fraction(0)),_mul(scale,value,m),m)
                if new:Q[pair]=new
                else:Q.pop(pair,None)
    return S,Q

def verify_local_leaf(row,ray,kappa,q,meter=None,precision=24):
    """Finite proper-ray covariance S²<=kappa*u^(q-1)*Q; no total-flux leaf."""
    m=meter or Meter();out={'status':'INVALID'}
    try:
        F._integer(precision,'precision',8,24);u,D,B,ranges=_row(row,m);a=_ray(ray,m);k=_rational(kappa,'kappa',m);exponent=_rational(q,'q',m)
        if k<0 or not 1<=exponent<2:raise AdmissionError('invalid kappa/q domain')
        S,Q=_ray_forms(D,B,a,m);Slo,Shi=A._poly_interval(S,ranges,m);leftlo,lefthi=A._square(Slo,Shi,m);Qlo,Qhi=_quad_interval(Q,ranges,m)
        plo,phi=(Fraction(1),Fraction(1)) if exponent==1 else power_enclosure(u,exponent-1,precision,m)
        values=[_mul(x,y,m) for x in (plo,phi) for y in (Qlo,Qhi)];rightlo=_mul(k,min(values),m);righthi=_mul(k,max(values),m)
        lower=_add(leftlo,-righthi,m);upper=_add(lefthi,-rightlo,m)
        status='CERTIFIED_FINITE' if upper<=0 else 'REFUTED_FINITE' if lower>0 else 'UNRESOLVED_INTERVAL'
        out.update(status=status,u=u,lower=str(lower),upper=str(upper),S_lower=str(Slo),S_upper=str(Shi),Q_lower=str(Qlo),Q_upper=str(Qhi),left_lower=str(leftlo),left_upper=str(lefthi),right_lower=str(rightlo),right_upper=str(righthi),cell_admission_still_required=True,proper_ray_verified=True)
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _done(out,m,error)
    return _done(out,m)

def verify_noncircularity(payload,ray,token_intervals,witness,meter=None):
    """Two cell coefficient vectors distinguish a proper ray from total flux.

    witness exactly {'first_cell':index,'second_cell':index}; nonzero determinant
    must be proved by a rational interval excluding zero under token enclosures.
    """
    m=meter or Meter();out={'status':'INVALID'}
    try:
        if type(payload) is not dict or not {'bands','cells'}<=set(payload):raise AdmissionError('cell payload required')
        a=_ray(ray,m);ranges=_ranges(token_intervals,m)
        if type(witness) is not dict or set(witness)!={'first_cell','second_cell'}:raise AdmissionError('invalid determinant witness')
        cells=payload['cells'];bands=payload['bands']
        indices=[F._integer(witness[k],k,0,len(cells)-1) for k in ('first_cell','second_cell')]
        if indices[0]==indices[1]:raise AdmissionError('distinct witness cells required')
        forms=[]
        for index in indices:
            cell=cells[index]
            if type(cell) is not dict or type(cell.get('count')) is not int or cell['count']<=0:raise AdmissionError('positive actual cell count required')
            bi=F._integer(cell.get('band'),'band',0,len(bands)-1);pc=F._integer(cell.get('parent_category'),'pc',0,10);hc=F._integer(cell.get('child_category'),'hc',0,10)
            deltas=_cell_deltas(bands[bi],pc,hc,m);proper=A._linear(deltas,a,m);total=A._linear(deltas,[Fraction(1)]*10,m);forms.append((proper,total))
        det={};_quad_add(det,forms[0][0],forms[1][1],Fraction(1),m);_quad_add(det,forms[1][0],forms[0][1],Fraction(-1),m)
        lo,hi=_quad_interval(det,ranges,m)
        if lo<=0<=hi:
            out.update(status='UNRESOLVED_INTERVAL',determinant_lower=str(lo),determinant_upper=str(hi),noncircularity_proved=False)
        else:out.update(status='VERIFIED_NONCIRCULARITY',determinant_lower=str(lo),determinant_upper=str(hi),noncircularity_proved=True,cell_admission_still_required=True)
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _done(out,m,error)
    return _done(out,m)


def verify_coefficient_norm(kernel,P,base,certificate,meter=None):
    """Universal floor-count L2 bound on a fixed prefix kernel after P folds.

    Certificate exact {'I':qstr,'E':qstr,'K':qstr}; I integral of step², E=sum
    step² over breakpoint intervals, K=I+E/base. No mu signs are inspected.
    """
    import check_mobius_prime_mass_gate_078 as M
    m=meter or Meter();out={'status':'INVALID'}
    try:
        original=M._kernel(kernel,m);primes=F._primes(P,m)
        if type(P) is not list or list(primes)!=sorted(P):raise AdmissionError('sorted P required')
        b=F._integer(base,'base',1,(1<<4096)-1)
        divisors=[(1,1)]
        for p in primes:divisors += [(d*p,-sign) for d,sign in divisors]
        if len(original)*len(divisors)>MAX_TERMS:raise ResourceLimit('prospective folded kernel gate')
        m.reserve(_resident()+8192*(1+len(original)*len(divisors)))
        folded={}
        for d,a in original.items():
            for mult,sign in divisors:
                divisor=d*mult;value=a if sign==1 else -a;new=_add(folded.get(divisor,Fraction(0)),value,m)
                if new:folded[divisor]=new
                else:folded.pop(divisor,None)
        events={};value=Fraction(0)
        for d,a in folded.items():
            point=Fraction(1,d);events[point]=_add(events.get(point,Fraction(0)),a,m);value=_add(value,a,m)
        points=sorted({Fraction(0)}|set(events));I=E=Fraction(0)
        for lo,hi in zip(points,points[1:]):
            value=_add(value,-events.get(lo,Fraction(0)),m)
            square=_mul(value,value,m);I=_add(I,_mul(square,_add(hi,-lo,m),m),m);E=_add(E,square,m)
        K=_add(I,_divide(E,Fraction(b),m),m)
        if type(certificate) is not dict or set(certificate)!={'I','E','K'}:raise AdmissionError('invalid norm certificate')
        for key,value in (('I',I),('E',E),('K',K)):
            if _rational(certificate[key],key,m)!=value:raise AdmissionError('coefficient norm '+key+' mismatch')
        out.update(status='VERIFIED_UNIFORM_COEFFICIENT_NORM',I=str(I),E=str(E),K=str(K),base=b,coefficient_l2_upper='I*u+E for every positive integer u; K*u for u>=base',flux_ray_gram_upper='3*max_i|a_i|^2*K*u when child=floor(u/2)>=base',source_kernel_binding_still_required=True,arithmetic_correlation_still_required=True,uniform_coefficient_norm_proved=True,folded_kernel=M._saved(folded),max_divisor=max(folded,default=0),sum_weights=str(sum(folded.values(),Fraction(0))),excluded_primes=list(primes))
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _done(out,m,error)
    result=_done(out,m);result['finite_identity_only']=False;return result

def verify_inactive(folded_kernel,gamma,base,indices,meter=None):
    """Sufficient uniform zero-coordinate certificate for an ALREADY folded kernel."""
    import check_mobius_prime_mass_gate_078 as M
    m=meter or Meter();out={'status':'INVALID','uniform_inactive_coordinates_proved':False}
    try:
        kernel=M._kernel(folded_kernel,m);g=_rational(gamma,'gamma',m);b=F._integer(base,'base',1,(1<<4096)-1)
        if g<0 or type(indices) is not list or indices!=sorted(set(indices)):raise AdmissionError('invalid gamma/indices')
        total=Fraction(0)
        for a in kernel.values():total=_add(total,a,m)
        maxd=max(kernel,default=0)
        for i in indices:
            F._integer(i,'inactive index',0,9)
            if i==0:valid=b>=maxd and total==0
            else:valid=1<=i<=6 and _mul(Fraction(i),g,m)>=1
            if not valid:
                out.update(status='UNSUPPORTED',reason='requested coordinate is not proved uniformly inactive',index=i)
                return _done(out,m)
        out.update(status='VERIFIED_INACTIVE_COORDINATES',indices=indices,base=b,max_divisor=maxd,sum_weights=str(total),uniform_inactive_coordinates_proved=True,folded_kernel_binding_still_required=True)
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _done(out,m,error)
    result=_done(out,m);result['finite_identity_only']=False;return result

def verify_cover(target,rays,coefficients,kappas,K,certificate,meter=None,precision=24):
    """Conditional triangle cover; does not prove any uniform covariance leaf."""
    from check_mobius_prime_storage_073 import _integer_root,_power_compare
    m=meter or Meter();out={'status':'INVALID','conditional_cover_verified':False}
    try:
        F._integer(precision,'precision',8,24)
        if type(target) is not list or len(target)!=10 or type(rays) is not list or type(coefficients) is not list or type(kappas) is not list or not len(rays)==len(coefficients)==len(kappas) or len(rays)>1024:raise AdmissionError('invalid cover shape')
        d=[_rational(x,'target',m) for x in target]
        if any(x not in (0,1) for x in d):raise AdmissionError('cover target must be binary active-coordinate sum')
        parsed=[_ray(ray,m) for ray in rays];ts=[_rational(x,'cover coefficient',m) for x in coefficients];ks=[_rational(x,'kappa',m) for x in kappas];norm=_rational(K,'K',m)
        if norm<0 or any(k<0 for k in ks):raise AdmissionError('negative covariance/norm price')
        reconstructed=[Fraction(0)]*10;price=Fraction(0);root_bounds=[]
        for a,t,k in zip(parsed,ts,ks):
            for i,value in enumerate(a):reconstructed[i]=_add(reconstructed[i],_mul(t,value,m),m)
            amax=max(abs(value) for value in a);radicand=_mul(_mul(_mul(Fraction(3),norm,m),k,m),_mul(amax,amax,m),m)
            # sqrt rational via exact integer comparison on denominator-cleared grid.
            shift=2*precision
            if radicand.numerator.bit_length()+shift>100000:raise ResourceLimit('cover square-root bit gate')
            scaled_num=radicand.numerator<<shift;target_int=scaled_num//radicand.denominator;root=_integer_root(target_int,2,m)
            exact=root*root*radicand.denominator==scaled_num
            bound=Fraction(root if exact else root+1,1<<precision)
            price=_add(price,_mul(abs(t),bound,m),m);root_bounds.append(str(bound))
        if reconstructed!=d:raise AdmissionError('cover target coefficient identity fails')
        price=_mul(price,price,m)
        if type(certificate) is not dict or set(certificate)!={'price'} or _rational(certificate['price'],'price',m)!=price:raise AdmissionError('conditional cover price mismatch')
        out.update(status='VERIFIED_CONDITIONAL_COVER',conditional_cover_verified=True,price=str(price),sqrt_upper_bounds=root_bounds,conditional_on_all_uniform_local_leaves=True,conditional_on_independent_noncircularity=True,conditional_on_uniform_coefficient_norm=True,conditional_on_inactive_coordinate_certificate=True,conditional_on_common_q_at_least_one=True,uniform_target_bound_proved=False,conditional_young_drift_prices={'tau_3/4':str(_mul(Fraction(3),price,m)),'tau_1':str(_mul(Fraction(2),price,m))},uniform_R_drift_proved=False)
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _done(out,m,error)
    return _done(out,m)

def verify_kernel_row(folded_kernel,u,intervals,meter=None):
    """Bind the paid ALREADY folded fixed prefix kernel to one saved row function."""
    import check_mobius_prime_mass_gate_078 as M
    m=meter or Meter();out={'status':'INVALID'}
    try:
        kernel=M._kernel(folded_kernel,m);scale=F._integer(u,'u',1,F.MAX_PARENT);rows,cost=F._intervals(intervals,m)
        m.reserve(_resident()+32*cost+8192*(1+len(kernel)));expected={}
        for divisor,weight in kernel.items():
            endpoint=scale//divisor
            if endpoint:
                F._join(expected.setdefault(0,{}),{'1':weight},1,m);F._join(expected.setdefault(endpoint,{}),{'1':weight},-1,m)
        witness=F._compare_events(expected,F._function_events(rows,m),m)
        if witness:out['first_witness']=witness;raise AdmissionError('saved row fixed-kernel function mismatch')
        out.update(status='VERIFIED_KERNEL_ROW',u=scale,intervals_checked=len(rows),fixed_kernel_row_verified=True,folded_kernel_binding_still_required=True,coefficient_norm_admission_still_required=True)
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _done(out,m,error)
    return _done(out,m)

def verify_complete_base(folded_kernel,base,certificate,meter=None):
    """Pay every small integer scale by |R(v)|<=v*sum|b_d|/d.

    For 1<=q<2 and 1<=v<2*base, R(v)^2/v^q<=2*base*A^2.
    This is a complete bounded-scale base, not an all-scale signed estimate.
    """
    import check_mobius_prime_mass_gate_078 as M
    m=meter or Meter();out={'status':'INVALID'}
    try:
        kernel=M._kernel(folded_kernel,m);b=F._integer(base,'base',1,(1<<4096)-1)
        A=Fraction(0)
        for d,a in kernel.items():A=_add(A,_divide(abs(a),Fraction(d),m),m)
        B=_mul(_mul(Fraction(2*b),A,m),A,m)
        if type(certificate) is not dict or set(certificate)!={'A','B'}:raise AdmissionError('invalid complete base certificate')
        if _rational(certificate['A'],'A',m)!=A or _rational(certificate['B'],'B',m)!=B:raise AdmissionError('complete base price mismatch')
        out.update(status='VERIFIED_COMPLETE_BASE',A=str(A),B=str(B),base=b,
            complete_base_proved=True,domain='every integer 1<=v<2*base, every real 1<=q<2',
            folded_kernel_binding_still_required=True,uniform_large_scale_growth_proved=False)
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _done(out,m,error)
    result=_done(out,m);result['finite_identity_only']=False;return result

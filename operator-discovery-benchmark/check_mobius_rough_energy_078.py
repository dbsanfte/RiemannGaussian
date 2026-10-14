"""Independent078 rough feature, energy and finite drift admission.

Eratosthenes prime-factor/sign-flip/square-mask source; no producer imports.
Frozen independent077 interval schema and073 bounded rational roots reused.
"""
from fractions import Fraction
import numpy as np
import check_mobius_residual_fold_077 as F
from check_mobius_prime_storage_073 import (AdmissionError,ResourceLimit,_rational,_add,_mul,_divide,_power_target,_integer_root,_power_compare,power_enclosure)
MAX_HORIZON=4000000
MEMORY_BUDGET=4*1024**3
class Meter(F.Meter):pass
_FACTOR=None
_QUERIES={}
_QUERY_BYTES=0
_POWER_CACHE={}
_POWER_BYTES=0

def _resident():return (0 if _FACTOR is None else sum(a.nbytes for a in _FACTOR.values()))+_QUERY_BYTES+_POWER_BYTES

def ensure_horizon(H,meter=None):
    """Largest-only independently factored source cache, returned readonly views."""
    global _FACTOR
    m=meter or Meter();F._integer(H,'horizon',0,MAX_HORIZON)
    if _FACTOR is None or len(_FACTOR['mu'])<=H:
        m.reserve(_resident()+48*(H+1)+4096);m.charge(H+1)
        mu=np.ones(H+1,dtype=np.int8);mu[0]=0
        least=np.zeros(H+1,dtype=np.int32);omega=np.zeros(H+1,dtype=np.uint8)
        if H>=1:least[1]=H+1
        for p in range(2,H+1):
            m.charge()
            if least[p]==0:
                size=H//p;m.charge(4*size+H//(p*p))
                part=least[p::p];part[part==0]=p
                mu[p::p]*=-1;omega[p::p]+=1
                if p*p<=H:mu[p*p::p*p]=0
        for a in (mu,least,omega):a.flags.writeable=False
        _FACTOR={'mu':mu,'least':least,'omega':omega}
    result={k:v[:H+1].view() for k,v in _FACTOR.items()}
    for a in result.values():a.flags.writeable=False
    return result

def ceil_power(H,gamma,meter=None):
    m=meter or Meter()
    if H==0 or gamma==0:return 1
    target=_power_target(H,gamma.numerator,gamma.denominator,0,m)
    root=_integer_root(target,gamma.denominator,m)
    return root if _power_compare(root,gamma.denominator,target,m)==0 else root+1

def _queries(H,gamma,P,m):
    global _QUERY_BYTES
    m.charge()
    y=ceil_power(H,gamma,m);s1=ceil_power(H,gamma/3,m);s2=ceil_power(H,2*gamma/3,m)
    # Compare without forming an oversized seventh power.
    if H and _power_compare(y,7,H,m)<0:raise AdmissionError('rough terminal degree gate y^7>=H is unpaid')
    N=max(H,0 if _FACTOR is None else len(_FACTOR['mu'])-1)
    key=(N,y,s1,s2,tuple(P))
    if key in _QUERIES:return _QUERIES[key],(y,s1,s2)
    size=40*(N+1)
    if _QUERY_BYTES+size>512*1024**2:_QUERIES.clear();_QUERY_BYTES=0
    m.reserve(_resident()+88*(N+1)+4096)
    source=ensure_horizon(N,m);n=np.arange(N+1,dtype=np.int32)
    allowed=source['mu']!=0;allowed[0]=False
    for p in P:m.charge(N+1);allowed &= n%p!=0
    least=source['least'];omega=source['omega'];rough=allowed & (least>min(y,N))
    if N>=1:rough[1]=allowed[1]
    # Dense integer prefixes intentionally independent of producer positions.
    result=np.zeros((10,N+1),dtype=np.int32);m.charge(10*(N+1))
    for degree in range(7):
        mask=rough & (omega==degree)
        result[degree]=np.cumsum(np.where(mask,source['mu'],0),dtype=np.int32)
    for j,(lo,hi) in enumerate(((0,s1),(s1,s2),(s2,y)),7):
        mask=allowed & (least>min(lo,N)) & (least<=min(hi,N))
        if N>=1:mask[1]=False
        result[j]=np.cumsum(np.where(mask,source['mu'],0),dtype=np.int32)
    result.flags.writeable=False;_QUERIES[key]=result;_QUERY_BYTES+=result.nbytes
    return result,(y,s1,s2)

def _polys(raw,m):
    if type(raw) is not list or len(raw)!=10:raise AdmissionError('ten feature polynomials required')
    if any(type(poly) is not dict for poly in raw) or sum(len(poly) for poly in raw)>F.MAX_TERMS:raise AdmissionError('feature term gate')
    cost=sum(F._raw_cost(poly) for poly in raw);m.reserve(_resident()+32*cost+4096)
    return [F._poly(poly,m) for poly in raw]

def _done(out,m,error=None):
    out=F._finish(out,m,error)
    out.update(uniform_growth_proved=False,uniform_drift_proved=False,uniform_source_bound_proved=False,complete_base_proved=False)
    return out

def verify_features(intervals,excluded_primes,gamma,features,expected_residual=None,meter=None):
    m=meter or Meter();out={'status':'INVALID'}
    try:
        rows,cost=F._intervals(intervals,m);P=F._primes(excluded_primes,m)
        if list(P)!=sorted(P):raise AdmissionError('excluded primes must be sorted')
        g=_rational(gamma,'gamma',m)
        if g<0:raise AdmissionError('negative feature gamma')
        actual=_polys(features,m);H=max((r for l,r,p in rows),default=0)
        m.reserve(_resident()+32*cost+88*(H+1)+4096)
        queries,cuts=_queries(H,g,P,m);expected=[{} for _ in range(10)]
        for index in range(10):
            for l,r,poly in rows:
                count=int(queries[index,r])-int(queries[index,l]);m.charge()
                if count:
                    for token,a in poly.items():
                        value=_mul(Fraction(count),a,m);new=_add(expected[index].get(token,Fraction(0)),value,m)
                        if new:expected[index][token]=new
                        else:expected[index].pop(token,None)
        if actual!=expected:raise AdmissionError('arithmetic feature polynomial mismatch')
        residual={}
        for poly in expected:F._join(residual,poly,1,m)
        if expected_residual is not None:
            if F._poly(expected_residual,m)!=residual:raise AdmissionError('complete residual sum binding mismatch')
        out.update(status='VERIFIED_FEATURES',horizon=H,cutoff=cuts[0],subcutoffs=list(cuts[1:]),features=[{t:str(a) for t,a in poly.items()} for poly in expected],residual_polynomial={t:str(a) for t,a in residual.items()},source_row_admission_still_required=True)
    except (ValueError,TypeError,KeyError,OverflowError) as error:
        result=_done(out,m,error)
        if 'degree gate' in str(error):result['domain_unpaid']=True
        return result
    return _done(out,m)

PROGRAM_KEYS={'schema','q','tau','rays','innovation_C'}
def _program(raw,m):
    if type(raw) is not dict or set(raw)!=PROGRAM_KEYS or raw['schema']!='rough-energy-program-v1':raise AdmissionError('invalid energy program schema')
    q=_rational(raw['q'],'q',m);tau=_rational(raw['tau'],'tau',m);C=_rational(raw['innovation_C'],'innovation_C',m)
    if not 1<=q<2 or not 0<=tau<=1 or C<0:raise AdmissionError('invalid q/tau/C domain')
    if type(raw['rays']) is not list or len(raw['rays'])>1024:raise AdmissionError('invalid rays')
    ray_cost=4096
    for ray in raw['rays']:
        if type(ray) is dict:
            ray_cost+=2048+sum(4*len(v) for v in ray.get('a',[]) if type(v) is str) if type(ray.get('a')) is list else 2048
    m.reserve(_resident()+16*ray_cost)
    rays=[]
    for ray in raw['rays']:
        if type(ray) is not dict or set(ray)!={'a','eta','lambda'} or type(ray['a']) is not list or len(ray['a'])!=10:raise AdmissionError('invalid ray schema')
        a=[_rational(v,'ray a',m) for v in ray['a']];eta=_rational(ray['eta'],'eta',m);weight=_rational(ray['lambda'],'lambda',m)
        if eta<0 or weight<=0 or all(x==a[0] for x in a):raise AdmissionError('zero/projection-only ray or invalid eta/lambda')
        rays.append((a,eta,weight))
    return q,tau,C,rays

def _row(raw,m):
    if type(raw) is not dict or set(raw)!={'u','features','token_intervals'}:raise AdmissionError('invalid energy row schema')
    u=F._integer(raw['u'],'u',1,F.MAX_PARENT);features=_polys(raw['features'],m);ranges=raw['token_intervals']
    if type(ranges) is not dict or len(ranges)>F.MAX_TERMS:raise AdmissionError('invalid token ranges')
    range_cost=4096
    for token,pair in ranges.items():
        if type(pair) in (tuple,list):range_cost+=1024+sum(4*len(v) for v in pair if type(v) is str)
    m.reserve(_resident()+16*range_cost+4096)
    parsed={}
    for token,pair in ranges.items():
        if type(token) is not str or not token or len(token)>256 or type(pair) not in (tuple,list) or len(pair)!=2:raise AdmissionError('invalid token range')
        lo,hi=(_rational(v,'token endpoint',m) for v in pair)
        if lo>hi:raise AdmissionError('inverted token range')
        parsed[token]=(lo,hi)
    if any(token not in parsed for poly in features for token in poly):raise AdmissionError('missing feature token enclosure')
    return u,features,parsed

def _linear(features,a,m):
    result={}
    for poly,coefficient in zip(features,a):
        if coefficient:
            for token,value in poly.items():
                new=_add(result.get(token,Fraction(0)),_mul(coefficient,value,m),m)
                if new:result[token]=new
                else:result.pop(token,None)
    return result

def _poly_interval(poly,ranges,m):
    lo=hi=Fraction(0)
    for token,a in poly.items():
        if token not in ranges:raise AdmissionError('missing token enclosure')
        x,y=ranges[token]
        if a<0:x,y=y,x
        lo=_add(lo,_mul(a,x,m),m);hi=_add(hi,_mul(a,y,m),m)
    return lo,hi

def _square(lo,hi,m):
    a,b=_mul(lo,lo,m),_mul(hi,hi,m)
    return Fraction(0) if lo<=0<=hi else min(a,b),max(a,b)

def _bounds(u,exponent,precision,m):
    global _POWER_BYTES
    key=(u,exponent,precision);m.charge()
    if key in _POWER_CACHE:return _POWER_CACHE[key]
    m.reserve(_resident()+1024*1024)
    result=power_enclosure(u,exponent,precision,m)
    size=1024+sum((v.numerator.bit_length()+v.denominator.bit_length()+7)//8 for v in result)
    if _POWER_BYTES+size>64*1024**2:_POWER_CACHE.clear();_POWER_BYTES=0
    m.reserve(_resident()+size);_POWER_CACHE[key]=result;_POWER_BYTES+=size
    return result

def _energy(parsed_program,parsed_row,m,precision):
    q,tau,C,rays=parsed_program;u,features,ranges=parsed_row
    # Preserve the shared-token residual polynomial before interval evaluation.
    residual=_linear(features,[Fraction(1)]*10,m);Rlo,Rhi=_poly_interval(residual,ranges,m);lower,upper=_square(Rlo,Rhi,m)
    for a,eta,weight in rays:
        ray=_linear(features,a,m);lo,hi=_poly_interval(ray,ranges,m);slo,shi=_square(lo,hi,m)
        plo,phi=(Fraction(1),Fraction(1)) if eta==0 else _bounds(u,_mul(Fraction(2),eta,m),precision,m)
        lower=_add(lower,_mul(weight,_divide(slo,phi,m),m),m);upper=_add(upper,_mul(weight,_divide(shi,plo,m),m),m)
    qlo,qhi=_bounds(u,q,precision,m)
    return {'energy_lower':lower,'energy_upper':upper,'normalized_lower':_divide(lower,qhi,m),'normalized_upper':_divide(upper,qlo,m),'residual_lower':Rlo,'residual_upper':Rhi}

def verify_energy(program,row,meter=None,precision=20):
    m=meter or Meter();out={'status':'INVALID'}
    try:
        F._integer(precision,'precision',8,24);p=_program(program,m);r=_row(row,m);energy=_energy(p,r,m,precision)
        out.update(status='VERIFIED_ENERGY_ENCLOSURE',u=r[0],projection_verified=True,features_admission_still_required=True,findings={'projection':'E>=R^2 by nonnegative sum of squares','growth':'positive semidefiniteness supplies no uniform growth bound'},**{key:str(v) for key,v in energy.items()})
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _done(out,m,error)
    return _done(out,m)

def verify_drift(program,parent,child,meter=None,precision=20):
    m=meter or Meter();out={'status':'INVALID'}
    try:
        F._integer(precision,'precision',8,24);p=_program(program,m);pr=_row(parent,m);cr=_row(child,m)
        if pr[0]<2 or cr[0]!=pr[0]//2:raise AdmissionError('child must be floor(parent/2), positive')
        pe=_energy(p,pr,m,precision);ce=_energy(p,cr,m,precision);q,tau,C,rays=p
        lo=_add(pe['normalized_lower'],-_mul(tau,ce['normalized_upper'],m),m);hi=_add(pe['normalized_upper'],-_mul(tau,ce['normalized_lower'],m),m)
        status='CERTIFIED_FINITE' if hi<=C else 'REFUTED_FINITE' if lo>C else 'UNRESOLVED_INTERVAL'
        out.update(status=status,u=pr[0],child_u=cr[0],lower=str(lo),upper=str(hi),threshold=str(C),projection_verified=True,parent_energy={k:str(v) for k,v in pe.items()},child_energy={k:str(v) for k,v in ce.items()},features_admission_still_required=True,findings={'scope':'finite drift only; complete base and all-scale drift remain unpaid','tau_endpoint':'tau=1 permits at most logarithmic normalized growth from an eventual uniform drift premise'})
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _done(out,m,error)
    return _done(out,m)

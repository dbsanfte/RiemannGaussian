"""Independent count-adaptive076 certificate checker.

Reuses frozen independent075 source/shape/Meter logic and073 bounded exact
rational/root arithmetic. No producer imports; source admission stays separate.
"""
from fractions import Fraction
import check_mobius_prime_moment_075 as F
from check_mobius_prime_storage_073 import (AdmissionError, ResourceLimit,
    _rational, _integer, _mul, _add, _divide, power_enclosure)
MEMORY_BUDGET=4*1024**3
_COUNT_CACHE={}
_BASE_BOUND_CACHE={}
_COUNT_BYTES=0
_BASE_BYTES=0
class Meter(F.Meter):
    def reserve(self,total_bytes):
        super().reserve(total_bytes+_COUNT_BYTES+_BASE_BYTES)
def _size(value):
    if isinstance(value,Fraction):return 128+(value.numerator.bit_length()+value.denominator.bit_length()+15)//8
    return 64+value.bit_length()//8

def count_enclosure(count,gamma,precision,meter=None):
    """Certified enclosure of max(1,count)**gamma, explicit-key cache."""
    global _COUNT_BYTES
    m=meter or Meter();_integer(count,'count',0)
    if not isinstance(gamma,Fraction) or gamma<0:raise AdmissionError('invalid gamma')
    if type(precision) is not int or not 8<=precision<=24:raise AdmissionError('invalid precision')
    count=max(1,count);key=(count,gamma,precision);m.charge()
    if key in _COUNT_CACHE:return _COUNT_CACHE[key]
    m.reserve(m.input_bytes+F.cache_bytes()+m.pending_bytes+1024*1024)
    result=(Fraction(1),Fraction(1)) if gamma==0 or count==1 else power_enclosure(count,gamma,precision,m)
    size=256+_size(count)+_size(gamma)+sum(_size(v) for v in result)
    if size>64*1024**2:raise ResourceLimit('count cache entry exceeds memory limit')
    if _COUNT_BYTES+size>64*1024**2:_COUNT_CACHE.clear();_COUNT_BYTES=0
    m.reserve(m.input_bytes+F.cache_bytes()+m.pending_bytes+size)
    _COUNT_CACHE[key]=result;_COUNT_BYTES+=size
    return result

def complete_base_bound(U,q,precision,meter=None):
    """Upper bound for every integer1..U, cached by exact(U,q,precision)."""
    global _BASE_BYTES
    m=meter or Meter();_integer(U,'base_u',16)
    if not isinstance(q,Fraction) or not 1<=q<2 or type(precision) is not int or not 8<=precision<=24:raise AdmissionError('invalid complete base exponent/precision')
    key=(U,q,precision);m.charge()
    if key in _BASE_BOUND_CACHE:return dict(_BASE_BOUND_CACHE[key])
    # Gate the full sieve and all retained objects BEFORE allocating/source work.
    m.reserve(m.input_bytes+F.cache_bytes()+24*(U//4+1)+65536)
    m.charge(5*U)
    M,pi=F.source(U//4,m)
    bound=Fraction(0);worst=1
    for u in range(1,U+1):
        m.charge(5);z=F.G(u,M)
        if not z:continue
        lo,hi=power_enclosure(u,q,precision,m)
        upper=_divide(Fraction(z*z),lo,m)
        if upper>bound:bound,worst=upper,u
    result={'upper':bound,'u':worst,'integers_checked':U}
    size=512+_size(bound)+_size(U)+_size(q)
    if _BASE_BYTES+size>16*1024**2:_BASE_BOUND_CACHE.clear();_BASE_BYTES=0
    m.reserve(m.input_bytes+F.cache_bytes()+24*(U//4+1)+size)
    _BASE_BOUND_CACHE[key]=dict(result);_BASE_BYTES+=size
    return result

def _witness_reserve(values,m):
    # Decimal formatting and retained JSON witnesses are larger than integers.
    size=1024+sum(512+(v.numerator.bit_length()+v.denominator.bit_length())//3 for v in values)
    m.input_bytes+=size
    m.reserve(m.input_bytes+F.cache_bytes())
def scale_interval(s,lo,hi,m):
    return (_mul(s,lo,m),_mul(s,hi,m)) if s>=0 else (_mul(s,hi,m),_mul(s,lo,m))
def square_interval(lo,hi,meter=None):
    m=meter or Meter()
    if lo>hi:raise AdmissionError('inverted interval')
    x,y=_mul(lo,lo,m),_mul(hi,hi,m)
    return (Fraction(0) if lo<=0<=hi else min(x,y),max(x,y))
def operator_interval(row,atoms,coefficients,precision,meter=None):
    m=meter or Meter();low=high=Fraction(0)
    for (column,gamma),a in zip(atoms,coefficients):
        m.charge()
        if not a:continue
        denlo,denhi=count_enclosure(row['counts'][column],gamma,precision,m)
        x=_mul(a,Fraction(row['components'][column]),m)
        lo,hi=scale_interval(x,_divide(Fraction(1),denhi,m),_divide(Fraction(1),denlo,m),m)
        low=_add(low,lo,m);high=_add(high,hi,m)
    return low,high

def structural_cauchy(atoms,a,beta,prime_columns,meter=None):
    """Sufficient arbitrary-child-vector proof, retaining repeated columns."""
    m=meter or Meter();A=[Fraction(0) for _ in beta]
    for (column,gamma),coefficient in zip(atoms,a):
        if coefficient and column<prime_columns and gamma<Fraction(1,2):return False
        A[column]=_add(A[column],abs(coefficient),m)
    price=Fraction(0)
    for x,y in zip(A,beta):
        if not x:continue
        if y<=0:return False
        price=_add(price,_divide(_mul(x,x,m),y,m),m)
    return price<=1

def required_prices(ts,ds,U,m):
    lowerlog=Fraction(2,3)*((U//4).bit_length()-1);required=[]
    for lo,hi in zip(ts,ts[1:]):
        z=_divide(_add(hi,-lo,m),_add(hi,lo,m),m);z2=_mul(z,z,m);term=z;log=Fraction(0)
        for j in range(12):
            log=_add(log,_divide(_mul(Fraction(2),term,m),Fraction(2*j+1),m),m);term=_mul(term,z2,m)
        log=_add(log,_divide(_mul(Fraction(2),term,m),_mul(Fraction(25),_add(Fraction(1),-z2,m),m),m),m)
        H=_mul(Fraction(2),_add(log,_divide(Fraction(1),_mul(hi,lowerlog,m),m),m),m)
        required.append(Fraction((H.numerator*(1<<20)+H.denominator-1)//H.denominator,1<<20))
    return required+[Fraction(1,d) for d in ds]
PROGRAM_KEYS={'schema','spec','atoms','operator','beta','correlation_mode','q','base_u','price_bounds','rho_upper','sqrt_rho_upper','innovation_C','base_upper','bound_B','precision','training_scales','uniform_innovation_proved','uniform_source_bound_proved','RH_proved'}
def _scales(values,U,m,name):
    if type(values) is not list or not values:raise AdmissionError(name+' must be nonempty list')
    m.reserve(m.input_bytes+F.cache_bytes()+256*len(values))
    previous=U
    for u in values:
        _integer(u,name,1)
        if u<=previous:raise AdmissionError(name+' must be sorted distinct and >base')
        previous=u
    return values

def verify_program(program,data,meter=None,scales=None):
    m=meter or Meter()
    out={'status':'INVALID','conditional_induction_verified':False,'universal_correlation_proved':False,'uniform_source_bound_proved':False,'RH_proved':False,'failures':[],'worst_innovation':None,'scales_checked':0,'correlation_theorem_tightenings':0}
    try:
        p=program
        if type(p) is not dict or set(p)!=PROGRAM_KEYS or p['schema']!='count-adaptive-control-program-v1':raise AdmissionError('invalid program schema')
        ts,ds=F.spec_parse(p['spec'],m);_,_,rows=F.validate_rows(data,m)
        if p['spec']!=data['spec']:raise AdmissionError('source spec mismatch')
        for flag in ('uniform_innovation_proved','uniform_source_bound_proved','RH_proved'):
            if p[flag] is not False:raise AdmissionError('false proof flags required')
        mode=p['correlation_mode']
        if mode not in ('structural_cauchy','arithmetic_claim'):raise AdmissionError('invalid correlation mode')
        q=_rational(p['q'],'q',m)
        if not 1<=q<2:raise AdmissionError('q outside [1,2)')
        U=_integer(p['base_u'],'base_u',16);precision=_integer(p['precision'],'precision',8)
        if precision>24:raise AdmissionError('precision >24')
        training=_scales(p['training_scales'],U,m,'training_scales')
        size=len(ts)-1+len(ds);raw_atoms=p['atoms'];raw_a=p['operator']
        if type(raw_atoms) is not list or type(raw_a) is not list or len(raw_atoms)!=len(raw_a):raise AdmissionError('atom/operator shape')
        m.input_bytes+=4096+2048*len(raw_atoms)
        m.reserve(m.input_bytes+F.cache_bytes()+512*len(raw_atoms))
        atoms=[];previous=None
        for atom in raw_atoms:
            if type(atom) is not dict or set(atom)!={'column','gamma'}:raise AdmissionError('invalid atom schema')
            column=_integer(atom['column'],'column',0)
            if column>=size:raise AdmissionError('column outside source')
            gamma=_rational(atom['gamma'],'gamma',m)
            if gamma<0:raise AdmissionError('negative gamma')
            item=(column,gamma)
            if previous is not None and item<=previous:raise AdmissionError('atoms must be sorted unique')
            previous=item;atoms.append(item)
        a=[_rational(v,'operator',m) for v in raw_a];vectors={}
        for key in ('beta','price_bounds'):
            if type(p[key]) is not list or len(p[key])!=size:raise AdmissionError('source vector shape')
            vectors[key]=[_rational(v,key,m) for v in p[key]]
        beta,prices=vectors['beta'],vectors['price_bounds']
        if any(v<0 for v in beta+prices):raise AdmissionError('negative beta/price')
        rho,r,C,base,B=(_rational(p[k],k,m) for k in ('rho_upper','sqrt_rho_upper','innovation_C','base_upper','bound_B'))
        if min(rho,r,C,base,B)<0 or r>=1:raise AdmissionError('invalid nonnegative bounds or contraction')
        if any(x<y for x,y in zip(prices,required_prices(ts,ds,U,m))):raise AdmissionError('price bound too small')
        price_sum=Fraction(0)
        for x,y in zip(beta,prices):price_sum=_add(price_sum,_mul(x,y,m),m)
        gap=_add(Fraction(1),-r,m)
        if rho<price_sum or rho>_mul(r,r,m) or base>B or C>_mul(_mul(gap,gap,m),B,m):raise AdmissionError('invalid contraction/base/innovation budget')
        proof=structural_cauchy(atoms,a,beta,len(ts)-1,m)
        if mode=='structural_cauchy' and not proof:raise AdmissionError('structural Cauchy certificate fails')
        bound=complete_base_bound(U,q,precision,m)
        if bound['upper']>base:raise AdmissionError('complete base upper fails at '+str(bound['u']))
        selected=_scales(training if scales is None else scales,U,m,'evaluation scales')
        m.input_bytes+=256*len(rows)+4096*len(selected)
        m.reserve(m.input_bytes+F.cache_bytes())
        indexed={row['u']:row for row in rows}
        if any(u not in indexed for u in selected):raise AdmissionError('missing evaluation row')
        out['conditional_induction_verified']=True;out['universal_correlation_proved']=proof
        out['complete_base']={'upper':str(bound['upper']),'u':bound['u'],'integers_checked':U}
        out['status']='VERIFIED_ON_FINITE_DOMAIN'
        worst_upper=None
        for u in selected:
            row=indexed[u];Llo,Lhi=operator_interval(row,atoms,a,precision,m)
            squarelo,squarehi=square_interval(Llo,Lhi,m);energy=Fraction(0)
            for b,v in zip(beta,row['moments']):energy=_add(energy,_mul(b,Fraction(v),m),m)
            # A separately proved structural theorem can tighten an ambiguous
            # square enclosure to its exact energy threshold, without rounding.
            if proof and squarelo<=energy and squarehi>energy:
                squarehi=energy;out['correlation_theorem_tightenings']+=1
            if squarehi>energy:
                _witness_reserve((squarelo,squarehi,energy,Llo,Lhi),m)
                out['failures'].append({'u':u,'lemma':'correlation','lower':str(squarelo),'upper':str(squarehi),'threshold':str(energy),'operator_lower':str(Llo),'operator_upper':str(Lhi),'status':'REFUTED' if squarelo>energy else 'UNRESOLVED_ROUNDING'})
            residual_lo=_add(Fraction(row['z']),-Lhi,m);residual_hi=_add(Fraction(row['z']),-Llo,m)
            reslo,reshi=square_interval(residual_lo,residual_hi,m);powerlo,powerhi=power_enclosure(u,q,precision,m)
            lower=_divide(reslo,powerhi,m);upper=_divide(reshi,powerlo,m)
            _witness_reserve((lower,upper,Llo,Lhi),m)
            witness={'u':u,'lower':str(lower),'upper':str(upper),'operator_lower':str(Llo),'operator_upper':str(Lhi)}
            if worst_upper is None or upper>worst_upper:out['worst_innovation']=witness;worst_upper=upper
            if upper>C:out['failures'].append(dict(witness,lemma='innovation',threshold=str(C),status='REFUTED' if lower>C else 'UNRESOLVED_ROUNDING'))
            out['scales_checked']+=1
        if out['failures']:out['status']='REFUTED' if any(f['status']=='REFUTED' for f in out['failures']) else 'UNRESOLVED_ROUNDING'
    except (ValueError,TypeError,KeyError,OverflowError) as error:
        out['status']='INVALID';out['reason']=str(error);out['conditional_induction_verified']=False;out['universal_correlation_proved']=False
        if isinstance(error,ResourceLimit):out['resource_limit']=True
    out['ops']=m.ops;out['peak_bytes']=m.peak_bytes;return out

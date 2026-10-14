"""Independent finite formal Möbius stencil and prime-toggle identity checker.

Only frozen independent073 rational arithmetic is reused. No producer, numerical
mu source or search is imported. Tokens are formal real labels, not assumed
independent; identities hold after every real substitution.
"""
from fractions import Fraction
from math import isqrt
from check_mobius_prime_storage_073 import AdmissionError, ResourceLimit, _rational, _add, _mul
MAX_N=16000003
MAX_PRIME=100000
MAX_TERMS=200000
MEMORY_BUDGET=4*1024**3
class Meter:
    def __init__(self,limit=300000000000):self.ops=0;self.limit=limit;self.peak_bytes=0
    def charge(self,count=1):
        self.ops+=count
        if self.ops>self.limit:raise ResourceLimit('work limit exceeded')
    def reserve(self,count):
        self.peak_bytes=max(self.peak_bytes,count)
        if count>MEMORY_BUDGET:raise ResourceLimit('prospective memory exceeds 4 GiB')
def _int(value,name,low,high):
    if type(value) is not int or not low<=value<=high:raise AdmissionError(name+' outside admitted integer range')
    return value
def _prime(p,m):
    _int(p,'prime',2,MAX_PRIME)
    for d in range(2,isqrt(p)+1):
        m.charge()
        if p%d==0:raise AdmissionError('prime is composite')
    return p
def _poly(raw,m):
    if type(raw) is not dict or len(raw)>MAX_TERMS:raise AdmissionError('invalid sparse polynomial')
    result={}
    for token,value in raw.items():
        if type(token) is not str or not token or len(token)>256:raise AdmissionError('invalid token label')
        coefficient=_rational(value,'polynomial coefficient',m)
        if coefficient==0:raise AdmissionError('zero coefficients must be omitted')
        result[token]=coefficient
    return result
def _map(raw,m):
    if type(raw) is not dict or len(raw)>MAX_TERMS:raise AdmissionError('invalid coefficient map')
    terms=0
    # First gate lengths before allocating any parsed map.
    for n,poly in raw.items():
        _int(n,'support',1,MAX_N)
        if type(poly) is not dict or not poly:raise AdmissionError('empty sparse map entry must be omitted')
        terms+=len(poly)
        if terms>MAX_TERMS:raise ResourceLimit('sparse term gate exceeded')
    m.reserve(4096+len(raw)*512+terms*4096)
    return {n:_poly(poly,m) for n,poly in raw.items()}
def _merge(target,n,poly,sign,m):
    row=target.setdefault(n,{})
    for token,value in poly.items():
        m.charge()
        new=_add(row.get(token,Fraction(0)),value if sign==1 else -value,m)
        if new:row[token]=new
        elif token in row:del row[token]
    if not row:del target[n]
def _finish(out,m,error=None):
    if error is not None:
        out['status']='INVALID';out['reason']=str(error)
        if isinstance(error,ResourceLimit):out['resource_limit']=True
    out.update(ops=m.ops,peak_bytes=m.peak_bytes,finite_identity_only=True,uniform_bound_proved=False,RH_proved=False)
    return out
def _difference(expected,actual):
    for n in sorted(set(expected)|set(actual)):
        if expected.get(n,{})!=actual.get(n,{}):
            return {'n':n,'expected':{t:str(v) for t,v in expected.get(n,{}).items()},'actual':{t:str(v) for t,v in actual.get(n,{}).items()}}
    return None

def verify_fold(before,after,p,prior_primes=()):
    m=Meter();out={'status':'INVALID'}
    try:
        _prime(p,m)
        if type(prior_primes) not in (tuple,list) or len(prior_primes)>MAX_PRIME:raise AdmissionError('invalid prior primes')
        m.reserve(4096+128*len(prior_primes))
        seen=set()
        for q in prior_primes:
            _prime(q,m)
            if q in seen or q==p:raise AdmissionError('fold primes must be distinct')
            seen.add(q)
        if type(before) is not dict or type(after) is not dict:raise AdmissionError('invalid coefficient maps')
        raw_terms=sum(len(poly) for poly in before.values() if type(poly) is dict)+sum(len(poly) for poly in after.values() if type(poly) is dict)
        m.reserve(8192+1024*(len(before)+len(after))+262144*raw_terms)
        old=_map(before,m);actual=_map(after,m)
        terms=sum(len(poly) for poly in old.values())+sum(len(poly) for poly in actual.values())
        m.reserve(8192+1024*(len(old)+len(actual))+262144*terms)
        expected={};squares=0;moved=0
        for n,poly in old.items():
            for q in seen:
                m.charge()
                if n%q==0:raise AdmissionError('before support violates retained coprime domain')
            if n%p:
                _merge(expected,n,poly,1,m)
            elif (n//p)%p:
                _merge(expected,n//p,poly,-1,m);moved+=1
            else:squares+=1
        witness=_difference(expected,actual)
        if witness is not None:out['first_witness']=witness;raise AdmissionError('fold coefficient identity mismatch')
        out.update(status='VERIFIED_IDENTITY',before_support=len(old),after_support=len(actual),squareful_support_removed=squares,moved_support=moved,retained_primes=list(prior_primes)+[p])
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _finish(out,m,error)
    return _finish(out,m)

def verify_stencil(components,coefficients):
    m=Meter();out={'status':'INVALID'}
    try:
        if type(components) is not list or len(components)>MAX_TERMS:raise AdmissionError('invalid components')
        parsed=[];terms=0;horizon=0
        for component in components:
            if type(component) is not dict or set(component)!={'parent','weight'}:raise AdmissionError('invalid component schema')
            parent=_int(component['parent'],'parent',0,4*MAX_N+3)
            if type(component['weight']) is not dict:raise AdmissionError('invalid component polynomial')
            terms+=len(component['weight'])
            if terms>MAX_TERMS:raise ResourceLimit('component term gate exceeded')
            horizon=max(horizon,parent//4)
        # Worst-case expansion is checked before parsing/allocating coefficient rows.
        possible=horizon*terms
        if possible>MAX_TERMS:raise ResourceLimit('prospective stencil sparse expansion exceeds term gate')
        m.reserve(4096+len(components)*1024+4096*terms+262144*possible+horizon*512)
        m.charge(horizon*max(1,len(components)))
        for component in components:parsed.append((component['parent'],_poly(component['weight'],m)))
        actual=_map(coefficients,m);expected={}
        # Independent prefix reconstruction; signs are literal source floors.
        for n in range(1,horizon+1):
            for u,poly in parsed:
                sign=(n<=u//8)-(n<=u//10)-(n<=u//4)+(n<=u//5)
                if sign:_merge(expected,n,poly,sign,m)
        witness=_difference(expected,actual)
        if witness is not None:out['first_witness']=witness;raise AdmissionError('stencil coefficient mismatch')
        out.update(status='VERIFIED_IDENTITY',components_checked=len(parsed),horizon=horizon,support=len(expected),terms=sum(len(poly) for poly in expected.values()))
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _finish(out,m,error)
    return _finish(out,m)

def bound_coefficients(coefficients,token_intervals):
    """Triangle bound on sum c(n)mu(n), after interval substitution and |mu|<=1.

    token_intervals maps labels to [canonical rational lower, upper]. No
    independence assumptions; repeated tokens retain their shared range.
    """
    m=Meter();out={'status':'INVALID','bound':None}
    try:
        if type(coefficients) is not dict:raise AdmissionError('invalid coefficient map')
        raw_terms=sum(len(poly) for poly in coefficients.values() if type(poly) is dict)
        m.reserve(8192+len(coefficients)*1024+262144*raw_terms)
        parsed=_map(coefficients,m)
        if type(token_intervals) is not dict or len(token_intervals)>MAX_TERMS:raise AdmissionError('invalid token intervals')
        m.reserve(4096+sum(len(poly) for poly in parsed.values())*262144+len(token_intervals)*4096)
        intervals={}
        for token,endpoints in token_intervals.items():
            if type(token) is not str or not token or len(token)>256 or type(endpoints) not in (tuple,list) or len(endpoints)!=2:raise AdmissionError('invalid token interval')
            lo,hi=(_rational(v,'interval endpoint',m) for v in endpoints)
            if lo>hi:raise AdmissionError('inverted token interval')
            intervals[token]=(lo,hi)
        total=Fraction(0);bounds={}
        for n,poly in parsed.items():
            lo=hi=Fraction(0)
            for token,a in poly.items():
                if token not in intervals:raise AdmissionError('missing token interval')
                left,right=intervals[token]
                if a<0:left,right=right,left
                lo=_add(lo,_mul(a,left,m),m);hi=_add(hi,_mul(a,right,m),m)
            absolute=max(abs(lo),abs(hi));total=_add(total,absolute,m)
            bounds[n]={'lower':str(lo),'upper':str(hi),'absolute_upper':str(absolute)}
        out.update(status='VERIFIED_BOUND',bound=str(total),coefficient_intervals=bounds,mu_assumption='|mu(n)|<=1',whole_supplied_domain=True)
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _finish(out,m,error)
    return _finish(out,m)

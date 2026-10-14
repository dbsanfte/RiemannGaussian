"""Independent075 moment checker; only rational/root arithmetic reused from frozen073.
No producer imports. Factor sieve and quotient grouped prime sums are independent.
"""
from array import array
from fractions import Fraction
from check_mobius_prime_storage_073 import (AdmissionError, ResourceLimit, _rational,
    _integer, _mul, _add, _divide, _power_target, _integer_root, power_enclosure)
MEMORY_BUDGET=4*1024**3
class Meter:
    def __init__(self, limit=300000000000):
        if type(limit) is not int or limit<0: raise ValueError('invalid limit')
        self.limit,self.ops=limit,0
        self.peak_bytes=0
        self.input_bytes=0
        self.pending_bytes=0
    def charge(self,count=1):
        if type(count) is not int or count<0: raise ValueError('invalid charge')
        self.ops+=count
        if self.ops>self.limit: raise ResourceLimit('operation limit exceeded')
    def reserve(self, total_bytes):
        """Check a conservative simultaneous allocation estimate before allocation."""
        if type(total_bytes) is not int or total_bytes<0: raise ValueError("invalid reservation")
        self.peak_bytes=max(self.peak_bytes,total_bytes)
        if total_bytes>MEMORY_BUDGET: raise ResourceLimit("prospective memory exceeds 4 GiB")
def cache_bytes(): return sum(64+48*len(v) for v in _BASE_CACHE.values())
def spec_parse(spec,m):
    if type(spec) is not dict or set(spec)!={'grid','theta','multipliers'} or type(spec['grid']) is not int or spec['grid']!=80: raise AdmissionError('invalid spec')
    ts,ds=spec['theta'],spec['multipliers']
    if type(ts) is not list or not 2<=len(ts)<=32 or type(ds) is not list or len(ds)>16: raise AdmissionError('invalid spec lengths')
    t=[_rational(x,'theta',m) for x in ts]
    if t!=sorted(set(t)) or any(x<Fraction(1,2) or x>=1 for x in t): raise AdmissionError('invalid theta')
    if any(type(d) is not int or not 2<=d<=64 for d in ds) or ds!=sorted(set(ds)): raise AdmissionError('invalid multipliers')
    return t,ds
_BASE_CACHE={}
def source(n,m):
    # signed mu plus prefix and pi; prospective allocations include sieve temporaries.
    _integer(n,'source horizon',1)
    m.reserve(m.input_bytes+cache_bytes()+m.pending_bytes+(n+1)*24+4096)
    m.charge(n+1)
    mu=array('b',[1])*(n+1); mu[0]=0
    composite=bytearray(n+1)
    pi=array('q',[0])*(n+1); M=array('q',[0])*(n+1)
    for p in range(2,n+1):
        m.charge()
        if not composite[p]:
            for k in range(p,n+1,p):
                m.charge(2); composite[k]=1; mu[k]=-mu[k]
            for k in range(p*p,n+1,p*p): m.charge(); mu[k]=0
    # A separate Eratosthenes primality bitmap avoids inferring prime from mu.
    prime=bytearray(b'\1')*(n+1)
    prime[0]=0
    if n>=1: prime[1]=0
    for p in range(2,n+1):
        m.charge()
        if prime[p]:
            for k in range(p*p,n+1,p): m.charge(); prime[k]=0
    for k in range(1,n+1): m.charge(2); M[k]=M[k-1]+mu[k]; pi[k]=pi[k-1]+prime[k]
    return M,pi
def G(u,M): return M[u//8]-M[u//10]-M[u//4]+M[u//5]
def cut(x,t,m):
    return 0 if x==0 else _integer_root(_power_target(x,t.numerator,t.denominator,0,m),t.denominator,m)
def validate_rows(data,m):
    if type(data) is not dict or set(data)!={'schema','spec','rows'} or data['schema']!='prime-grid-moment-data-v1': raise AdmissionError('invalid data schema')
    ts,ds=spec_parse(data['spec'],m); rows=data['rows']; size=len(ts)-1+len(ds)
    if type(rows) is not list: raise AdmissionError('rows must be list')
    # Account resident JSON and later row-index/failure objects without copying it.
    m.input_bytes=max(m.input_bytes,4096+len(rows)*(1024+160*size))
    m.reserve(m.input_bytes+cache_bytes())
    previous=0
    for row in rows:
        if type(row) is not dict or set(row)!={'u','X','cuts','z','components','moments','counts'}: raise AdmissionError('invalid row schema')
        u=_integer(row['u'],'u',1)
        m.input_bytes+=max(0,u.bit_length()//8-32)*3
        m.reserve(m.input_bytes+cache_bytes())
        if u<=previous: raise AdmissionError('rows must be unique sorted')
        previous=u
        if _integer(row['X'],'X',0)!=u//4: raise AdmissionError('wrong X')
        if type(row['cuts']) is not list or row['cuts']!=[cut(u//4,t,m) for t in ts] or any(type(v) is not int for v in row['cuts']): raise AdmissionError('wrong cuts')
        _integer(row['z'],'z')
        for key in ('components','moments','counts'):
            if type(row[key]) is not list or len(row[key])!=size: raise AdmissionError('wrong vector shape')
            for v in row[key]:
                _integer(v,key,0 if key!='components' else None)
                m.input_bytes += max(0,v.bit_length()//8-32)
                m.reserve(m.input_bytes+cache_bytes())
    return ts,ds,rows
def verify_data(data,meter=None):
    m=meter or Meter(); result={'status':'INVALID','uniform_source_bound_proved':False,'RH_proved':False,'rows_checked':0}
    try:
        ts,ds,rows=validate_rows(data,m)
        M,pi=source(max(1,max((r['u']//4 for r in rows),default=1)),m)
        for r in rows:
            B=[]; Q=[]; N=[]; u=r['u']
            for lo,hi in zip(r['cuts'],r['cuts'][1:]):
                b=q=n=0
                # quotient j, including zero only if a malformed cutoff could exceed u.
                for j in range(u//max(hi,1),u//(lo+1)+1):
                    m.charge()
                    if j==0: continue
                    left=max(lo,u//(j+1)); right=min(hi,u//j)
                    if right>left:
                        count=pi[right]-pi[left]; value=G(j,M)
                        b+=count*value; q+=count*value*value; n+=count
                B.append(b); Q.append(q); N.append(n)
            for d in ds:
                value=G(u//d,M); B.append(value); Q.append(value*value); N.append(1)
            if (r['z'],r['components'],r['moments'],r['counts'])!=(G(u,M),B,Q,N):
                result['first_witness']={'u':u,'expected_z':G(u,M),'expected_components':B,'expected_moments':Q,'expected_counts':N}; raise AdmissionError('source mismatch')
            result['rows_checked']+=1
        result['status']='VERIFIED'
    except (ValueError,TypeError,KeyError,OverflowError) as e: result['reason']=str(e)
    result['ops']=m.ops; result['peak_bytes']=m.peak_bytes; return result
PROGRAM_KEYS={'schema','spec','q','operator','beta','base_u','price_bounds','rho_upper','sqrt_rho_upper','innovation_C','base_upper','bound_B','precision','training_scales','uniform_innovation_proved','uniform_correlation_proved','uniform_source_bound_proved','RH_proved'}
def verify_program(program,data,meter=None,scales=None):
    m=meter or Meter(); out={'status':'INVALID','conditional_induction_verified':False,'universal_direct_correlation_proved':False,'uniform_source_bound_proved':False,'RH_proved':False,'failures':[],'scales_checked':0}
    try:
        p=program
        if type(p) is not dict or set(p)!=PROGRAM_KEYS or p['schema']!='prime-grid-control-program-v1': raise AdmissionError('invalid program schema')
        ts,ds=spec_parse(p['spec'],m); _,_,rows=validate_rows(data,m)
        if p['spec']!=data['spec']: raise AdmissionError('source spec mismatch')
        for flag in ('uniform_innovation_proved','uniform_correlation_proved','uniform_source_bound_proved','RH_proved'):
            if p[flag] is not False: raise AdmissionError('false proof flag required')
        q=_rational(p['q'],'q',m)
        if not 1<=q<2: raise AdmissionError('q outside [1,2)')
        size=len(ts)-1+len(ds); vectors={}
        for key in ('operator','beta','price_bounds'):
            if type(p[key]) is not list or len(p[key])!=size: raise AdmissionError('vector shape')
            vectors[key]=[_rational(v,key,m) for v in p[key]]
        a,beta,prices=(vectors[k] for k in ('operator','beta','price_bounds'))
        if any(v<0 for v in beta+prices): raise AdmissionError('negative beta/price')
        rho,r,C,base,B=(_rational(p[k],k,m) for k in ('rho_upper','sqrt_rho_upper','innovation_C','base_upper','bound_B'))
        if min(rho,r,C,base,B)<0 or r>=1: raise AdmissionError('invalid bounds')
        U=_integer(p['base_u'],'base_u',16); precision=_integer(p['precision'],'precision',8)
        if precision>24: raise AdmissionError('precision >24')
        train=p['training_scales']
        if type(train) is list: m.reserve(m.input_bytes+cache_bytes()+128*len(train))
        if type(train) is not list or not train or any(type(v) is not int or v<=U for v in train) or train!=sorted(set(train)): raise AdmissionError('invalid training scales')
        lowerlog=Fraction(2,3)*( (U//4).bit_length()-1); required=[]
        for lo,hi in zip(ts,ts[1:]):
            z=(hi-lo)/(hi+lo); z2=_mul(z,z,m); term=z; log=Fraction(0)
            for j in range(12): log=_add(log,_divide(_mul(Fraction(2),term,m),Fraction(2*j+1),m),m); term=_mul(term,z2,m)
            log=_add(log,_divide(_mul(Fraction(2),term,m),_mul(Fraction(25),1-z2,m),m),m)
            H=_mul(Fraction(2),_add(log,_divide(Fraction(1),_mul(hi,lowerlog,m),m),m),m)
            required.append(Fraction((H.numerator*(1<<20)+H.denominator-1)//H.denominator,1<<20))
        required += [Fraction(1,d) for d in ds]
        if any(x<y for x,y in zip(prices,required)): raise AdmissionError('price bound too small')
        price_sum=Fraction(0)
        for x,y in zip(beta,prices): price_sum=_add(price_sum,_mul(x,y,m),m)
        if rho<price_sum or rho>_mul(r,r,m) or base>B or C>_mul(_mul(1-r,1-r,m),B,m): raise AdmissionError('invalid contraction/base/innovation budget')
        if U not in _BASE_CACHE:
            base_bytes=64+48*U
            # Cache limit is checked before constructing the tuple or sieve.
            if base_bytes>MEMORY_BUDGET//4: raise ResourceLimit('prospective base cache exceeds 1 GiB')
            if cache_bytes()+base_bytes>MEMORY_BUDGET//4: _BASE_CACHE.clear()
            m.pending_bytes=base_bytes
            m.reserve(m.input_bytes+cache_bytes()+base_bytes+24*(U//4+1)+4096)
            m.charge(5*U); M,_=source(U//4,m); values=tuple(G(u,M) for u in range(1,U+1))
            _BASE_CACHE[U]=values
            m.pending_bytes=0
        for u,z in enumerate(_BASE_CACHE[U],1):
            low,high=power_enclosure(u,q,precision,m)
            if _divide(Fraction(z*z,1),low,m)>base: raise AdmissionError('base enclosure fails at '+str(u))
        out['conditional_induction_verified']=True
        direct=len(ts)-1
        direct_price=Fraction(0)
        valid_direct=all(x==0 for x in a[:direct]) and all(x==0 or y>0 for x,y in zip(a[direct:],beta[direct:]))
        if valid_direct:
            for x,y in zip(a[direct:],beta[direct:]):
                if x: direct_price=_add(direct_price,_divide(_mul(x,x,m),y,m),m)
        out['universal_direct_correlation_proved']=valid_direct and direct_price<=1
        selected=train if scales is None else scales
        if type(selected) is list: m.reserve(m.input_bytes+cache_bytes()+256*len(selected))
        if type(selected) is not list or not selected or selected!=sorted(set(selected)) or any(type(u) is not int or u<=U for u in selected): raise AdmissionError('invalid evaluation scales')
        indexed={row['u']:row for row in rows}
        out['status']='VERIFIED_ON_FINITE_DOMAIN'; worst=None
        for u in selected:
            if u not in indexed: raise AdmissionError('missing evaluation row')
            row=indexed[u]; L=Fraction(0); energy=Fraction(0)
            for x,v,y,w in zip(a,row['components'],beta,row['moments']): L=_add(L,_mul(x,Fraction(v),m),m); energy=_add(energy,_mul(y,Fraction(w),m),m)
            if _mul(L,L,m)>energy: out['failures'].append({'u':u,'lemma':'correlation','left':str(L*L),'right':str(energy),'status':'REFUTED'})
            difference=_add(Fraction(row['z']),-L,m); residual=_mul(difference,difference,m); low,high=power_enclosure(u,q,precision,m); lower=_divide(residual,high,m); upper=_divide(residual,low,m)
            witness={'u':u,'lower':str(lower),'upper':str(upper)}
            if worst is None or upper>Fraction(worst['upper']): worst=witness
            if upper>C: out['failures'].append(dict(witness,lemma='innovation',status='REFUTED' if lower>C else 'UNRESOLVED_ROUNDING'))
            out['scales_checked']+=1
        out['worst_innovation']=worst
        if out['failures']: out['status']='REFUTED' if any(f['status']=='REFUTED' for f in out['failures']) else 'UNRESOLVED_ROUNDING'
    except (ValueError,TypeError,KeyError,OverflowError) as e: out['status']='INVALID'; out['reason']=str(e); out['conditional_induction_verified']=False
    out['ops']=m.ops; out['peak_bytes']=m.peak_bytes; m.pending_bytes=0; return out

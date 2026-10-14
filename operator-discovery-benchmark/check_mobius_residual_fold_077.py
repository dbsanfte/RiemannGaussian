"""Independent scalable finite interval Möbius checker077.

No producer imports or mu queries. Uses frozen independent073 rational helpers;
compiled binding also reuses independent075 cutoff and076 root admission.
"""
from fractions import Fraction
from math import isqrt
from check_mobius_prime_storage_073 import AdmissionError, ResourceLimit, _rational, _add, _mul
MAX_HORIZON=4000000
MAX_PARENT=16000003
MAX_TERMS=100000
MAX_INTERVALS=100000
MEMORY_BUDGET=4*1024**3
class Meter:
    def __init__(self,limit=300000000000):
        self.limit,self.ops,self.peak_bytes=limit,0,0
    def charge(self,n=1):
        self.ops+=n
        if self.ops>self.limit:raise ResourceLimit('work limit exceeded')
    def reserve(self,n):
        self.peak_bytes=max(self.peak_bytes,n)
        if n>MEMORY_BUDGET:raise ResourceLimit('prospective memory exceeds 4 GiB')
def _integer(n,name,lo,hi):
    if type(n) is not int or not lo<=n<=hi:raise AdmissionError(name+' outside integer range')
    return n
def _primes(values,m):
    if type(values) not in (list,tuple) or len(values)>10:raise AdmissionError('at most ten primes')
    seen=set()
    for p in values:
        _integer(p,'prime',2,100000)
        if p in seen:raise AdmissionError('distinct primes required')
        for d in range(2,isqrt(p)+1):
            m.charge()
            if p%d==0:raise AdmissionError('composite prime')
        seen.add(p)
    return tuple(values)
def _poly(raw,m):
    if type(raw) is not dict:raise AdmissionError('invalid polynomial')
    result={}
    for token,value in raw.items():
        if type(token) is not str or not token or len(token)>256:raise AdmissionError('invalid token')
        v=_rational(value,'coefficient',m)
        if not v:raise AdmissionError('omit zero polynomial coefficients')
        result[token]=v
    return result
def _raw_cost(raw):
    # Includes parsed rationals, source text and labels; scales with real inputs.
    cost=512
    for token,value in raw.items():
        cost+=512+4*len(token) if type(token) is str else 512
        if type(value) is str:cost+=4*len(value)
    return cost
def _intervals(raw,m):
    if type(raw) is not list or len(raw)>MAX_INTERVALS:raise AdmissionError('invalid interval list')
    previous=0;terms=0;cost=4096
    for row in raw:
        if type(row) is not dict or set(row)!={'left','right','weight'}:raise AdmissionError('invalid interval schema')
        l=_integer(row['left'],'left',0,MAX_HORIZON);r=_integer(row['right'],'right',1,MAX_HORIZON)
        if l>=r or l<previous:raise AdmissionError('intervals must be sorted disjoint')
        previous=r
        if type(row['weight']) is not dict or not row['weight']:raise AdmissionError('omit zero interval rows')
        terms+=len(row['weight']);cost+=_raw_cost(row['weight'])
        if terms>MAX_TERMS:raise ResourceLimit('sparse interval term gate exceeded')
    m.reserve(cost*4)
    return [(row['left'],row['right'],_poly(row['weight'],m)) for row in raw],cost

def _components(raw,m):
    if type(raw) is not list or len(raw)>MAX_INTERVALS:raise AdmissionError('invalid components')
    terms=0;cost=4096
    for row in raw:
        if type(row) is not dict or set(row)!={'parent','weight'}:raise AdmissionError('invalid component schema')
        _integer(row['parent'],'parent',0,MAX_PARENT)
        if type(row['weight']) is not dict:raise AdmissionError('invalid weight')
        terms+=len(row['weight']);cost+=_raw_cost(row['weight'])
        if terms>MAX_TERMS:raise ResourceLimit('component term gate exceeded')
    m.reserve(cost*8)
    return [(row['parent'],_poly(row['weight'],m)) for row in raw],cost

def _join(target,poly,sign,m):
    for token,value in poly.items():
        m.charge()
        v=_add(target.get(token,Fraction(0)),value if sign==1 else -value,m)
        if v:target[token]=v
        else:target.pop(token,None)

def _function_events(intervals,m):
    events={}
    for l,r,poly in intervals:
        _join(events.setdefault(l,{}),poly,1,m);_join(events.setdefault(r,{}),poly,-1,m)
    return events

def _compare_events(expected,actual,m):
    # On segment (point,nextpoint], event at point is active.
    E={};A={};points=sorted(set(expected)|set(actual))
    for i,point in enumerate(points):
        _join(E,expected.get(point,{}),1,m);_join(A,actual.get(point,{}),1,m)
        if i+1<len(points) and points[i+1]>point and E!=A:
            return {'left':point,'right':points[i+1],'expected':{k:str(v) for k,v in E.items()},'actual':{k:str(v) for k,v in A.items()}}
    if E or A:raise AdmissionError('nonzero coefficient beyond final endpoint')
    return None

def _finish(out,m,error=None):
    if error is not None:
        out.update(status='INVALID',reason=str(error))
        if isinstance(error,ResourceLimit):out['resource_limit']=True
    out.update(ops=m.ops,peak_bytes=m.peak_bytes,finite_identity_only=True,uniform_bound_proved=False,RH_proved=False)
    return out

def verify_stencil(components,intervals):
    m=Meter();out={'status':'INVALID'}
    try:
        rows,ccost=_components(components,m);target,icost=_intervals(intervals,m)
        m.reserve(16*(ccost+icost));expected={}
        for u,poly in rows:
            # Prefix 1<=n<=floor(u/h) is the interval (0,floor(u/h)].
            for h,sign in ((8,1),(10,-1),(4,-1),(5,1)):
                endpoint=u//h
                if endpoint:
                    _join(expected.setdefault(0,{}),poly,sign,m)
                    _join(expected.setdefault(endpoint,{}),poly,-sign,m)
        witness=_compare_events(expected,_function_events(target,m),m)
        if witness:out['first_witness']=witness;raise AdmissionError('stencil function mismatch')
        out.update(status='VERIFIED_IDENTITY',components_checked=len(rows),intervals_checked=len(target),horizon=max((r for l,r,w in target),default=0))
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _finish(out,m,error)
    return _finish(out,m)

def verify_fold(before,after,p,prior_primes=()):
    m=Meter();out={'status':'INVALID'}
    try:
        primes=_primes(prior_primes,m)
        _primes(list(primes)+[p],m)
        old,bcost=_intervals(before,m);new,acost=_intervals(after,m)
        m.reserve(16*(bcost+acost));expected=_function_events(old,m)
        for l,r,poly in old:
            # f(pm) on (floor(l/p),floor(r/p)]; never erase excluded indices.
            left,right=l//p,r//p
            if left<right:
                _join(expected.setdefault(left,{}),poly,-1,m)
                _join(expected.setdefault(right,{}),poly,1,m)
        witness=_compare_events(expected,_function_events(new,m),m)
        if witness:out['first_witness']=witness;raise AdmissionError('fold function mismatch')
        out.update(status='VERIFIED_IDENTITY',before_intervals=len(old),after_intervals=len(new),retained_primes=list(primes)+[p],represented_domain='gcd(m, product(retained_primes))=1')
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _finish(out,m,error)
    return _finish(out,m)

def coprime_count(left,right,primes=(),meter=None):
    m=meter or Meter();_integer(left,'left',0,MAX_HORIZON);_integer(right,'right',left,MAX_HORIZON)
    ps=_primes(primes,m);divisors=[(1,1)]
    for p in ps:
        extra=[]
        for d,sign in divisors:
            m.charge()
            # A pruned divisor and all descendants have zero floor counts.
            if d<=right//p:extra.append((d*p,-sign))
        divisors.extend(extra)
    m.charge(len(divisors))
    return sum(sign*(right//d-left//d) for d,sign in divisors)

def bound_intervals(intervals,token_intervals,primes=()):
    m=Meter();out={'status':'INVALID'}
    try:
        rows,cost=_intervals(intervals,m);ps=_primes(primes,m)
        if type(token_intervals) is not dict or len(token_intervals)>MAX_TERMS:raise AdmissionError('invalid token intervals')
        m.reserve(32*cost+sum(512+sum(4*len(v) for v in pair if type(v) is str) for pair in token_intervals.values() if type(pair) in (list,tuple)))
        ranges={}
        for token,pair in token_intervals.items():
            if type(token) is not str or not token or len(token)>256 or type(pair) not in (list,tuple) or len(pair)!=2:raise AdmissionError('invalid token interval')
            low,high=(_rational(v,'token endpoint',m) for v in pair)
            if low>high:raise AdmissionError('inverted token interval')
            ranges[token]=(low,high)
        # Reuse one divisor expansion over horizon, independently exact counts.
        horizon=max((r for l,r,w in rows),default=0);divisors=[(1,1)]
        for p in ps:
            additions=[]
            for d,sign in divisors:
                m.charge()
                if d<=horizon//p:additions.append((d*p,-sign))
            divisors.extend(additions)
        upper=lower=Fraction(0);counts=[]
        for l,r,poly in rows:
            lo=hi=Fraction(0)
            for token,a in poly.items():
                if token not in ranges:raise AdmissionError('missing token interval')
                x,y=ranges[token]
                if a<0:x,y=y,x
                lo=_add(lo,_mul(a,x,m),m);hi=_add(hi,_mul(a,y,m),m)
            m.charge(len(divisors));count=sum(sign*(r//d-l//d) for d,sign in divisors)
            if count<0:raise AdmissionError('negative coprime count')
            maxabs=max(abs(lo),abs(hi));minabs=Fraction(0) if lo<=0<=hi else min(abs(lo),abs(hi))
            upper=_add(upper,_mul(Fraction(count),maxabs,m),m);lower=_add(lower,_mul(Fraction(count),minabs,m),m)
            counts.append(count)
        out.update(status='VERIFIED_BOUND',bound=str(upper),l1_upper=str(upper),l1_lower=str(lower),counts=counts,primes=list(ps),whole_supplied_domain=True,mu_assumption='|mu(n)|<=1 on retained coprime domain')
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _finish(out,m,error)
    return _finish(out,m)

def verify_compiled(program,row,prime_groups,compiled,precision=20):
    """Bind a residual compiler payload to literal prime children and count tokens.

    Row mu-derived z/B/Q still require separate frozen075 source admission.
    This function supplies prime-group/count and symbolic compiler admission.
    """
    import check_mobius_prime_moment_075 as S
    import check_mobius_count_control_076 as R
    m=Meter();m.input_bytes=0;m.pending_bytes=0;out={'status':'INVALID'}
    try:
        _integer(precision,'precision',8,24)
        if type(program) is not dict or not {'spec','atoms','operator'}<=set(program):raise AdmissionError('invalid source program')
        spec=program['spec'];ts,ds=S.spec_parse(spec,m);split=len(ts)-1;size=split+len(ds)
        if type(row) is not dict:raise AdmissionError('invalid row')
        _integer(row.get('u'),'parent',1,MAX_PARENT)
        S.validate_rows({'schema':'prime-grid-moment-data-v1','spec':spec,'rows':[row]},m)
        atoms=program['atoms'];coefficients=program['operator']
        if type(atoms) is not list or type(coefficients) is not list or len(atoms)!=len(coefficients) or len(atoms)>MAX_TERMS:raise AdmissionError('atom/operator shape')
        atom_cost=4096
        for atom,coefficient in zip(atoms,coefficients):
            atom_cost+=2048+(4*len(coefficient) if type(coefficient) is str else 0)+(4*len(atom.get('gamma','')) if type(atom) is dict and type(atom.get('gamma')) is str else 0)
        m.reserve(m.input_bytes+8*atom_cost+80*1024**2)
        m.input_bytes+=8*atom_cost
        parsed=[];previous=None
        for atom,coefficient in zip(atoms,coefficients):
            if type(atom) is not dict or set(atom)!={'column','gamma'}:raise AdmissionError('invalid atom')
            column=_integer(atom['column'],'column',0,size-1);gamma=_rational(atom['gamma'],'gamma',m)
            if gamma<0:raise AdmissionError('negative gamma')
            key=(column,gamma)
            if previous is not None and key<=previous:raise AdmissionError('atoms must be sorted unique')
            previous=key;parsed.append((column,gamma,_rational(coefficient,'operator',m)))
        if type(prime_groups) is not list or len(prime_groups)!=split:raise AdmissionError('prime groups shape')
        u=row['u'];cuts=row['cuts'];horizon=cuts[-1]
        m.reserve(m.input_bytes+128*len(atoms)+64*(horizon+1)+80*1024**2)
        # Own Eratosthenes sieve, no mu accesses or producer groups.
        m.charge(horizon+1);prime=bytearray(b'\1')*(horizon+1);prime[0]=0
        if horizon>=1:prime[1]=0
        for p in range(2,isqrt(horizon)+1):
            if prime[p]:
                for n in range(p*p,horizon+1,p):m.charge();prime[n]=0
        expected_groups=[];expected_counts=[]
        for lo,hi in zip(cuts,cuts[1:]):
            group={}
            for p in range(lo+1,hi+1):
                m.charge()
                if prime[p]:child=u//p;group[child]=group.get(child,0)+1
            expected_groups.append(group);expected_counts.append(sum(group.values()))
        for group in prime_groups:
            if type(group) is not dict or len(group)>MAX_TERMS:raise AdmissionError('invalid prime group')
            for child,count in group.items():_integer(child,'child',1,u//2);_integer(count,'multiplicity',1,horizon)
        if prime_groups!=expected_groups:raise AdmissionError('prime child groups mismatch')
        if row['counts']!=expected_counts+[1]*len(ds):raise AdmissionError('source counts mismatch')
        weights=[{} for _ in range(size)];tokens={'1':['1','1']};definitions={'1':{'kind':'constant','value':'1'}}
        for column,gamma,a in parsed:
            count=row['counts'][column]
            token='1' if count<=1 or gamma==0 else 'count:'+str(count)+'^(-'+str(gamma)+')'
            if token not in tokens:
                lower,upper=R.count_enclosure(count,gamma,precision,m)
                token_cost=4096+8*len(token)+4*(lower.numerator.bit_length()+lower.denominator.bit_length()+upper.numerator.bit_length()+upper.denominator.bit_length())//3
                m.input_bytes+=token_cost
                m.reserve(m.input_bytes+80*1024**2+64*(horizon+1))
                from check_mobius_prime_storage_073 import _divide
                tokens[token]=[str(_divide(Fraction(1),upper,m)),str(_divide(Fraction(1),lower,m))]
                definitions[token]={'kind':'inverse_rational_count_power','count':count,'gamma':str(gamma)}
            _join(weights[column],{token:a},-1,m)
        planned_components=1+sum(len(group) for i,group in enumerate(expected_groups) if weights[i])+sum(bool(weights[i]) for i in range(split,size))
        planned_terms=1+sum(len(weights[i])*len(group) for i,group in enumerate(expected_groups))+sum(len(weights[i]) for i in range(split,size))
        if planned_components>MAX_INTERVALS or planned_terms>MAX_TERMS:raise ResourceLimit('prospective compiled expansion exceeds term/component gate')
        column_cost=[512+sum(2048+4*len(t)+2*(a.numerator.bit_length()+a.denominator.bit_length()) for t,a in weight.items()) for weight in weights]
        compiled_cost=4096+sum(column_cost[i]*len(group) for i,group in enumerate(expected_groups) if weights[i])+sum(column_cost[i] for i in range(split,size) if weights[i])
        m.reserve(m.input_bytes+80*1024**2+64*(horizon+1)+8*compiled_cost)
        expected_components=[{'parent':u,'weight':{'1':'1'}}]
        for i,group in enumerate(expected_groups):
            if weights[i]:
                for child,count in sorted(group.items()):expected_components.append({'parent':child,'weight':{t:str(_mul(Fraction(count),a,m)) for t,a in weights[i].items()}})
        for i,d in enumerate(ds,split):
            if weights[i]:expected_components.append({'parent':u//d,'weight':{t:str(a) for t,a in weights[i].items()}})
        if len(expected_components)>MAX_INTERVALS:raise ResourceLimit('compiled component gate exceeded')
        if type(compiled) is not dict or not {'components','token_intervals','token_definitions'}<=set(compiled):raise AdmissionError('invalid compiled payload')
        validated_components,actual_cost=_components(compiled['components'],m)
        m.reserve(m.input_bytes+80*1024**2+64*(horizon+1)+8*(compiled_cost+actual_cost))
        for flag in ('source_admission_supplied','uniform_bound_proved','RH_proved'):
            if flag in compiled and compiled[flag] is not False:raise AdmissionError('false compiler flags required')
        if type(compiled['token_definitions']) is not dict or type(compiled['token_intervals']) is not dict:raise AdmissionError('invalid compiled tokens')
        for token,definition in compiled['token_definitions'].items():
            if type(definition) is not dict:raise AdmissionError('invalid token definition')
            if definition.get('kind')=='inverse_rational_count_power':
                _integer(definition.get('count'),'definition count',2,MAX_HORIZON);_rational(definition.get('gamma'),'definition gamma',m)
        if compiled['components']!=expected_components:raise AdmissionError('compiled components mismatch')
        if compiled['token_definitions']!=definitions or compiled['token_intervals']!=tokens:raise AdmissionError('compiled count-token definitions/enclosures mismatch')
        out.update(status='VERIFIED_IDENTITY',prime_groups_checked=split,counts_checked=size,components_checked=len(expected_components),token_definitions_checked=len(definitions),source_data_admission_still_required=True,prime_group_admission_supplied=True)
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _finish(out,m,error)
    return _finish(out,m)

def verify_bulk_obstruction(kernel,child_min_divisor,primes,certificate):
    """Uniform obstruction to a fixed-prime coefficient-l1 method only.

    No claim that the signed arithmetic residual or source bound is refuted.
    """
    from check_mobius_prime_storage_073 import _divide
    m=Meter();out={'status':'INVALID','arithmetic_residual_refuted':False,'uniform_l1_power_bound_obstructed':False,'uniform_source_bound_proved':False}
    try:
        child=_integer(child_min_divisor,'child minimum divisor',2,1<<4096);ps=_primes(primes,m)
        if type(kernel) is not list or not kernel or len(kernel)>MAX_TERMS:raise AdmissionError('invalid kernel')
        m.reserve(4096+sum(1024+4*len(row.get('weight','')) for row in kernel if type(row) is dict))
        rows=[]
        for row in kernel:
            if type(row) is not dict or set(row)!={'divisor','weight'}:raise AdmissionError('invalid kernel schema')
            divisor=_integer(row['divisor'],'kernel divisor',1,1<<4096);weight=_rational(row['weight'],'kernel weight',m)
            rows.append((Fraction(1,divisor),weight))
        keys={'lower','upper','coefficient','delta','A','E','threshold_u','q'}
        if type(certificate) is not dict or set(certificate)!=keys:raise AdmissionError('invalid obstruction certificate schema')
        lo,hi,c,delta,A,E,q=(_rational(certificate[k],k,m) for k in ('lower','upper','coefficient','delta','A','E','q'))
        if not 1<=q<2:raise AdmissionError('q outside [1,2)')
        horizon=max(point for point,weight in rows)
        if not 0<=lo<hi<=horizon or lo<horizon/child or lo<horizon/2:raise AdmissionError('band is not beyond all child/fold horizons')
        if any(lo<point<hi for point,weight in rows):raise AdmissionError('kernel breakpoint inside band')
        actual=Fraction(0)
        for point,weight in rows:
            if hi<=point:actual=_add(actual,weight,m)
        if actual!=c or not c:raise AdmissionError('nonzero band coefficient mismatch')
        expected_delta=Fraction(1)
        for p in ps:expected_delta=_mul(expected_delta,Fraction(p-1,p),m)
        expected_A=_mul(_mul(abs(c),expected_delta,m),_add(hi,-lo,m),m);expected_E=_mul(abs(c),Fraction(1<<len(ps)),m)
        if delta!=expected_delta or A!=expected_A or E!=expected_E or A<=0:raise AdmissionError('obstruction constants mismatch')
        threshold=_divide(_mul(Fraction(2),E,m),A,m);threshold_u=(threshold.numerator+threshold.denominator-1)//threshold.denominator
        if type(certificate['threshold_u']) is not int or certificate['threshold_u']!=threshold_u:raise AdmissionError('threshold mismatch')
        out.update(status='VERIFIED_UNIFORM_COEFFICIENT_OBSTRUCTION',uniform_l1_power_bound_obstructed=True,horizon=str(horizon),lower=str(lo),upper=str(hi),coefficient=str(c),A=str(A),E=str(E),threshold_u=threshold_u,q=str(q),l1_lower_for_all_integer_u='A*u-E',l1_lower_above_threshold='A*u/2',scope='fixed finite prime schedule coefficient l1 method; signed arithmetic residual unrefuted')
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _finish(out,m,error)
    # This result is a generic uniform negative-method theorem, not finite identity.
    out=_finish(out,m);out['finite_identity_only']=False;return out

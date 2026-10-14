"""Independent source replay for exact moving-profile prime transitions.

Reuses frozen045 spec and beta admission. Rounded atoms are reconstructed by
integer root inequalities; ordinary mu and every signed transition column are
independent of the new producer. This is source algebra, not a norm theorem.
"""
from fractions import Fraction as Q
import math
import time
import check_floor_residual_drift_045 as DRIFT

ROUNDING={'kind':'dyadic_power_floor','bits_multiplier':4,'scale':'ceil_log2_N',
          'drift':'round_each_exponential_before_signed_sum',
          'product':'multiply_rounded_children_exactly'}
MAX_INDEX=5000
MAX_SUPPORT=4096
MAX_INPUT_BITS=4096
MAX_INTERMEDIATE_BITS=16384
MAX_POWER_BITS=400000
MAX_MEMORY=4*1024**3


class Meter:
    def __init__(self,cap=50000000,seconds=180):
        if type(cap) is not int or cap<0:raise ValueError('nonnegative work cap')
        if type(seconds) not in (int,float) or not math.isfinite(seconds) or seconds<=0:
            raise ValueError('positive finite deadline')
        self.cap=cap;self.operations=0;self.deadline=time.monotonic()+seconds
    def charge(self,n=1):
        if type(n) is not int or n<0 or n>self.cap-self.operations:raise OverflowError('transition source work cap')
        self.operations+=n
        if time.monotonic()>self.deadline:raise TimeoutError('transition source deadline')


def _meter(m):return Meter() if m is None else m

def _same(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return set(a)==set(b) and all(_same(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(_same(x,y) for x,y in zip(a,b))
    return a==b

def _expect(a,b):
    if not _same(a,b):raise ValueError('source, signed identity or scope mismatch')

def _fields(obj,keys):
    if type(obj) is not dict or set(obj)!=set(keys):raise ValueError('exact source certificate fields')

def _bounded(value,m,bits=MAX_INTERMEDIATE_BITS):
    size=max(abs(value.numerator).bit_length(),value.denominator.bit_length())
    if size>bits:raise OverflowError('transition rational capacity')
    m.charge(1+size);return value

def _rat(text,m):
    return DRIFT.rational(text,m)

def _add(a,b,m):return _bounded(a+b,m)
def _mul(a,b,m):return _bounded(a*b,m)

def _factor(n,m):
    factors=[];d=2
    while d*d<=n:
        e=0
        while n%d==0:n//=d;e+=1;m.charge(8)
        if e:factors.append((d,e))
        d+=1;m.charge(8)
    if n>1:factors.append((n,1))
    return factors

def _request(request,m):
    _fields(request,('source_recipe','prime','parent_support','d','rounding'))
    recipe=request['source_recipe'];_fields(recipe,('id','base','auxiliary'))
    if type(recipe['id']) is not str or not 1<=len(recipe['id'])<=250 or recipe['auxiliary'] is not None:
        raise ValueError('bare actual moving-mixture source recipe')
    a,theta,terms=DRIFT.parse_spec(recipe['base'],m)
    _expect(request['rounding'],ROUNDING)
    p,N=request['prime'],request['parent_support']
    if type(p) is not int or type(N) is not int or not 2<=p<=MAX_INDEX or not 2<=N<=MAX_SUPPORT or p*N>MAX_INDEX:
        raise ValueError('actual prime, parent>=2 and child index<=5000')
    if _factor(p,m)!=[(p,1)]:raise ValueError('prime dilation requires an actual prime')
    d=_rat(request['d'],m)
    # Powers are temporary, not stored for every atom. The cache stores only
    # small rounded rationals. Use the maximum one-power working reserve.
    estimate=(N+p*N+1)*(4096+32*((MAX_INTERMEDIATE_BITS+7)//8))+8*(N+p*N+1)*1024+16*((MAX_POWER_BITS+7)//8)
    if estimate>MAX_MEMORY:raise OverflowError('prospective transition source memory cap')
    return recipe['base'],p,N,d,terms


def _power(n,k,m):
    if type(n) is not int or n<0 or type(k) is not int or k<0:raise ValueError('integer powered comparison')
    estimated=max(1,n.bit_length())*k
    if estimated>MAX_POWER_BITS:raise OverflowError('exact root power capacity')
    # Charges a conservative bit work proxy, independent of producer counts.
    m.charge(max(1,estimated)*max(1,k.bit_length()));return n**k


def _integer_root(number,degree,upper,m):
    """Floor root with exact final inequalities and bounded Newton/binary work."""
    if number==0:return 0
    if degree==1:return number
    if degree>64:
        lo=0;hi=upper+1
        while hi-lo>1:
            mid=(lo+hi)//2
            if _power(mid,degree,m)<=number:lo=mid
            else:hi=mid
            m.charge(5)
        root=lo
    else:
        root=1<<((number.bit_length()+degree-1)//degree)
        root=min(root,upper)
        while True:
            divisor=_power(root,degree-1,m)
            nextroot=((degree-1)*root+number//divisor)//degree
            m.charge(5)
            if nextroot>=root:break
            root=nextroot
    if not _power(root,degree,m)<=number<_power(root+1,degree,m):
        raise ArithmeticError('integer root maximality')
    return root


def _atom(n,exponent,bits,m):
    if type(n) is not int or not 1<=n<=MAX_INDEX or type(exponent) is not Q or exponent<=0 or type(bits) is not int or not 1<=bits<=16384:
        raise ValueError('exact atom domain')
    if n==1:return Q(1)
    u,v=exponent.numerator,exponent.denominator
    estimate=bits*v+u*n.bit_length()+4
    if estimate>MAX_POWER_BITS:raise OverflowError('rounded atom power capacity')
    # A strict elementary lower bound can license an exactly zero atom
    # without allocating a needlessly large powered integer. Equality is
    # deliberately excluded: at that boundary the rounded atom may be2^-p.
    if u*(n.bit_length()-1)>bits*v:
        m.charge(1+u.bit_length()+v.bit_length()+n.bit_length());return Q(0)
    factor=_power(n,u,m);target=1<<(bits*v);m.charge(bits*v+1)
    quotient=target//factor;root=_integer_root(quotient,v,1<<bits,m)
    # Verify directly against the original rational power rather than merely
    # trusting an integer-root implementation.
    if not _power(root,v,m)*factor<=target<_power(root+1,v,m)*factor:
        raise ArithmeticError('complete rounded rational exponent inequality')
    return Q(root,1<<bits)


def _profile(spec,N,terms,cache,m):
    beta=DRIFT.beta(spec['a'],spec['theta'],N,m);_bounded(beta,m,MAX_INPUT_BITS)
    bits=4*(N-1).bit_length();values=[Q(0)];computed=hits=0
    for n in range(1,N+1):
        value=Q(0)
        for rate,weight in terms:
            exponent=_mul(rate,beta,m);_bounded(exponent,m,MAX_INPUT_BITS)
            key=(n,bits,exponent.numerator,exponent.denominator)
            if key not in cache:cache[key]=_atom(n,exponent,bits,m);computed+=1
            else:hits+=1;m.charge(1)
            value=_add(value,_mul(weight,cache[key],m),m)
        _bounded(value,m,MAX_INPUT_BITS);values.append(value)
    if values[1]!=1:raise ArithmeticError('actual rounded unit')
    return values,beta,bits,computed,hits


# C*chi - sum c_n*f_n - sum d_q*I_q, native signed convention.
def _vector(C=0,c=None,d=None):return Q(C),{} if c is None else {n:v for n,v in c.items() if v},{} if d is None else {n:v for n,v in d.items() if v}

def _scale(v,a,m):return _vector(_mul(v[0],a,m),{n:_mul(c,a,m) for n,c in v[1].items()}, {n:_mul(d,a,m) for n,d in v[2].items()})

def _plus(v,w,m):
    out=[]
    for left,right in zip(v[1:],w[1:]):
        current=left.copy()
        for n,c in right.items():current[n]=_add(current.get(n,Q(0)),c,m)
        out.append(current)
    return _vector(_add(v[0],w[0],m),*out)

def _dilate(v,p,m):
    c={};steps={p:-v[0]} if v[0] else {}
    for n,value in v[1].items():
        c[p*n]=_add(c.get(p*n,Q(0)),value,m)
        c[p]=_add(c.get(p,Q(0)),-value/n,m)
    for q,value in v[2].items():steps[p*q]=_add(steps.get(p*q,Q(0)),value,m)
    return _vector(0,c,steps)


def _decode(program,m):
    _fields(program,('id','constant','coefficients','steps'))
    if type(program['id']) is not str or not 1<=len(program['id'])<=256:raise ValueError('program identifier')
    if type(program['coefficients']) is not list or type(program['steps']) is not list or len(program['coefficients'])+len(program['steps'])>MAX_SUPPORT:
        raise ValueError('transition program support capacity')
    vectors=[]
    for key,index in (('coefficients','n'),('steps','q')):
        rows={};previous=1
        for row in program[key]:
            _fields(row,(index,'value'));n=row[index];value=_rat(row['value'],m)
            if type(n) is not int or not previous<n<=MAX_INDEX or not value:raise ValueError('sorted nonzero signed column')
            rows[n]=value;previous=n
        vectors.append(rows)
    return _vector(_rat(program['constant'],m),*vectors)


def _bind(program,expected,m):
    if _decode(program,m)!=expected:raise ValueError('complete source-bound transition vector mismatch')


def verify_state(request,certificate,meter=None):
    """Verify actual supplied profiles and the complete h/A/v source vectors."""
    m=_meter(meter);spec,p,N,d,terms=_request(request,m)
    _fields(certificate,('schema','request','parent_values','child_values','programs',
        'identity_only','uniform_bound_proved','rh_claim'))
    for key,value in {'schema':'floor-prime-transition-state-v1','request':request,
        'identity_only':True,'uniform_bound_proved':False,'rh_claim':False}.items():_expect(certificate[key],value)
    _fields(certificate['programs'],('h','A','v'))
    arrays=[]
    for key,length in (('parent_values',N),('child_values',p*N)):
        rows=certificate[key]
        if type(rows) is not list or len(rows)!=length:raise ValueError('every actual source profile index required')
        arrays.append([Q(0)]+[_rat(s,m) for s in rows])
    cache={}
    U,parent_beta,parent_bits,parent_computed,parent_hits=_profile(spec,N,terms,cache,m)
    V,child_beta,child_bits,child_computed,child_hits=_profile(spec,p*N,terms,cache,m)
    if arrays[0]!=U or arrays[1]!=V:raise ValueError('actual separately rounded source profile mismatch')
    mu=[0]
    for n in range(1,p*N+1):
        factors=_factor(n,m);mu.append(0 if any(e>1 for _,e in factors) else (-1)**len(factors))
    parent=_vector(1,{n:-mu[n]*U[n] for n in range(2,N+1)})
    child=_vector(1,{n:-mu[n]*V[n] for n in range(2,p*N+1)})
    h=_plus(child,_dilate(parent,p,m),m)
    inner=_vector(_add(Q(1),-V[p],m),
        {n:-mu[n]*_add(U[n],-V[p*n],m) for n in range(2,N+1)})
    auxiliary=_dilate(inner,p,m)
    v=_plus(h,_scale(auxiliary,-d,m),m)
    # Independent matched identity is a useful safeguard against accidentally
    # dropping the unit/indicator or the prime-square parent contributions.
    direct=_vector(V[p],{n:-mu[n]*V[p*n] for n in range(2,N+1)})
    matched=_plus(child,_dilate(direct,p,m),m)
    if _plus(matched,auxiliary,m)!=h:raise ArithmeticError('division-free full original recovery')
    prefix='prime_transition_'+str(p)+'_'+str(N)
    for name,expected in (('h',h),('A',auxiliary),('v',v)):
        program=certificate['programs'][name]
        _bind(program,expected,m);_expect(program['id'],prefix+'_'+name)
    return {'verified':True,'actual_source_profiles_verified':True,
        'ordinary_mu_independently_factored':True,'separate_atom_rounding_verified':True,
        'all_source_indices_retained':True,'division_free_matched_recovery_verified':True,
        'identity_only':True,'uniform_bound_proved':False,'rh_claim':False,
        'parent_support':N,'child_support':p*N,'prime':p,'d':request['d'],
        'parent_beta':str(parent_beta),'child_beta':str(child_beta),
        'parent_precision_bits':parent_bits,'child_precision_bits':child_bits,
        'frozen_primitives_reused':'check_floor_residual_drift_045.parse_spec/beta/rational',
        'counters':{'profile_values_verified':N+p*N,'rounded_atom_occurrences':(N+p*N)*len(terms),
            'distinct_atoms_reconstructed':parent_computed+child_computed,
            'atom_cache_hits':parent_hits+child_hits,'mu_indices_factored':p*N},
        'limits':{'max_index':MAX_INDEX,'max_support':MAX_SUPPORT,'input_bits':MAX_INPUT_BITS,
            'intermediate_bits':MAX_INTERMEDIATE_BITS,'integer_power_bits':MAX_POWER_BITS,
            'prospective_memory_bytes':MAX_MEMORY}}

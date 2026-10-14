"""Infer exact profile conservation and use it for positive-copy matching.

The generator sees exact quarter-grid masks and a generic divisibility basis.
It is not supplied a winning profile combination or a numerical cost table.
"""
from collections import defaultdict,deque
from fractions import Fraction as Q
from itertools import product
from math import gcd,fsum,isfinite,prod

from prime_transfer_algebra_058 import Meter,_rref
from mobius_transport_search_059 import _q,_tokens

PROFILES=('P','Q','D','S')
MAX_PERIOD=4096
MAX_WEIGHT=16
MAX_COPIES=1_000_000


def profile_vector(n,p,q):
    def W(r):return n//r-3*(n//(2*r))+2*(n//(4*r))
    a,b=W(p),W(q);row=[0]*4
    if not a and not b:return row
    if not b:index,sign=0,a
    elif not a:index,sign=1,-b
    elif a==b:index,sign=2,a
    else:index,sign=3,a
    row[index]=sign
    return row


def signature(parameters,meter=None):
    meter=meter or Meter();p,q=parameters['p'],parameters['q']
    if type(p) is not int or type(q) is not int or not 2<=p<q:raise ValueError('ordered positive source scales')
    period=4*p*q
    if period>MAX_PERIOD:raise OverflowError('prospective exact profile-period capacity')
    divisors=[b for b in range(1,period+1) if period%b==0]
    meter.reserve(1024+period*4096);meter.charge(8*period)
    values=[profile_vector(n,p,q) for n in range(period+1)]
    if values[0]!=[0]*4 or values[-1]!=values[0]:raise ArithmeticError('zero origin and full period')
    jumps=[[values[n][i]-values[n-1][i] for i in range(4)] for n in range(1,period+1)]
    # Divisibility coefficients are forced by the rows at each divisor.
    coefficients={}
    for b in divisors:
        coefficients[b]=[jumps[b-1][i]-sum(coefficients[d][i] for d in divisors if d<b and b%d==0)
                         for i in range(4)]
        meter.charge(8*len(divisors))
    residual=[]
    for n in range(1,period+1):
        residual.append([jumps[n-1][i]-sum(coefficients[b][i] for b in divisors if n%b==0) for i in range(4)])
        meter.charge(8*len(divisors))
    rows=[(n,(),tuple((i,c) for i,c in enumerate(row) if c)) for n,row in enumerate(residual)]
    pivots,rref=_rref(rows,4,meter,period*4096)
    basis=[]
    for free in range(4):
        if free in pivots:continue
        vector=[Q(0)]*4;vector[free]=Q(1)
        for pivot,row in zip(pivots,rref):vector[pivot]=-row.get(free,Q(0))
        if any(sum(c*x for c,x in zip(row,vector)) for row in residual):raise ArithmeticError('exact nullspace replay')
        basis.append([str(v) for v in vector]);meter.charge(8*period)
    return {'period':period,'divisors':divisors,'jumps':jumps,'divisor_coefficients':coefficients,
            'residual_rows':residual,'rank':len(pivots),'nullity':len(basis),'basis':basis,
            'rref':[{str(k):str(v) for k,v in row.items()} for row in rref]}


def identity(parameters,vector,compiled,meter=None):
    meter=meter or Meter()
    if type(vector) is not list or len(vector)!=4:raise ValueError('four canonical profile coefficients')
    weights=[_q(v) for v in vector]
    if not any(weights):raise ValueError('nonzero profile expression')
    for row in compiled['residual_rows']:
        meter.charge(16)
        if sum(c*w for c,w in zip(row,weights)):return None
    terms=[]
    for b in compiled['divisors']:
        c=sum(v*w for v,w in zip(compiled['divisor_coefficients'][b],weights))
        if c:terms.append({'d':b,'c':str(c)})
        meter.charge(16)
    return {'schema':'mobius-profile-floor-identity-v1','parameters':parameters,
            'period':compiled['period'],'profile_coefficients':vector,'floor_coefficients':terms}


def copy_certificate(ident):
    weights=[int(_q(s)) for s in ident['profile_coefficients']]
    if any(str(w)!=s or not 1<=w<=MAX_WEIGHT for w,s in zip(weights,ident['profile_coefficients'])):
        raise ValueError('strict positive bounded integer copy masses')
    params=ident['parameters'];k=len(params['primes']);alpha=_q(params['alpha'])
    if not 0<alpha<1:raise ValueError('fractional kernel order')
    magnitude=Q(6*prod(params['primes']))/(k-alpha)
    coefficient=magnitude*sum(abs(_q(t['c'])) for t in ident['floor_coefficients'])/min(weights)
    return {'schema':'mobius-copy-leftover-bound-v1','identity':ident,'weights':weights,
            'magnitude_constant':str(magnitude),'coefficient':str(coefficient),'log_degree':k}


def discover(parameters,max_weight=6,meter=None):
    meter=meter or Meter()
    if type(max_weight) is not int or not 1<=max_weight<=MAX_WEIGHT:raise ValueError('finite positive mass budget')
    compiled=signature(parameters,meter)
    basis=[identity(parameters,v,compiled,meter) for v in compiled['basis']]
    candidates=[];examined=0;primitive=0
    for weights in product(range(1,max_weight+1),repeat=4):
        examined+=1;meter.charge(8)
        if gcd(gcd(weights[0],weights[1]),gcd(weights[2],weights[3]))!=1:continue
        primitive+=1
        ident=identity(parameters,list(map(str,weights)),compiled,meter)
        if ident is not None:candidates.append(copy_certificate(ident))
    candidates.sort(key=lambda c:(c['log_degree'],Q(c['coefficient']),sum(c['weights']),c['weights']))
    return {'schema':'mobius-mass-conservation-discovery-v1','parameters':parameters,
            'signature':compiled,'basis_identities':basis,'positive_copy_certificates':candidates,
            'weight_vectors_examined':examined,'primitive_vectors_examined':primitive,
            'weight_budget':max_weight,'source_values_used':False,'uniform_full_source_bound_proved':False}


def copy_plan(tokens,weights,mode='profile_then_global',meter=None):
    meter=meter or Meter();by_d=_tokens(tokens)
    if type(weights) is not list or len(weights)!=4 or any(type(w) is not int or not 1<=w<=MAX_WEIGHT for w in weights):
        raise ValueError('four positive integer copy counts')
    if mode not in ('global','profile_then_global'):raise ValueError('declared copy matching semantics')
    total=sum(weights[PROFILES.index(t['profile'])] for t in tokens)
    if total>MAX_COPIES:raise MemoryError('prospective copy table capacity')
    meter.reserve(1024+total*1024);copies={}
    for d in sorted(by_d):
        t=by_d[d];w=weights[PROFILES.index(t['profile'])]
        if not isfinite(t['magnitude']) or t['magnitude']<0:raise ValueError('nonnegative finite screening magnitude')
        for index in range(w):
            copies[(d,index)]={'profile':t['profile'],'sign':t['sign'],'magnitude':t['magnitude']/w}
        meter.charge(8*w)
    available=set(copies);pairs=[]
    for group in (('profile','all') if mode=='profile_then_global' else ('all',)):
        groups=defaultdict(list)
        for key in sorted(available):groups[copies[key]['profile'] if group=='profile' else 'all'].append(key)
        for name in sorted(groups):
            queue=deque()
            for key in groups[name]:
                if queue and copies[queue[-1]]['sign']!=copies[key]['sign']:
                    other=queue.pop();pairs.append([other,key]);available.remove(other);available.remove(key)
                else:queue.append(key)
                meter.charge(12)
    weighted_count=sum(t['sign'] for t in copies.values())
    if len(available)!=abs(weighted_count):raise ArithmeticError('complete global residual count')
    left=sorted(available)
    return {'pairs':[[list(a),list(b)] for a,b in pairs],'unmatched':[list(a) for a in left],
            'copy_count':total,'signed_copy_count':weighted_count,
            'pair_cost_float':fsum(abs(copies[a]['magnitude']-copies[b]['magnitude']) for a,b in pairs),
            'leftover_cost_float':fsum(copies[a]['magnitude'] for a in left),
            'descriptive_float_only':True,'uniform_pair_cost_bound_proved':False}


def smooth_count(primes,X,meter=None):
    meter=meter or Meter();X=Q(X)
    def count(index,remaining):
        if remaining<1:return 0
        if index==len(primes):return 1
        result=0
        while remaining>=1:
            result+=count(index+1,remaining);remaining/=primes[index];meter.charge(8)
        return result
    return count(0,X)


def exact_smooth_mass(ident,N,meter=None):
    meter=meter or Meter()
    return sum(_q(t['c'])*smooth_count(ident['parameters']['primes'],Q(4*N,t['d']),meter)
               for t in ident['floor_coefficients'])

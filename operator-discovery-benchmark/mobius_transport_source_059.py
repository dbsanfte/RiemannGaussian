"""FLOAT screening of the joined ordinary-mu prime transport source.

All source weights and the empty-band gate are exact. Quadrature values and
positive magnitudes are numerical screening only, without rigorous intervals.
"""
from fractions import Fraction as Q
import math
import time
import numpy as np

MAX_N=262144
MAX_PRIME=1_000_000
MAX_PRIMES=8
MAX_PARAMETER_BITS=4096
MAX_POWER_BITS=400000
MAX_DEGREE=256
BATCH_SIZE=2048
MAX_CACHE_BYTES=512*1024**2
MAX_WORKING_BYTES=4*1024**3
PROFILES=('P','Q','D','S')


class Meter:
    def __init__(self,cap=50_000_000_000,seconds=7200):
        if type(cap) is not int or cap<0:raise ValueError('nonnegative work cap')
        if type(seconds) not in (int,float) or not math.isfinite(seconds) or seconds<=0:
            raise ValueError('positive finite deadline')
        self.cap,self.operations,self.deadline=cap,0,time.monotonic()+seconds
        self.peak_bytes_estimate=0
        self.primitives={k:0 for k in ('prime_trial_divisions','exact_power_bits','mu_sieve_entries',
            'integer_weight_entries','coprime_mask_entries','log_atoms','quadrature_nodes',
            'quadrature_matrix_entries','tokens','cache_hits')}
    def charge(self,amount=1):
        if type(amount) is not int or amount<0 or amount>self.cap-self.operations:
            raise OverflowError('transport work cap')
        self.operations+=amount
        if time.monotonic()>self.deadline:raise TimeoutError('transport deadline')
    def reserve(self,amount):
        if type(amount) is not int or not 0<=amount<=MAX_WORKING_BYTES:
            raise MemoryError('transport prospective memory cap')
        self.peak_bytes_estimate=max(self.peak_bytes_estimate,amount);self.charge()
    def counts(self):
        return {'operations':self.operations,'peak_bytes_estimate':self.peak_bytes_estimate,
                'total_primitive_counts':dict(self.primitives)}


def _meter(meter):return Meter() if meter is None else meter

def _q(text):
    if type(text) is not str or not 1<=len(text)<=2500:raise ValueError('bounded canonical rational')
    try:value=Q(text)
    except (ValueError,ZeroDivisionError):raise ValueError('canonical rational') from None
    if str(value)!=text:raise ValueError('canonical rational')
    if max(abs(value.numerator).bit_length(),value.denominator.bit_length())>MAX_PARAMETER_BITS:
        raise OverflowError('transport rational bit cap')
    return value

def _prime(p,meter):
    if type(p) is not int or not 2<=p<=MAX_PRIME:raise ValueError('actual bounded prime')
    for d in range(2,math.isqrt(p)+1):
        meter.primitives['prime_trial_divisions']+=1;meter.charge(4)
        if p%d==0:raise ValueError('actual prime required')
    return p

def _request(request,meter):
    if type(request) is not dict or set(request)!={'N','alpha','gamma','tau','primes','p','q'}:
        raise ValueError('exact transport request schema')
    N=request['N'];alpha,gamma,tau=(_q(request[k]) for k in ('alpha','gamma','tau'))
    if type(N) is not int or not 2<=N<=MAX_N:raise ValueError('integer scale resource domain')
    if not 0<alpha<1 or gamma<=0 or not 0<tau<1:raise ValueError('transport alpha/gamma/tau domain')
    primes=request['primes']
    if type(primes) is not list or not 2<=len(primes)<=MAX_PRIMES:
        raise ValueError('bounded sorted actual-prime list containing p,q')
    checked=tuple(_prime(prime,meter) for prime in primes)
    if sorted(set(checked))!=primes:raise ValueError('canonical distinct prime list')
    p,q=request['p'],request['q']
    if type(p) is not int or type(q) is not int or p>=q or p not in checked or q not in checked:
        raise ValueError('distinct actual p<q in prime list')
    meter.charge(32+sum(abs(v.numerator).bit_length()+v.denominator.bit_length() for v in (alpha,gamma,tau)))
    return N,alpha,gamma,tau,checked,p,q


def _band_empty(N,gamma,tau,meter):
    u,v=gamma.numerator,gamma.denominator
    estimate=max(u*N.bit_length()+v*tau.numerator.bit_length(),v*tau.denominator.bit_length())
    if estimate>MAX_POWER_BITS:raise OverflowError('empty-band exact power bit cap')
    meter.primitives['exact_power_bits']+=estimate;meter.charge(estimate+u.bit_length()+v.bit_length())
    return pow(N,u)*pow(tau.numerator,v)<=pow(tau.denominator,v)


class Context:
    def __init__(self,max_bytes=MAX_CACHE_BYTES):
        if type(max_bytes) is not int or not 0<=max_bytes<=MAX_CACHE_BYTES:
            raise ValueError('bounded transport literal cache')
        self.max_bytes,self.bytes_estimate=max_bytes,0
        self.mu,self.kernels,self.logs,self.nodes={},{},{},{}
    def get(self,table,key,meter):
        if key in table:
            meter.primitives['cache_hits']+=1;meter.charge();return table[key]
        return None
    def store(self,table,key,value,size,meter):
        meter.reserve(self.bytes_estimate+size)
        if size<=self.max_bytes-self.bytes_estimate:
            table[key]=value;self.bytes_estimate+=size
        return value


def prepare_context(meter=None,max_bytes=MAX_CACHE_BYTES):
    meter=_meter(meter);meter.reserve(1024);return Context(max_bytes)


def _mu(X,context,meter):
    cached=context.get(context.mu,X,meter)
    if cached is not None:return cached
    mu=np.ones(X+1,dtype=np.int8);mu[0]=0
    primes=np.ones(X+1,dtype=np.bool_);primes[:2]=False
    for p in range(2,X+1):
        if primes[p]:
            mu[p::p]*=-1
            count=X//p
            meter.primitives['mu_sieve_entries']+=count;meter.charge(count*4+1)
            if p*p<=X:
                primes[p*p::p]=False;mu[p*p::p*p]=0
                count=X//(p*p)
                meter.primitives['mu_sieve_entries']+=count;meter.charge(count*4)
        meter.charge()
    mu.flags.writeable=False
    return context.store(context.mu,X,mu,1024+X+1,meter)


def _kernel(N,primes,p,q,context,meter):
    key=(N,primes,p,q)
    cached=context.get(context.kernels,key,meter)
    if cached is not None:return cached
    X=4*N//p
    meter.reserve(context.bytes_estimate+4096+512*(X+1)+BATCH_SIZE*MAX_DEGREE*16)
    mu=_mu(X,context,meter)
    d=np.arange(1,X+1,dtype=np.int64)
    mask=mu[1:]!=0
    for prime in primes:
        mask[prime-1::prime]=False
        meter.primitives['coprime_mask_entries']+=X//prime;meter.charge(X//prime+1)
    a=(4*N)//(p*d)-3*((2*N)//(p*d))+2*(N//(p*d))
    b=(4*N)//(q*d)-3*((2*N)//(q*d))+2*(N//(q*d))
    if np.any(np.abs(a)>1) or np.any(np.abs(b)>1):raise ArithmeticError('exact quotient W range')
    keep=mask&((a!=0)|(b!=0));d,a,b=d[keep],a[keep],b[keep]
    signs=np.where(a!=0,a,-b).astype(np.int8)
    profiles=np.where(b==0,0,np.where(a==0,1,np.where(a==b,2,3))).astype(np.int8)
    mobius=mu[d].copy()
    for array in (d,a,b,signs,profiles,mobius):array.flags.writeable=False
    meter.primitives['integer_weight_entries']+=2*X;meter.charge(32*(X+1))
    result=(d,a,b,signs,profiles,mobius)
    return context.store(context.kernels,key,result,4096+sum(arr.nbytes for arr in result),meter)


def _log_arrays(N,primes,p,q,d,context,meter):
    key=(N,primes,p,q)
    cached=context.get(context.logs,key,meter)
    if cached is not None:return cached
    values=(np.log((p*d).astype(np.float64)),np.log((q*d).astype(np.float64)))
    for array in values:array.flags.writeable=False
    meter.primitives['log_atoms']+=2*len(d)+len(primes)+1
    meter.charge(16*(2*len(d)+len(primes)+1))
    result=(*values,np.log(np.asarray(primes,dtype=np.float64)),math.log1p((q-p)/p))
    result[2].flags.writeable=False
    return context.store(context.logs,key,result,1024+sum(a.nbytes for a in result[:3]),meter)


def _quadrature(degree,context,meter):
    cached=context.get(context.nodes,degree,meter)
    if cached is not None:return cached
    nodes,weights=np.polynomial.legendre.leggauss(degree)
    if not np.all(np.isfinite(nodes)) or not np.all(weights>0):raise ArithmeticError('finite positive quadrature nodes')
    nodes.flags.writeable=False;weights.flags.writeable=False
    meter.primitives['quadrature_nodes']+=degree;meter.charge(degree**3+degree*16)
    return context.store(context.nodes,degree,(nodes,weights),1024+nodes.nbytes+weights.nbytes,meter)


def _delta(before,after):
    return {'operations':after['operations']-before['operations'],
            'peak_bytes_estimate':after['peak_bytes_estimate'],
            'total_primitive_counts':{k:after['total_primitive_counts'][k]-before['total_primitive_counts'][k]
                                      for k in after['total_primitive_counts']}}


def classify_pair(a,b):
    """Exact signed coefficient rule, independent of numerical magnitudes."""
    if type(a) is not int or type(b) is not int or a not in (-1,0,1) or b not in (-1,0,1) or (a,b)==(0,0):
        raise ValueError('nonzero quotient weight pair in {-1,0,1}^2')
    if b==0:return 'P',a
    if a==0:return 'Q',-b
    return ('D' if a==b else 'S'),a


def evaluate(request,degree=64,meter=None,context=None):
    """Exact token decomposition with uncertified FLOAT magnitudes."""
    meter=_meter(meter);before=meter.counts()
    N,alpha,gamma,tau,primes,p,q=_request(request,meter)
    if type(degree) is not int or not 8<=degree<=MAX_DEGREE:raise ValueError('quadrature degree8..256')
    context=prepare_context(meter) if context is None else context
    if type(context) is not Context:raise ValueError('producer-owned transport cache')
    empty=_band_empty(N,gamma,tau,meter)
    X=4*N//p
    meter.reserve(context.bytes_estimate+4096+512*(X+1)+16*BATCH_SIZE*degree)
    d,a,b,sigma,profiles,mu=_kernel(N,primes,p,q,context,meter)
    magnitudes=np.zeros(len(d),dtype=np.float64)
    epsilon_float=tau_float=None
    if not empty and len(d):
        tau_float=float(tau)
        try:epsilon_float=math.exp(-float(gamma)*math.log(N))
        except (OverflowError,ValueError):raise ArithmeticError('screening endpoint float range') from None
        if not 0<epsilon_float<tau_float<1:
            raise ArithmeticError('nonempty exact band unresolved in FLOAT endpoints')
        complement=float(1-alpha)
        if not math.isfinite(complement) or complement<=0:
            raise ArithmeticError('positive gamma normalizer unresolved in FLOAT')
        normalizer=math.exp(-math.lgamma(complement))
        if not math.isfinite(normalizer) or normalizer<=0:
            raise ArithmeticError('finite positive FLOAT normalizer')
        logs_p,logs_q,logs_M,log_ratio=_log_arrays(N,primes,p,q,d,context,meter)
        nodes,weights=_quadrature(degree,context,meter)
        t=(tau_float+epsilon_float)/2+(tau_float-epsilon_float)*nodes/2
        with np.errstate(over='raise',divide='raise',invalid='raise',under='ignore'):
            G=np.prod(-np.expm1(-t[:,None]*logs_M[None,:]),axis=1)
            common=weights*(tau_float-epsilon_float)/2*G*np.power(t,-1-float(alpha))*normalizer
            difference_factor=-np.expm1(-t*log_ratio)
            for start in range(0,len(d),BATCH_SIZE):
                stop=min(len(d),start+BATCH_SIZE)
                ep=np.exp(-logs_p[start:stop,None]*t[None,:])
                eq=np.exp(-logs_q[start:stop,None]*t[None,:])
                P=ep@common;Qvalue=eq@common;D=ep@(common*difference_factor)
                Svalue=P+Qvalue
                selected=np.choose(profiles[start:stop],(P,Qvalue,D,Svalue))
                if not np.all(np.isfinite(selected)) or not np.all(selected>0):
                    raise ArithmeticError('finite strictly positive numerical profile required')
                magnitudes[start:stop]=selected
                entries=(stop-start)*degree
                meter.primitives['quadrature_matrix_entries']+=entries*2;meter.charge(entries*32)
    tokens=[{'d':int(divisor),'profile':PROFILES[int(profile)],'sign':int(mobius*kernel_sign),
             'kernel_sign':int(kernel_sign),'mu':int(mobius),'magnitude':float(magnitude)}
            for divisor,profile,kernel_sign,mobius,magnitude in zip(d,profiles,sigma,mu,magnitudes)]
    if any(classify_pair(int(av),int(bv))!=(token['profile'],token['kernel_sign'])
           for av,bv,token in zip(a,b,tokens)):
        raise ArithmeticError('exact token profile decomposition')
    signed=math.fsum(token['sign']*token['magnitude'] for token in tokens)
    absolute=math.fsum(token['magnitude'] for token in tokens)
    if not math.isfinite(signed) or not math.isfinite(absolute):raise ArithmeticError('finite FLOAT totals')
    meter.primitives['tokens']+=len(tokens);meter.charge(32*len(tokens)+1)
    return {'schema':'mobius-transport-numerical-source-v1',
        'request':dict(request,primes=list(primes)),'tokens':tokens,'signed_sum':signed,'absolute_sum':absolute,
        'numeric':{'method':'NumPy vectorized Gauss-Legendre; stable positive difference integrand',
            'degree':degree,'dtype':'float64','empty_band_exact':empty,
            'epsilon_float':epsilon_float,'tau_float':tau_float,
            'normalization':'1/Gamma(1-alpha)',
            'source_horizon':X,'unit_d_considered':True,'unit_token_present':bool(len(d) and d[0]==1),
            'zero_weight_pair_removed':True,'q_range_exit_preserved':True,
            'source_mu':'ordinary integer prime/multiple and square-multiple sieve',
            'token_order':'ascending actual integer d','numerical_screening_only':True,
            'quadrature_error_certified':False,'rigorous_positive_magnitudes_admitted':False,
            'rigorous_source_interval_admitted':False,'uniform_bound_proved':False,
            'rh_proved':False,'artifact_hashes_used':False},
        'counts':_delta(before,meter.counts())}

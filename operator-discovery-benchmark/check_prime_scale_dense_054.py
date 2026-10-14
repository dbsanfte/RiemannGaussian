"""Independent NEW-endpoint dense witness admission.

Source prefixes are rebuilt by frozen053 independent primitives, never admitted
from saved flags or a caller-constructed VerifiedSource. Rebuilding can overlap
atoms computed in the older study; this is a new witness audit, not replay of
its training/evaluation sample bank. No054 producer imports or stored data I/O.
"""
from fractions import Fraction as Q
from weakref import WeakKeyDictionary
import numpy as np
from check_prime_scale_filter_053 import Meter,_parse,_expect
import check_prime_scale_values_053 as VALUES

MAX_N=VALUES.MAX_N
BITS=32
MAX_CACHED_INDICES=4_000_000
MAX_CONTEXT_ALPHAS=32
MAX_LIVE_CONTEXTS=64


class _Context:
    __slots__=('__weakref__',)


_CONTEXTS=WeakKeyDictionary()


def prepare_context(meter=None):
    """Return an opaque live authority for this module's new-audit prefixes."""
    if meter is not None:meter.charge()
    if len(_CONTEXTS)>=MAX_LIVE_CONTEXTS:raise OverflowError('live source context capacity')
    context=_Context();_CONTEXTS[context]={};return context


def _sources(context):
    if type(context) is not _Context or context not in _CONTEXTS:
        raise ValueError('checker-created live source context required')
    return _CONTEXTS[context]


def _source(alpha,n,meter,context):
    cache=_sources(context);previous=cache.get(alpha)
    if previous is not None and n<=previous.max_n:
        meter.charge(1)
        return previous,{'new_atoms':0,'reused_verified_through':previous.max_n,'source_prefix_rebuilt':False}
    if type(n) is not int or not 2<=n<=MAX_N:raise ValueError('bounded witness source coverage')
    if alpha not in cache and len(cache)>=MAX_CONTEXT_ALPHAS:raise OverflowError('source exponent cache capacity')
    old=0 if previous is None else previous.max_n
    prospective=n+1
    for live_context,live_cache in _CONTEXTS.items():
        prospective+=sum(s.max_n+1 for key,s in live_cache.items() if live_context is not context or key!=alpha)
        meter.charge(len(live_cache)+1)
    if prospective>MAX_CACHED_INDICES:raise OverflowError('prospective cached source memory capacity')
    prefix_bound=(n-1)*n.bit_length()*(1<<BITS)
    if prefix_bound>VALUES.INT64_MAX:raise OverflowError('witness source int64 capacity')
    meter.charge(64*(n+1))
    mu=VALUES._mobius(n,meter)
    weights=np.zeros(n+1,dtype=np.int64)
    if previous is not None:
        if not np.array_equal(mu[:old+1],previous.mu):raise ArithmeticError('independent extended ordinary mu mismatch')
        weights[:old+1]=previous.weights
    a=Q(alpha);new_atoms=0;refinement={str(p):0 for p in (192,256,384)}
    for d in range(max(2,old+1),n+1):
        if mu[d]:
            value,precision=VALUES._atom(d,a,BITS,meter)
            if value>n.bit_length()*(1<<BITS):raise ArithmeticError('proved logarithmic atom capacity')
            weights[d]=-int(mu[d])*value;new_atoms+=1;refinement[str(precision)]+=1
    # These arrays stay module-private; the public context holds no arrays.
    source=VALUES.VerifiedSource(alpha,n,BITS,mu,weights,
        {'authority':'rebuilt inside new054 witness audit','verified':True})
    cache[alpha]=source
    return source,{'new_atoms':new_atoms,'reused_verified_through':old,'source_prefix_rebuilt':True,
        'atom_refinement_counts':refinement}


def _prefix(source,scale,meter):
    """One fresh complete divisor-floor prefix, retaining rounding signs."""
    if type(scale) is not int or not 2<=scale<=source.max_n:raise ValueError('prefix within rebuilt source')
    # floor atom <=ceil(log2(scale)); sum floor(scale/d)<=scale*ceil(log2(scale)).
    capacity=scale*scale.bit_length()**2*(1<<source.bits)
    if capacity>VALUES.INT64_MAX:raise OverflowError('direct prefix accumulation capacity')
    divisors=np.arange(2,scale+1,dtype=np.int64)
    multiplicities=scale//divisors
    center=int(np.sum(source.weights[2:scale+1]*multiplicities,dtype=np.int64))
    down=int(np.sum(multiplicities[source.mu[2:scale+1]==1],dtype=np.int64))
    up=int(np.sum(multiplicities[source.mu[2:scale+1]==-1],dtype=np.int64))
    meter.charge(96*scale)
    return center,down,up


def _reconstruct(request,N,meter,context):
    alpha,q,cs,C,eta,_=_parse(request,meter)
    if type(N) is not int or not 2<=N<=MAX_N:raise ValueError('ordinary bounded integer witness')
    if eta!=0:raise ValueError('this dense exact-square certificate requires log_power0')
    largest=q**(len(cs)-1)*N
    source,rebuild=_source(request['alpha'],largest,meter,context)
    rows=[];center=lower=upper=0
    for j,c in enumerate(cs):
        scale=q**j*N
        acenter,down,up=_prefix(source,scale,meter)
        termlo=c*(acenter-down) if c>=0 else c*(acenter+up)
        termhi=c*(acenter+up) if c>=0 else c*(acenter-down)
        rows.append({'j':j,'scale':scale,'coefficient':c,'Acenter':acenter,
            'Adown':down,'Aup':up,'lower_numerator':acenter-down,'upper_numerator':acenter+up})
        center+=c*acenter;lower+=termlo;upper+=termhi
    if not lower<=center<=upper:raise ArithmeticError('complete signed interval ordering')
    absolute=0 if lower<=0<=upper else min(abs(lower),abs(upper))
    left=absolute**2*alpha.denominator**2*C.denominator**2
    right=N*alpha.numerator**2*(1<<(2*BITS))*C.numerator**2
    meter.charge(1+left.bit_length()+right.bit_length())
    return {'N':N,'used':largest,'rows':rows,'center':center,'lower':lower,'upper':upper,
        'absolute':absolute,'left':left,'right':right,'source':source,'rebuild':rebuild}


def verify_witness(request,witness,meter=None,context=None):
    """Independently verify ONE new dense integer counterexample.

    Saved arrays/flags are not accepted. Only the prefix actually used by this
    witness is rebuilt, optionally reusing this new audit's private live cache.
    """
    meter=Meter(cap=200_000_000_000,seconds=7200) if meter is None else meter
    if type(witness) is not dict or set(witness)!={'schema','id','request','N','source_max_n',
        'source_support_used','dyadic_bits','denominator','term_rows','Tcenter','Tlower','Tupper',
        'lower_abs_numerator','comparison','source_chain_replayed_here','all_scale',
        'float_or_root_comparison_used'}:raise ValueError('exact dense witness schema')
    alpha,q,cs,C,eta,_=_parse(request,meter)
    if C!=2 or eta!=0:raise ValueError('registered dense C2 log_power0 witness scope')
    _expect(witness['request'],request)
    if type(witness['id']) is not str or not 1<=len(witness['id'])<=250:raise ValueError('bounded witness identifier')
    N=witness['N'];availability=witness['source_max_n']
    if type(N) is not int or not 2<=N<=MAX_N:raise ValueError('ordinary bounded integer witness')
    used=q**(len(cs)-1)*N
    if type(availability) is not int or not used<=availability<=MAX_N:raise ValueError('bounded available source includes witness')
    _expect(witness['source_support_used'],used)
    _expect(witness['dyadic_bits'],BITS);_expect(witness['denominator'],1<<BITS)
    _expect(witness['schema'],'prime-scale-dense-counterexample-v1')
    for flag in ('source_chain_replayed_here','all_scale','float_or_root_comparison_used'):
        _expect(witness[flag],False)
    if context is None:context=prepare_context(meter)
    replay=_reconstruct(request,N,meter,context)
    expected={'schema':'prime-scale-dense-counterexample-v1','id':witness['id'],'request':request,
        'N':N,'source_max_n':availability,'source_support_used':used,'dyadic_bits':BITS,
        'denominator':1<<BITS,'term_rows':replay['rows'],'Tcenter':replay['center'],
        'Tlower':replay['lower'],'Tupper':replay['upper'],
        'lower_abs_numerator':replay['absolute'],
        'comparison':{'left':replay['left'],'right':replay['right'],'relation':'>',
            'formula':'lower_abs^2*alpha_den^2 > 4*N*alpha_num^2*2^(2*bits)'},
        'source_chain_replayed_here':False,'all_scale':False,'float_or_root_comparison_used':False}
    _expect(witness,expected)
    if replay['left']<=replay['right']:raise ValueError('strict registered inequality failure not proved')
    lo=Q(replay['lower']*alpha.denominator,(1<<BITS)*alpha.numerator)
    hi=Q(replay['upper']*alpha.denominator,(1<<BITS)*alpha.numerator)
    meter.charge(len(repr(expected))+300)
    return {'verified':True,'id':witness['id'],'request':request,'N':N,
        'status':'FINITE_REFUTATION','registered_uniform_bound_refuted':True,
        'checked_source_max_n':used,'producer_source_availability':availability,
        'unused_source_indices_verified':False,'dyadic_bits':BITS,
        'normalized_source_interval':{'lower':str(lo),'upper':str(hi)},
        'comparison':expected['comparison'],'source_reconstruction':replay['rebuild'],
        'source_method':'new-prefix ordinary divisor-recurrence mu and independent192/256/384-bit log atoms',
        'old_atoms_may_overlap_new_witness_reconstruction':True,
        'finite_only':True,'all_other_constants_or_rates_refuted':False,
        'RH_proved':False,'RH_refuted':False,'producer_imported':False}

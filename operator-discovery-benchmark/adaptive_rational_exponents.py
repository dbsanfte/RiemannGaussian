"""Resumable exact exponent enumeration, without a denominator ceiling.

Ordinary candidates have increasing |numerator|+denominator, then increasing
signed numerator. Requested exponents are a metered priority queue. Finite
search coverage and unproved analytic recovery are always explicit.
"""
from fractions import Fraction
import math
import re

SCHEMA='adaptive-rational-exponents-cursor-v1'
_FIELDS={'schema','lower','upper','height','offset','requests','injected',
         'emitted_total','scans_total','operations_total','exhausted'}
_SYNTAX=re.compile(r'[+-]?[0-9]+(?:/[+-]?[0-9]+)?\Z')


class _Stop(Exception):
    def __init__(self,required):self.required=required


class _Budget:
    def __init__(self,cap):self.cap=cap;self.operations=0
    def charge(self,n):
        if n>self.cap-self.operations:raise _Stop(n)
        self.operations+=n


def _decimal(n):
    """Decimal conversion without Python's unrelated decimal digit ceiling."""
    sign='-' if n<0 else '';n=abs(n)
    chunks=[]
    while n>=10**9:
        n,r=divmod(n,10**9);chunks.append(r)
    return sign+str(n)+''.join('%09d'%r for r in reversed(chunks))


def _text(q):
    return _decimal(q.numerator)+('/'+_decimal(q.denominator) if q.denominator!=1 else '')


def _integer(text):
    sign=-1 if text.startswith('-') else 1
    if text[:1] in ('-','+'):text=text[1:]
    n=0
    for start in range(0,len(text),9):
        piece=text[start:start+9];n=n*10**len(piece)+int(piece)
    return sign*n


def _token(value):
    # Public interval/request syntax is exact text. No float is rationalized.
    if type(value) is not str:
        raise ValueError('exact rational strings required; floats are rejected')
    return value


def _parse(text,budget):
    _token(text)
    # Reserve before regex, integer allocation, reduction and decimal export.
    budget.charge(1+4*len(text)**2)
    if not _SYNTAX.fullmatch(text):raise ValueError('integer or integer/integer rational text')
    parts=text.split('/')
    numerator=_integer(parts[0]);denominator=_integer(parts[1]) if len(parts)==2 else 1
    if denominator==0:raise ValueError('nonzero rational denominator')
    return Fraction(numerator,denominator)


def _position(q,height,offset):
    h=abs(q.numerator)+q.denominator
    return h<height or (h==height and q.numerator+h-1<offset)


def _state(cursor,lower,upper,requested):
    if type(requested) not in (list,tuple) or any(type(x) is not str for x in requested):
        raise ValueError('finite requested list of exact rational strings')
    if cursor is None:
        return dict(schema=SCHEMA,lower=_token('0' if lower is None else lower),
            upper=_token('1' if upper is None else upper),height=1,offset=0,
            requests=list(requested),injected=[],emitted_total=0,scans_total=0,
            operations_total=0,exhausted=False)
    if type(cursor) is not dict or set(cursor)!=_FIELDS or cursor['schema']!=SCHEMA:
        raise ValueError('exact continuation cursor fields')
    for key in ('height','offset','emitted_total','scans_total','operations_total'):
        if type(cursor[key]) is not int or cursor[key]<0:raise ValueError('strict cursor counters')
    h,offset=cursor['height'],cursor['offset']
    if h<1 or offset>=2*h-1 or cursor['scans_total']!=(h-1)**2+offset:
        raise ValueError('consistent height-shell continuation position')
    if type(cursor['exhausted']) is not bool:raise ValueError('strict cursor exhaustion flag')
    for key in ('requests','injected'):
        if type(cursor[key]) is not list or any(type(x) is not str for x in cursor[key]):
            raise ValueError('cursor exact rational queues')
    _token(cursor['lower']);_token(cursor['upper'])
    if lower is not None and lower!=cursor['lower']:
        raise ValueError('resume preserves canonical lower interval')
    if upper is not None and upper!=cursor['upper']:
        raise ValueError('resume preserves canonical upper interval')
    return dict(cursor,requests=cursor['requests']+list(requested),injected=cursor['injected'][:])


def next_batch(cursor=None,lower=None,upper=None,max_candidates=128,
               work_budget=20000,requested=()):
    """Return candidates, exact continuation, declared coverage and proxy work.

    Initial interval defaults to[0,1]; omitted bounds preserve it on resume.
    Inputs are rational TEXT, normalized after a reserved bit/parse charge.
    Zero work returns an unchanged scan position with all requests retained.
    A request too large for a call remains queued: increasing the resource
    budget can admit it. No semantic bit or denominator cutoff is imposed.

    Cursors are transparent resumable state, not authenticated proof objects;
    callers preserve them unchanged. Scan counters make their position auditable.
    """
    if type(max_candidates) is not int or max_candidates<=0:
        raise ValueError('positive integer candidate cap')
    if type(work_budget) is not int or work_budget<0:
        raise ValueError('nonnegative integer work cap')
    state=_state(cursor,lower,upper,requested);budget=_Budget(work_budget)
    candidates=[];admissions=[];rejections=[];request_index=0
    status='candidate_limit';required=None;bounds_validated=False
    try:
        budget.charge(5+len(state['requests'])+len(state['injected']))
        lo=_parse(state['lower'],budget);hi=_parse(state['upper'],budget)
        if lo>hi:raise ValueError('ordered finite closed interval')
        state['lower'],state['upper']=_text(lo),_text(hi);bounds_validated=True
        injected=set()
        for text in state['injected']:
            q=_parse(text,budget)
            if _text(q)!=text or not lo<=q<=hi or text in injected:
                raise ValueError('canonical unique admitted requests within interval')
            injected.add(text)
        if state['exhausted'] and lo!=hi:
            raise ValueError('a nondegenerate rational interval is never exhausted')
        while request_index<len(state['requests']) and len(candidates)<max_candidates:
            raw=state['requests'][request_index];q=_parse(raw,budget);text=_text(q)
            request_index+=1
            if not lo<=q<=hi:
                rejections.append(dict(request=raw,normalized=text,reason='outside_interval'))
            elif text in injected or _position(q,state['height'],state['offset']):
                rejections.append(dict(request=raw,normalized=text,reason='already_admitted'))
            else:
                candidates.append(text);admissions.append(dict(exponent=text,route='explicit_request'))
                injected.add(text);state['injected'].append(text);state['emitted_total']+=1
        if request_index<len(state['requests']):
            status='candidate_limit'
        elif lo==hi:
            text=_text(lo)
            if text not in injected and not state['exhausted'] and len(candidates)<max_candidates:
                candidates.append(text);admissions.append(dict(exponent=text,route='singleton_interval'))
                state['injected'].append(text);state['emitted_total']+=1
            state['exhausted']=text in state['injected'];status='interval_exhausted'
        elif not state['exhausted']:
            bits_bounds=sum(abs(q.numerator).bit_length()+q.denominator.bit_length() for q in (lo,hi))
            while len(candidates)<max_candidates:
                h,offset=state['height'],state['offset'];a=offset-(h-1);b=h-abs(a)
                # Ordinary gcd/comparison is a bit-size primitive proxy, not
                # a claim of a bit-complexity theorem for arbitrary precision.
                budget.charge(2+abs(a).bit_length()+b.bit_length()+bits_bounds)
                state['scans_total']+=1;state['offset']+=1
                if state['offset']==2*h-1:state['height']+=1;state['offset']=0
                if math.gcd(a,b)!=1:continue
                q=Fraction(a,b)
                if not lo<=q<=hi:continue
                text=_text(q)
                if text in injected:
                    injected.remove(text);state['injected'].remove(text)
                    continue
                candidates.append(text);admissions.append(dict(exponent=text,route='height_shell'))
                state['emitted_total']+=1
    except _Stop as stop:
        status='work_budget';required=stop.required
    except ValueError as error:
        error.operations=budget.operations
        raise
    state['requests']=state['requests'][request_index:]
    state['operations_total']+=budget.operations
    return dict(candidates=candidates,cursor=state,operations=budget.operations,
        status=status,admissions=admissions,request_rejections=rejections,
        coverage=dict(interval=[state['lower'],state['upper']],interval_validated=bounds_validated,
            closed_interval=True,ordinary_order='increasing |a|+b, then signed numerator',
            ordinary_complete_through_height=state['height']-1,
            next_height=state['height'],next_offset=state['offset'],
            ordinary_pairs_scanned_total=state['scans_total'],emitted_total=state['emitted_total'],
            all_rationals_in_interval_covered=state['exhausted'],
            pending_requested=len(state['requests']),pending_early_admissions=len(state['injected']),
            no_semantic_denominator_ceiling=True,no_semantic_bit_ceiling=True,
            finite_work_cap=work_budget,finite_candidate_cap=max_candidates,
            next_required_work=required,
            arithmetic_control_proved=False,recovery_bound_paid=False))


def _exponent(value,meter=None):
    if type(value) is Fraction:
        text=_text(value)
    elif type(value) is int:
        text=_decimal(value)
    else:text=_token(value)
    class B:
        def charge(self,n):
            if meter is not None:meter.charge(n)
    return _text(_parse(text,B()))


def coefficient_twist(gamma,state,meter=None):
    """n^-gamma times a COMPLETE signed coefficient state; no bound claim."""
    if type(state) is not int or state<0:raise ValueError('nonnegative integer state')
    return dict(op='coefficient_twist',exponent=_exponent(gamma,meter),state=state)


def signed_power(gamma,state,meter=None):
    """Separate sign-preserving pointwise power, never a Dirichlet power."""
    if type(state) is not int or state<0:raise ValueError('nonnegative integer state')
    return dict(op='signed_power',exponent=_exponent(gamma,meter),state=state)


def signed_power_ast(gamma,input_index,meter=None):
    """Old rational-power syntax for its two available real sequence inputs."""
    if type(input_index) is not int or input_index not in (0,1):
        raise ValueError('old grammar real input0 or1')
    return ['rpow',['input',input_index],_exponent(gamma,meter),'signed']


def production_contract(program):
    if type(program) is not dict or set(program)!={'op','exponent','state'}:
        raise ValueError('exact production fields')
    if program['op']=='coefficient_twist':
        normalized=coefficient_twist(program['exponent'],program['state'])
        domain='integer n>=1; full real signed coefficient state; n^-gamma positive'
    elif program['op']=='signed_power':
        normalized=signed_power(program['exponent'],program['state'])
        domain='real sign-preserving power; gamma<=0 excludes zero; not an ordinary even root'
    else:raise ValueError('known separately typed production')
    if normalized!=program:raise ValueError('canonical production exponent')
    return dict(domain=domain,exact_fraction_exponent=True,uniform_bound_proved=False,
                recovery_needed=True,recovery_paid=False,
                source_lattice_is_not_an_exponent_restriction=True)

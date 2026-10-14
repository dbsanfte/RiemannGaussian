"""Independent finite rough-prime transport and graded parity terminal checker.

Frozen independent077 interval/rational admission reused, never a producer.
Prime rosters/products are independently reconstructed; no arithmetic mu query.
"""
from fractions import Fraction
from bisect import bisect_left
import check_mobius_residual_fold_077 as F
from check_mobius_prime_storage_073 import AdmissionError, ResourceLimit, _rational, _add, _mul
MAX_PRODUCTS=500000
MAX_TERMS=100000
MEMORY_BUDGET=4*1024**3
class Meter(F.Meter):pass

def _cutoff(value,name):return F._integer(value,name,1,1<<4096)
def _excluded(values,m):
    if type(values) is not list:raise AdmissionError('excluded primes must be sorted list')
    result=F._primes(values,m)
    if list(result)!=sorted(result):raise AdmissionError('excluded primes must be sorted distinct')
    return result

def _sieve(horizon,m):
    F._integer(horizon,'sieve horizon',0,F.MAX_HORIZON)
    # Reserve byte bitmap and worst-case Python prime list before allocation.
    m.reserve(4096+64*(horizon+1));m.charge(horizon+1)
    flags=bytearray(b'\1')*(horizon+1);flags[0]=0
    if horizon>=1:flags[1]=0
    from math import isqrt
    for p in range(2,isqrt(horizon)+1):
        if flags[p]:
            for n in range(p*p,horizon+1,p):m.charge();flags[n]=0
    m.charge(horizon+1)
    return [n for n in range(2,horizon+1) if flags[n]]
def _done(out,m,error=None):
    result=F._finish(out,m,error)
    result.update(uniform_source_bound_proved=False,conditional_real_token_identity=True)
    return result

def verify_transport(intervals,payload):
    m=Meter();out={'status':'INVALID'}
    try:
        rows,cost=F._intervals(intervals,m);H=max((r for l,r,w in rows),default=0)
        keys={'schema','lower_cutoff','upper_cutoff','excluded_primes','children'}
        if type(payload) is not dict or set(payload)!=keys or payload['schema']!='rough-prime-transport-v1':raise AdmissionError('invalid transport schema')
        y1=_cutoff(payload['lower_cutoff'],'lower cutoff');y2=_cutoff(payload['upper_cutoff'],'upper cutoff')
        if y2<y1:raise AdmissionError('inverted rough cutoffs')
        excluded=_excluded(payload['excluded_primes'],m)
        expected_primes=[p for p in _sieve(min(y2,H),m) if p>y1 and p not in excluded]
        children=payload['children']
        if type(children) is not list or len(children)!=len(expected_primes):raise AdmissionError('complete rough-prime roster required')
        # A roster payload may be much larger than its source interval function.
        raw_cost=0
        for child in children:
            if type(child) is not dict or set(child)!={'prime','intervals'}:raise AdmissionError('invalid transport child')
            if type(child['intervals']) is not list or len(child['intervals'])>F.MAX_INTERVALS:raise AdmissionError('invalid child intervals')
            for row in child['intervals']:
                if type(row) is not dict or type(row.get('weight')) is not dict:raise AdmissionError('invalid child interval')
                raw_cost+=F._raw_cost(row['weight'])
        m.reserve(4096+64*(H+1)+1024*len(children)+16*cost+8*raw_cost)
        for p,child in zip(expected_primes,children):
            if type(child['prime']) is not int or child['prime']!=p:raise AdmissionError('rough-prime roster mismatch')
            actual,child_cost=F._intervals(child['intervals'],m)
            m.reserve(4096+64*(H+1)+1024*len(children)+16*(cost+child_cost)+8*raw_cost)
            scaled=[(l//p,r//p,poly) for l,r,poly in rows if l//p<r//p]
            mismatch=F._compare_events(F._function_events(scaled,m),F._function_events(actual,m),m)
            if mismatch:out['first_witness']=dict(mismatch,prime=p);raise AdmissionError('transport scaled coefficient function mismatch')
        out.update(status='VERIFIED_IDENTITY',horizon=H,children_checked=len(children),excluded_primes=list(excluded),identity='T(c,y1)-T(c,y2)=-sum_{y1<p<=y2,p not excluded} T(c(p*),p)',unit_retained=True)
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _done(out,m,error)
    return _done(out,m)

def _product_layers(primes,degree,H,m):
    """Independent increasing-prime enumeration, no repeated factors or mu sieve."""
    counts=[0]*(degree+1);products=[[] for _ in range(degree+1)]
    if H>=1:counts[0]=1;products[0].append(1)
    total=counts[0]
    # Prospective cap includes products, traversal state, and sorted query copies.
    m.reserve(4096+64*(H+1)+96*MAX_PRODUCTS)
    def descend(product,start,depth):
        nonlocal total
        if depth>=degree:return
        for index in range(start,len(primes)):
            p=primes[index];m.charge()
            if p>H//product:break
            value=product*p;total+=1
            if total>MAX_PRODUCTS:raise ResourceLimit('prospective prime-product count exceeds500000')
            products[depth+1].append(value);counts[depth+1]+=1
            descend(value,index+1,depth+1)
    if degree and H>=1:descend(1,0,0)
    return products,counts

def verify_terminal(intervals,payload):
    m=Meter();out={'status':'INVALID'}
    try:
        rows,cost=F._intervals(intervals,m);H=max((r for l,r,w in rows),default=0)
        keys={'schema','cutoff','degree','excluded_primes','layer_polynomials','layer_counts','signed_polynomial'}
        if type(payload) is not dict or set(payload)!=keys or payload['schema']!='rough-factor-terminal-v1':raise AdmissionError('invalid terminal schema')
        y=_cutoff(payload['cutoff'],'cutoff');degree=F._integer(payload['degree'],'degree',0,4);excluded=_excluded(payload['excluded_primes'],m)
        if pow(y,degree+1)<H:raise AdmissionError('inexact terminal factor threshold')
        raw_layers=payload['layer_polynomials'];raw_counts=payload['layer_counts']
        if type(raw_layers) is not list or len(raw_layers)!=degree+1 or type(raw_counts) is not list or len(raw_counts)!=degree+1:raise AdmissionError('terminal layer shape')
        if any(type(c) is not int or c<0 or c>MAX_PRODUCTS for c in raw_counts):raise AdmissionError('invalid layer counts')
        raw_polys=raw_layers+[payload['signed_polynomial']]
        if any(type(poly) is not dict for poly in raw_polys) or sum(len(poly) for poly in raw_polys)>MAX_TERMS:raise AdmissionError('terminal polynomial term gate')
        pcost=sum(F._raw_cost(poly) for poly in raw_polys)
        m.reserve(4096+64*(H+1)+96*MAX_PRODUCTS+32*(cost+pcost))
        actual_layers=[F._poly(poly,m) for poly in raw_layers];actual_signed=F._poly(payload['signed_polynomial'],m)
        primes=[p for p in _sieve(H,m) if p>y and p not in excluded]
        products,counts=_product_layers(primes,degree,H,m)
        if counts!=raw_counts:raise AdmissionError('terminal complete factor-layer counts mismatch')
        layers=[]
        for layer in products:
            layer.sort();poly={}
            # Interval/count lookup preserves all complete token polynomials.
            for l,r,weight in rows:
                count=bisect_left(layer,r+1)-bisect_left(layer,l+1);m.charge(max(1,len(layer).bit_length()))
                if count:
                    for token,a in weight.items():
                        v=_mul(Fraction(count),a,m);poly[token]=_add(poly.get(token,Fraction(0)),v,m)
                        if not poly[token]:del poly[token]
            layers.append(poly)
        signed={}
        for r,poly in enumerate(layers):F._join(signed,poly,1 if r%2==0 else -1,m)
        if layers!=actual_layers:raise AdmissionError('terminal layer polynomial mismatch')
        if signed!=actual_signed:raise AdmissionError('terminal graded parity polynomial mismatch')
        out.update(status='VERIFIED_IDENTITY',horizon=H,degree=degree,cutoff=y,excluded_primes=list(excluded),layer_counts=counts,products_checked=sum(counts),signed_polynomial={t:str(v) for t,v in signed.items()},identity='T(c,y)=sum_r (-1)^r layer_polynomial[r]',unit_count=counts[0])
    except (ValueError,TypeError,KeyError,OverflowError) as error:return _done(out,m,error)
    return _done(out,m)

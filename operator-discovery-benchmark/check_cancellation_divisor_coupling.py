"""Independent complete weighted divisor coupling audit, no producer imports."""
from fractions import Fraction as F
import hashlib
import json
import re
import check_grouped_arithmetic as G
P=G.P

def digest(v):return hashlib.sha256(json.dumps(v,sort_keys=True,separators=(',',':'),allow_nan=False).encode()).hexdigest()
def check_coupling(horizon,weights,output,*,target='mu',max_horizon=128,max_operations=20000000,max_terms=10000,max_coefficient_bits=4096):
    for v in [horizon,max_horizon,max_operations,max_terms,max_coefficient_bits]:
        if type(v)is not int or v<1:raise ValueError('strict positive bounds')
    H=horizon
    if target!='mu':raise ValueError('mu inverse-of-ones only')
    if H>max_horizon or H*H>max_operations:raise OverflowError('complete independent source preflight')
    if type(weights)is not list or len(weights)!=H:raise ValueError('complete weights')
    q=[]
    for v in weights:
        if type(v)is not str or len(v)>2*max_coefficient_bits+3 or re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?',v)is None:raise ValueError('canonical rational literal')
        x=F(v)
        if str(x)!=v:raise ValueError('canonical rational')
        if max(abs(x.numerator).bit_length(),x.denominator.bit_length())>max_coefficient_bits:raise OverflowError('input bits')
        q.append(x)
    used=0
    def charge(n):
        nonlocal used
        used+=n
        if used>max_operations:raise OverflowError('independent coupling work')
    def bounded(p):
        if len(p)>max_terms:raise OverflowError('independent terms')
        if any(max(abs(x.numerator).bit_length(),x.denominator.bit_length())>max_coefficient_bits for x in p.values()):raise OverflowError('independent coefficient bits')
        return p
    def add(a,b,s=F(1)):
        charge(len(a)+len(b));return bounded(P.add(a,b,s))
    def mul(a,b):
        charge(len(a)*len(b));return bounded(P.multiply(a,b))
    B={};pairs=[];blocks=[]
    # Enumerate the FULL Cartesian source horizon, testing divisor membership
    # independently; retain all weights including zeros and negative values.
    for a in range(1,H+1):
        ds=[]
        for d in range(1,H+1):
            charge(1)
            if a%d==0:
                ds.append(d);pairs.append([a,d]);B=add(B,{tuple(sorted((a,d))):q[a-1]}if q[a-1]else{})
        blocks.append(dict(a=a,weight=str(q[a-1]),divisors=ds))
    c=q[0];factor=add(B,{():c}if c else{});normal=[];closed=[]
    for a in range(1,H+1):
        spec=dict(kind='unit')if a==1 else dict(kind='inverse_row',n=a)
        mult={():c,(1,):c}if a==1 and c else{}if a==1 else{(a,):q[a-1]}if q[a-1]else{}
        normal.append(dict(spec=spec,multiplier=P.canonical(mult)));closed.append(dict(spec=spec,multiplier=P.canonical(mul(mult,factor))))
    square=mul(B,B);normal_lhs=add(B,{():-c}if c else{});scalar={():-c*c}if c else{};square_lhs=add(square,scalar)
    def cert(lhs,rels):return dict(target='mu',horizon=H,lhs=P.canonical(lhs),squares=[],relations=rels)
    expected=dict(target='mu',horizon=H,weights=weights,weights_sha256=digest(weights),B=P.canonical(B),c=str(c),square_polynomial=P.canonical(square),scalar_minus_c_squared=P.canonical(scalar),normalization_certificate=cert(normal_lhs,normal),square_closure_certificate=cert(square_lhs,closed),source=dict(pairs=pairs,pairs_sha256=digest(pairs),pair_count=len(pairs),blocks=blocks,source_domain='all 1<=a<=H and d|a; zero weights retained',complete=True),formal_identities_verified=True,arithmetic_values_substituted=False,square_is_bound_certificate=False,scope='supplied weighted Mobius inverse-row identity; cross-divisor square terms complete; no critical estimate',global_bound_proved=False,RH_proved=False)
    if type(output)is not dict or set(output)!=set(expected)|{'cost'}:raise ValueError('coupling exact output fields')
    for k,v in expected.items():
        if output[k]!=v or digest(output[k])!=digest(v):raise ValueError('complete weighted coupling '+k)
    cost=output['cost']
    if type(cost)is not dict or set(cost)!={'operations','max_operations','max_terms','max_coefficient_bits'}or any(type(v)is not int for v in cost.values())or not 0<=cost['operations']<=max_operations:raise ValueError('producer resource receipt')
    if (cost['max_operations'],cost['max_terms'],cost['max_coefficient_bits'])!=(max_operations,max_terms,max_coefficient_bits):raise ValueError('producer budget binding')
    for ccert in [expected['normalization_certificate'],expected['square_closure_certificate']]:
        # Existing independent relation math checks both complete formal identities.
        G.verify_certificate(ccert)
    return dict(verified=True,complete_divisor_source=True,complete_cross_divisor_products=True,unit_endpoint_retained=True,finite_identities_only=True,independent_operations_proxy=used,producer_operation_count_independently_verified=False,global_bound_proved=False,RH_proved=False)

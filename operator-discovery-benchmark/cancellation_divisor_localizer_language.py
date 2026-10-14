"""Complete signed divisor localizers and inverse-gcd pair relations.

The fixed grammar has both scale regions and all integer kernel powers -1,0,1.
No Mobius sign samples are used. Grouping equal relation specs is exact linear
aggregation of ALL ordered source pairs, with complete coverage hashes.
"""
from fractions import Fraction as F
from math import gcd
import hashlib
import json
import grouped_arithmetic_language as L
import cancellation_factor_search_language as BASE

SPEC=dict(version='signed-divisor-localizers-v1',regions=['parent','child'],powers=[-1,0,1],
          square_forms=['plain','squarefree_plain','modulated','plus','minus'],
          relation_forms=['norm_closure','gcd_inverse'],divisor_domain='all 1<=d<=t',
          pair_domain='all ordered 1<=a,b<=t',source_scale='N=4X-1',
          squarefree_weights='factor-certified 0/1; no Mobius signs')

def digest(v):return hashlib.sha256(json.dumps(v,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def additions():
    out=dict(square=[],relation=[])
    for region in SPEC['regions']:
        for power in SPEC['powers']:
            common=dict(version=SPEC['version'],region=region,power=power,
                        divisor_domain=SPEC['divisor_domain'],pair_domain=SPEC['pair_domain'])
            for form in SPEC['square_forms']:
                d=dict(common,family='divisor_localizer_square',form=form)
                out['square'].append(dict(d,id=digest(d)))
            for form in SPEC['relation_forms']:
                d=dict(common,family='divisor_localizer_relation',form=form)
                out['relation'].append(dict(d,id=digest(d)))
    return out

def descriptors():
    old=BASE.descriptors();extra=additions()
    return {k:old[k]+extra[k] for k in old}


def build_additions(X,*,max_horizon=80,max_operations=200000000,max_terms=30000,max_coefficient_bits=4096):
    for v in (X,max_horizon,max_operations,max_terms,max_coefficient_bits):
        if type(v)is not int or v<1:raise ValueError('positive strict limits')
    H=4*X-1
    if H>max_horizon or 12*H**3>max_operations:raise OverflowError('complete divisor preflight')
    used=0
    def charge(n=1):
        nonlocal used
        used+=n
        if used>max_operations:raise OverflowError('complete divisor construction work')
    def addterm(poly,m,q):
        charge();value=poly.get(m,F(0))+q
        if max(abs(value.numerator).bit_length(),value.denominator.bit_length())>max_coefficient_bits:raise OverflowError('coefficient bits')
        if value:poly[m]=value
        else:poly.pop(m,None)
        if len(poly)>max_terms:raise OverflowError('polynomial terms')
    def serial(poly):
        charge(len(poly));return L.dump_poly(poly)
    factors={d:L.factor_witness(d,max_n=max_horizon,max_operations=max_operations)for d in range(1,H+1)}
    u={d:int(all(e==1 for p,e in factors[d]))for d in factors}
    square_groups=[];relation_groups=[];archive=[]
    for region in SPEC['regions']:
        ts=list(range(X,2*X)if region=='parent'else range(2*X,4*X))
        pairs=[[t,a,b]for t in ts for a in range(1,t+1)for b in range(1,t+1)]
        divisor_members=[[t,d,a]for t in ts for d in range(1,t+1)for a in range(d,t+1,d)]
        pair_counts={g:0 for g in range(1,H+1)}
        for t,a,b in pairs:pair_counts[gcd(a,b)]+=1
        for power in SPEC['powers']:
            sq={k:[]for k in SPEC['square_forms']};norms={};inverse={};divisor_cells=0
            for t in ts:
                weights={a:F(a,t)**power for a in range(1,t+1)}
                for d in range(1,t+1):
                    divisor_cells+=1;p={(a,):weights[a]for a in range(d,t+1,d)}
                    mod={tuple(sorted((d,a))):q for (a,),q in p.items()}
                    polynomials=dict(plain=p,squarefree_plain=p,modulated=mod,
                                     plus=L.add(p,mod),minus=L.add(p,L.scale(mod,-1)))
                    for form in SPEC['square_forms']:
                        sq[form].append(dict(weight=str(u[d]if form=='squarefree_plain'else 1),poly=serial(polynomials[form])))
                    charge(len(p)**2)
                    p2=L.mul(p,p,max_terms=max_terms,max_operations=max_operations)
                    dest=norms.setdefault(d,{})
                    for m,q in p2.items():addterm(dest,m,q)
                for a in range(1,t+1):
                    for b in range(1,t+1):
                        g=gcd(a,b);dest=inverse.setdefault(g,{})
                        addterm(dest,tuple(sorted((a,b))),weights[a]*weights[b])
            square_groups.extend(sq[k]for k in SPEC['square_forms'])
            norm_group=[dict(spec=dict(kind='norm',n=d,factors=factors[d]),multiplier=serial(p))for d,p in sorted(norms.items())]
            inverse_group=[dict(spec=dict(kind='unit')if g==1 else dict(kind='inverse_row',n=g),multiplier=serial(p))for g,p in sorted(inverse.items())]
            relation_groups.extend([norm_group,inverse_group])
            archive.append(dict(region=region,power=power,scales=ts,ordered_pair_count=len(pairs),
                ordered_pairs_sha256=digest(pairs),gcd_pair_counts={str(g):c for g,c in pair_counts.items()if c},
                divisor_cells=divisor_cells,divisor_members_count=len(divisor_members),
                divisor_members_sha256=digest(divisor_members),
                square_groups_sha256=digest([sq[k]for k in SPEC['square_forms']]),
                norm_group_sha256=digest(norm_group),gcd_inverse_group_sha256=digest(inverse_group),
                aggregation='sum complete multipliers with equal primitive relation; no source pair dropped'))
    return dict(square_groups=square_groups,relation_groups=relation_groups,archive=archive,
                spec=SPEC,construction_operations=used,arithmetic_sign_values_substituted=False,
                global_bound_proved=False,RH_proved=False)


def build_instance(target,X,q,C,claim='critical',**limits):
    if target!='mu':raise ValueError('Mobius inverse-of-ones language only')
    extra=build_additions(X,**limits)
    out=BASE.build_instance(target,X,q,C,claim)
    out['instance']['square_groups'].extend(extra['square_groups'])
    out['instance']['relation_groups'].extend(extra['relation_groups']);d=descriptors()
    out.update(square_ids=[x['id']for x in d['square']],relation_ids=[x['id']for x in d['relation']],
        dictionary_sha256=digest(d),divisor_archive=extra['archive'],divisor_spec=SPEC,
        divisor_construction_operations=extra['construction_operations'])
    return out

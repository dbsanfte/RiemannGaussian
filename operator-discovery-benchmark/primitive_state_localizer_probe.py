"""Exact, complete-column arithmetic-closure diagnostic of an admitted dual.

Signed relation coefficients require zero pairing. Unsupported moments remain
unknown after coefficient cancellation; no arithmetic responses are substituted.
"""
from fractions import Fraction as F
import hashlib
import json
import time
import grouped_arithmetic_language as L

FLAGS=dict(global_bound_proved=False,RH_proved=False,larger_cone_feasibility_proved=False)
SPEC=dict(version='primitive-state-functional-probe-v1',
          selection='every declared relation-state column, in descriptor order',
          signed_relation_rule='exact zero pairing required',
          missing_policy='unknown after exact polynomial cancellation',
          no_new_floating_search=True,no_actual_signed_response_inputs=True)


def digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def encode(column):
    return [dict(instance=k,m=list(m),c=str(q)) for (k,m),q in sorted(column.items())]


def compile_columns(instances,*,max_operations=200000000,max_terms=100000,
                    max_coefficient_bits=4096,max_horizon=80,deadline=None):
    if any(type(v)is not int or v<1 for v in [max_operations,max_terms,max_coefficient_bits,max_horizon]):
        raise ValueError('strict positive complete diagnostic limits')
    if type(instances)is not list or not instances:raise ValueError('complete nonempty source instances')
    count=len(instances[0]['relation_groups']);columns=[{} for _ in range(count)];used=0;cache={}
    def charge(n):
        nonlocal used
        used+=n
        if used>max_operations:raise OverflowError('complete relation-column work cap')
        if deadline is not None and time.monotonic()>deadline:raise TimeoutError('complete diagnostic deadline')
    def checked(q):
        if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits:
            raise OverflowError('diagnostic rational coefficient bits')
        return q
    for k,inst in enumerate(instances):
        if set(inst)!={'target','horizon','lhs','square_groups','relation_groups'} or inst['target']!='mu' or inst['lhs'] or inst['square_groups']:
            raise ValueError('relation-only Mobius closure diagnostic')
        H=inst['horizon']
        if type(H)is not int or not 1<=H<=max_horizon or len(inst['relation_groups'])!=count:
            raise ValueError('bounded complete shared relation coverage')
        for j,group in enumerate(inst['relation_groups']):
            dest=columns[j]
            for term in group:
                if set(term)!={'spec','multiplier'}:raise ValueError('native arithmetic relation term')
                key=H,digest(term['spec'])
                if key not in cache:
                    cache[key]=L.relation(term['spec'],'mu',H,max_operations=max_operations,max_horizon=max_horizon)
                    charge(H*H+len(cache[key]))
                relation=cache[key];multiplier=L.load_poly(term['multiplier'])
                if any(n>H for m in multiplier for n in m):raise ValueError('source polynomial horizon')
                if any(len(a)+len(b)>12 for a in multiplier for b in relation):raise OverflowError('diagnostic polynomial degree')
                charge(len(multiplier)*len(relation)+len(multiplier))
                for a,v in multiplier.items():
                    checked(v)
                    for b,w in relation.items():
                        m=(k,tuple(sorted(a+b)));q=checked(dest.get(m,F(0))+checked(v*w))
                        if q:dest[m]=q
                        else:dest.pop(m,None)
                if len(dest)>max_terms:raise OverflowError('complete diagnostic column size')
    return columns,dict(construction_operations=used,unique_primitive_relations=len(cache))


def probe(instances,descriptors,dual,**limits):
    domain=[(r['instance'],tuple(r['m'])) for r in dual['monomials']]
    if domain!=sorted(set(domain)) or len(domain)!=len(dual['weights']):raise ValueError('unique admitted moment domain')
    y=dict(zip(domain,map(F,dual['weights'])))
    columns,cost=compile_columns(instances,**limits)
    if len(columns)!=len(descriptors) or len({d['id'] for d in descriptors})!=len(descriptors):
        raise ValueError('every unique descriptor in source order')
    missing=sorted({m for p in columns for m in p if m not in y});lookup={m:i for i,m in enumerate(missing)}
    rows=[]
    for i,(column,desc) in enumerate(zip(columns,descriptors)):
        absent=sorted(lookup[m] for m in column if m not in y)
        row=dict(index=i,descriptor_id=desc['id'],complete_column_sha256=digest(encode(column)),
                 terms=len(column),missing_indices=absent)
        if absent:row['status']='unknown_missing_coordinates'
        else:
            value=sum((q*y[m] for m,q in column.items()),F(0))
            row.update(status='violated_relation' if value else 'annihilated_relation',pairing=str(value))
        rows.append(row)
    counts={s:sum(r['status']==s for r in rows) for s in ['violated_relation','annihilated_relation','unknown_missing_coordinates']}
    status=('witness_invalid_for_localizer_cone' if counts['violated_relation'] else
            'unknown_missing_coordinates' if counts['unknown_missing_coordinates'] else 'witness_extends_to_localizer_cone')
    return dict(status=status,rows=rows,counts=counts,
                missing_coordinates=[dict(instance=k,m=list(m)) for k,m in missing],
                source_hashes=list(map(digest,instances)),descriptor_sha256=digest(descriptors),
                input_dual_sha256=digest(dual),cost=cost,no_new_floating_search=True,**FLAGS)
